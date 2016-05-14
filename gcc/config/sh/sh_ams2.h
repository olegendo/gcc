//
// the ams pass obtains a set of alternatives for a given access from the
// delegate (the target).  an alternative is simply a desired/supported
// address expression and its cost.  the costs are allowed to vary for
// each access and alternative independently, so the target can estimate
// the costs based on the context.
// the original address expression that is found in an insn is matched
// against the target provided alternatives to derive the cost for the
// original form.  this will be used as the "original cost".  if no match
// can be found infinite costs will be assigned.
//
// we assume that when initially analysing the access sequences the
// address expressions found in mems are valid addresses for the target.
// this means that the access sequence will continue possible address
// register modification insns or splits.  in order to optimize an
// access sequence the values of the address registers and modifications
// are traced back as much as possible.
// brief example:
//
// the original sequence:
// 1:    load.l  @r123, r50
// 2:    add     #64, r123
// 3:    load.l  @r123, r51
//
// will be analysed as:
// 1:    load.l  @r123, r50
// 3:    load.l  @(r123 + 64), r51
//
// the target provides the alternatives (addr = cost) for loads 1 and 3:
// 1:    @reg = 1, @(reg + 0..60) = 1, @reg+ = 1
// 3:    @reg = 1, @(reg + 0..60) = 1, @reg+ = 1
//
// the target reports cost 3 for the address reg modification in 2.
// the total costs of the original sequence are 1 + 3 + 1 = 5.
//
// the task is to minimize the costs of the total sequence.  since the
// originally used address modes already have minimal costs, the only
// thing that can be optimized away is the address reg modification in 2.
//
// after applying the optimizations we get the following optimized
// sequence:
// 1:    load.l  @r123+, r50
// 2:    --
// 3:    load.l  @(r123 + 60), r51
//
// if the original value of r123 is used after load 3 a better sequence
// could be:
//       mov     r123,r124   // split sequence
//       load.l  @124+, r50
//       load.l  @(r124 + 60), r51
//
// or using indexed addressing:
//       load.l  @r123, r50
//       mov     #64, r60
//       load.l  @(r123 + r60), r51
//
// .. depending on the context.


#ifndef includeguard_gcc_sh_ams2_includeguard
#define includeguard_gcc_sh_ams2_includeguard

#include "tree-pass.h"
#include <limits>
#include <list>
#include <vector>
#include <functional>
#include <map>
#include <set>
#include <string>

#include "filter_iterator.h"
#include "static_vector.h"
#include "ref_counted.h"

class sh_ams2 : public rtl_opt_pass
{
public:
  struct options
  {
    // Use default values.
    options (void);

    // Parse options from comma separated key=value list
    options (const char* str);
    options (const std::string& str);

    // Check if the acces sequence costs are minimal.  If so, don't try to
    // optimize the access sequence.  Default is true.
    bool check_minimal_cost;

    // Check if the original access sequence costs are less or equal to the
    // proposed AMS optimized access sequence costs.  If so, don't try to
    // optimize the access sequence.  Default is true.
    bool check_original_cost;

    // Split the access sequences into multiple smaller ones by placing
    // accesses that share the same base reg into separate sequences.
    // Default is true.
    bool split_sequences;

    // By default AMS will do alternative validation, but it can be disabled
    // by the delegate to speed up processing.  This will force the validation.
    // Default is false.
    bool force_alt_validation;

    // Disable alternative validation in any case.  This is mainly useful for
    // debugging.  Default is false.
    bool disable_alt_validation;

    // Run CSE after AMS.
    bool cse;

    // Run CSE2 after AMS.
    bool cse2;

    // Run global CSE after AMS.
    bool gcse;

    // Allow new insns to be emitted when doing a validate_change to replace
    // memory addresses in insns.  If new insns are emitted it usually means
    // AMS is missing something.  It should usually not happen.  Enabled by
    // default.
    bool allow_mem_addr_change_new_insns;

    // Use this as a base look ahead count value for the algorithm that selects
    // alternatives.  Default is 1.
    int base_lookahead_count;
  };


  typedef int regno_t;

  // for a constant displacement using a 32 bit int should be sufficient.
  // however, we use it also to represent constant addresses.
  typedef int64_t disp_t;
  typedef int scale_t;

  enum
  {
    infinite_costs = INT_MAX// std::numeric_limits<int>::max ();
  };

  static const rtx invalid_regno;
  static const rtx any_regno;

  static regno_t get_regno (const_rtx x);

  // Comparison struct for sets and maps containing reg rtx-es.
  struct cmp_by_regno
  {
    bool operator () (const rtx a, const rtx b) const
    {
      return REGNO (a) < REGNO (b);
    }
  };

  // Return true if R1 and R2 is the same reg, or if both are NULL.
  static bool
  regs_equal (const rtx r1, const rtx r2)
  {
    if (!r1 && !r2)
      return true;
    if (!r1 || !r2)
      return false;
    return REGNO (r1) == REGNO (r2);
  }


  // the most complex non modifying address is of the form
  // 'base_reg + index_reg*scale + disp'.

  // a post/pre-modifying address can be of the form 'base_reg += disp'
  // or 'base_reg += mod_reg', although for now we support only the former.
  // if 'disp' is positive, it is a post/pre-increment.
  // if 'disp' is negative, it is a post/pre-decrement.
  // if abs ('disp') == access mode size it's a {PRE,POST}_{INC_DEC}.

  // we could use an abstract base class etc etc, but that usually implies
  // that we need to store objects thereof on the free store and keep the
  // pointers.  i.e. we can't pass/copy the whole thing by value and keep the
  // type info.  because of that we have one fat address expression base class
  // that keeps all the possible members of all subclasses.
  enum addr_type_t { non_mod, pre_mod, post_mod };

  class addr_expr
  {
  public:
    addr_expr (void) : m_cached_to_rtx (NULL) { }

    addr_type_t type (void) const { return m_type; }

    rtx base_reg (void) const { return m_base_reg; }
    bool has_base_reg (void) const { return base_reg () != invalid_regno; }
    bool has_no_base_reg (void) const { return !has_base_reg (); }

    disp_t disp (void) const { return m_disp; }
    disp_t disp_min (void) const { return m_disp_min; }
    disp_t disp_max (void) const { return m_disp_max; }
    bool has_disp (void) const { return disp () != 0; }
    bool has_no_disp (void) const { return !has_disp (); }

    rtx index_reg (void) const { return m_index_reg; }
    bool has_index_reg (void) const { return index_reg () != invalid_regno; }
    bool has_no_index_reg (void) const { return !has_index_reg (); }

    scale_t scale (void) const { return m_scale; }
    scale_t scale_min (void) const { return m_scale_min; }
    scale_t scale_max (void) const { return m_scale_max; }

    bool operator == (const addr_expr& other) const;
    bool operator != (const addr_expr& other) const;

    std::pair<disp_t, bool> operator - (const addr_expr& other) const;

    // returns true if the original address expression is more complex than
    // what AMS can handle.
    bool is_invalid (void) const { return disp_min () > disp_max (); }

    // displacement relative to the base reg before the actual memory access.
    // e.g. a pre-dec access will have a pre-disp of -mode_size.
    disp_t entry_disp (void) const { return type () == pre_mod ? disp () : 0; }

    // displacement relative to the base reg after the actual memory access.
    // e.g. a post-inc access will have a post-disp of +mode_size.
    disp_t exit_disp (void) const { return type () == post_mod ? disp () : 0; }

    // Convert this addr_expr into an rtx.
    // Notice that if it contains the any_regno placeholder, the resulting
    // rtx might not be completely valid.
    rtx to_rtx (void) const;

    // Mutating functions.
    void set_base_reg (rtx val);
    void set_index_reg (rtx val);
    void set_disp (disp_t val);
    void set_scale (scale_t val);

    // Comparison struct for sets and maps containing address expressions.
    struct compare
    {
      bool operator () (const sh_ams2::addr_expr& a,
                        const sh_ams2::addr_expr& b) const
      {
        if (a.is_invalid () && b.is_invalid ())
          return false;
        if (a.is_invalid () || b.is_invalid ())
          return a.is_invalid ();

        if (a.has_base_reg () && b.has_base_reg ())
          {
            if (REGNO (a.base_reg ()) != REGNO (b.base_reg ()))
              return REGNO (a.base_reg ()) < REGNO (b.base_reg ());
          }
        else if (a.has_base_reg () || b.has_base_reg ())
          return a.has_base_reg ();

        if (a.has_index_reg () && b.has_index_reg ())
          {
            if (REGNO (a.index_reg ()) != REGNO (b.index_reg ()))
              return REGNO (a.index_reg ()) < REGNO (b.index_reg ());
          }
        else if (a.has_index_reg () || b.has_index_reg ())
          return a.has_index_reg ();

        if (a.disp () == b.disp () && a.has_index_reg () && b.has_index_reg ())
          return a.scale () < b.scale ();
        return a.disp () < b.disp ();
      }
    };

  protected:
    addr_type_t m_type;

    // FIXME: on some architectures constant addresses can be used directly.
    // in such cases, after the constant pool layout has been determined,
    // the value of the base register will be e.g. a constant label_ref.
    // currently we can't deal with those.
    rtx m_base_reg;
    disp_t m_disp;
    disp_t m_disp_min;
    disp_t m_disp_max;
    rtx m_index_reg;
    scale_t m_scale;
    scale_t m_scale_min;
    scale_t m_scale_max;
    mutable rtx m_cached_to_rtx;
  };

  class non_mod_addr : public addr_expr
  {
  public:
    non_mod_addr (rtx base_reg, rtx index_reg, scale_t scale,
                  scale_t scale_min, scale_t scale_max,
                  disp_t disp, disp_t disp_min, disp_t disp_max);

    non_mod_addr (rtx base_reg, rtx index_reg, scale_t scale, disp_t disp);
  };

  class pre_mod_addr : public addr_expr
  {
  public:
    pre_mod_addr (rtx base_reg, disp_t disp, disp_t disp_min, disp_t disp_max);
    pre_mod_addr (rtx base_reg, disp_t disp);
  };

  class post_mod_addr : public addr_expr
  {
  public:
    post_mod_addr (rtx base_reg, disp_t disp, disp_t disp_min, disp_t disp_max);
    post_mod_addr (rtx base_reg, disp_t disp);
  };


  // helper functions to create a particular type of address expression.
  static addr_expr
  make_reg_addr (rtx base_reg = any_regno);

  static addr_expr
  make_disp_addr (disp_t disp_min, disp_t disp_max);

  static addr_expr
  make_disp_addr (rtx base_reg, disp_t disp_min, disp_t disp_max);

  static addr_expr
  make_const_addr (disp_t disp);

  static addr_expr
  make_const_addr (rtx disp);

  static addr_expr
  make_index_addr (scale_t scale_min, scale_t scale_max);

  static addr_expr
  make_index_addr (void);

  static addr_expr
  check_make_non_mod_addr (rtx base_reg, rtx index_reg,
                           HOST_WIDE_INT scale, HOST_WIDE_INT disp);

  static addr_expr
  make_post_inc_addr (machine_mode mode, rtx base_rtx = any_regno);

  static addr_expr
  make_post_dec_addr (machine_mode mode, rtx base_reg = any_regno);

  static addr_expr
  make_pre_inc_addr (machine_mode mode, rtx base_reg = any_regno);

  static addr_expr
  make_pre_dec_addr (machine_mode mode, rtx base_reg = any_regno);

  static addr_expr
  make_invalid_addr (void);


  struct delegate;

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // An alternative for an address mode.  These are usually provided
  // to AMS by the delegate for each memory access in an (access) sequence.
  class alternative
  {
  public:
    alternative (void) : m_valid (false) { }

    alternative (int cost, const addr_expr& ae)
    : m_valid (true), m_addr_expr (ae), m_cost (cost) { }

    const addr_expr& address (void) const { return m_addr_expr; }

    int cost (void) const { return m_cost; }
    void set_cost (int val) { m_cost = val; }
    void adjust_cost (int val) { m_cost += val; }

    bool valid (void) const { return m_valid; }
    void set_valid (bool val = true) { m_valid = val; }
    void set_invalid (bool val = true) { m_valid = !val; }

  private:
    // Tells whether this alternative is valid.  Initially the delegate
    // might add alternatives which are later found to be invalid, because
    // the specified addr_expr can't be used in a particular insn.  Invalid
    // alternatives are either skipped or removed from the alternative set
    // by AMS.
    bool m_valid;

    // The cost of using this alternative, relative to other alternatives
    // and to the various reg-mod costs used by AMS.  Can also be negative.
    int m_cost;

    // The address expression for this alternative, which might contain
    // the "any_regno" placeholder for registers.  The placeholders are
    // then substituted with register numbers by AMS when it decides to
    // use that alternative.
    addr_expr m_addr_expr;
  };

  // Support a limited number of alternatives only.
  typedef static_vector<alternative, 16> alternative_set;


  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // A sequence element's adjacency information.
  // Probably only useful for mem access elements and reg-uses.
  class adjacent_chain_info
  {
  public:
    adjacent_chain_info (void)
      : m_pos (0), m_len (1), m_first_acc (NULL), m_last_acc (NULL) { }
    adjacent_chain_info (int p, int l, const access* fa, const access* la)
      : m_pos (p), m_len (l), m_first_acc (fa), m_last_acc (la) { }

    int pos (void) const { return m_pos; }
    int length (void) const { return m_len; }

    bool is_first (void) const { return m_pos == 0; }
    bool is_last (void) const { return m_pos == m_len - 1; }

    const access* first (void) const { return m_first_acc; }
    const access* last (void) const { return m_last_acc; }

  private:
    int m_pos;
    int m_len;
    const access* m_first_acc;
    const access* m_last_acc;
  };

  // The type of an (access) sequence element.
  enum element_type
  {
    type_mem_load,
    type_mem_store,
    type_mem_operand,
    type_reg_mod,
    type_reg_barrier,
    type_reg_use
  };

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  class sequence_element;
  class mem_access;
  class mem_load;
  class mem_store;
  class mem_operand;
  class reg_mod;
  class reg_barrier;
  class reg_use;

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // Base class of an (access) sequence element.
  class sequence_element : public ref_counted
  {
  public:
    virtual ~sequence_element (void) { }

    // Returns the type of the element.  Could also use RTTI for this.
    element_type type (void) const { return m_type; }

    // The cost of this element in the sequence.
    int cost (void) const { return m_cost; }
    void set_cost (int new_cost) { m_cost = new_cost; }
    void adjust_cost (int d) { m_cost += d; }

    // The insn rtx of this element.  Maybe null if it has been inserted
    // by AMS into the sequence and is not present in the original insn list.
    rtx_insn* insn (void) const { return m_insn; }

    // An increasing/decreasing chain of adjacent accesses that this access
    // is part of.
    virtual const adjacent_chain_info&
    inc_chain (void) const { return g_no_incdec_chain; }

    virtual const adjacent_chain_info&
    dec_chain (void) const { return g_no_incdec_chain; }

    virtual void
    set_inc_chain (const adjacent_chain_info&) { }

    virtual void
    set_dec_chain (const adjacent_chain_info&) { }

    // List of all the immediate dependencies for this element.
    // E.g. if a reg-mod is required by a mem access, the reg-mod will be
    // listed here.  Another case are reg-mods that require the result of
    // other reg-mods.

/*
NOTE:
    specify the max number of predecessor BBs to visit when trying to trace
    back defs.  if the limit is exceeded a reg_barrier should be placed in
    the BB where the limit was exceeded.
*/

    const std::list<ref_counting_ptr<sequence_element> >&
    dependencies (void) const { return m_dependencies; }

    std::list<ref_counting_ptr<sequence_element> >&
    dependencies (void) { return m_dependencies; }


  protected:
    sequence_element (element_type t) : m_type (t), m_cost (0) { }

  private:
    static const adjacent_chain_info g_no_incdec_chain;

    // Changing the type after construction is not supported.
    const element_type m_type;

    int m_cost;
    rtx_insn* m_insn;

    std::list<ref_counting_ptr<sequence_element> > m_dependencies;
  };

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // Base class for a memory access element.
  class mem_access : public sequence_element
  {
  public:
    virtual ~mem_access (void) { }

    virtual const adjacent_chain_info&
    inc_chain (void) const { return m_inc_chain; }

    virtual const adjacent_chain_info&
    dec_chain (void) const { return m_dec_chain; }

    virtual void
    set_inc_chain (const adjacent_chain_info& c) { m_inc_chain = c; }

    virtual void
    set_dec_chain (const adjacent_chain_info& c) { m_dec_chain = c; }

    alternative_set& alternatives (void) { return m_alternatives; }
    const alternative_set& alternatives (void) const { return m_alternatives; }

    // FIXME: find shorter name.
    bool alternative_validation_enabled (void) const { return m_validate_alts; }
    void set_alternative_validation (bool val) { m_validate_alts = val; }

    bool matches_alternative (const alternative& alt) const;

    // Check if DISP can be used as constant displacement in any of the address
    // alternatives of the access.
    bool displacement_fits_alternative (disp_t disp) const;

    // Try replacing the current address in the mem(s) of the insn with
    // the specified one.  Returns true if the replacement seems OK or
    // false otherwise.
    virtual bool try_replace_addr (const addr_expr& new_addr) = 0;

    // Replace the current address in the mem(s) of the insn with the
    // specified one.  Returns true if the replacement was OK.
    // FIXME: also return the new insns that might have been generated
    // by target's legitimize_address (internally do a begin_sequence to
    // capture those new insns).
    // FIXME even more: the insns that are emitted when the address is
    // changed must be added to the dependencies of this access.  this is
    // important for multiple AMS sub-passes.
    virtual bool replace_addr (const addr_expr& new_addr) = 0;

    // The effective address expression.
    // Might be invalid if AMS was not able to understand it.
    const addr_expr& effective_addr (void) const { return m_effective_addr; }
    void set_effective_addr (const addr_expr& new_addr);

    // The address expression rtx as it is currently being used in the mem
    // rtx in the insn.
    rtx current_addr_rtx (void) const { return m_current_addr_rtx; }
    void set_current_addr_rtx (rtx new_addr_rtx);

    // The address expression that is currently being used.
    // Might be invalid if AMS was not able to understand it.
    const addr_expr& current_addr (void) const { return m_current_addr; }
    void set_current_addr (const addr_expr& new_addr);

  protected:
    mem_access (element_type t) : sequence_element (t) { }

    // The address expressions are usually set/updated by the sub-class.
    addr_expr m_effective_addr;
    addr_expr m_current_addr;
    rtx m_current_addr_rtx;

  private:
    bool m_validate_alts;
    alternative_set m_alternatives;
    adjacent_chain_info m_inc_chain;
    adjacent_chain_info m_dec_chain;
  };

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // A memory load -- an insn with only one mem rtx.
  class mem_load : public mem_access
  {
  public:
    mem_load (void) : mem_access (type_mem_load) { };

    virtual bool try_replace_addr_rtx (const addr_expr& new_addr);
    virtual bool replace_addr_rtx (const addr_expr& new_addr);

  private:
    // Reference into the rtx_insn where the mem rtx resides.
    rtx* m_mem_ref;
  };

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // A memory store -- an insn with only one mem rtx.
  class mem_store : public mem_access
  {
  public:
    mem_store (void) : mem_access (type_mem_store) { };

    virtual bool try_replace_addr (const addr_expr& new_addr);
    virtual bool replace_addr (const addr_expr& new_addr);

  private:
    // Reference into the rtx_insn where the mem rtx resides.
    rtx* m_mem_ref;
  };

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // A memory operand element is basically the same as a mem load and a
  // mem store.  The same address rtx is present in one insn in multiple
  // places.  When replacing/updating that address rtx, it must be done
  // for all the occurences at once.
  class mem_operand : public mem_access
  {
  public:
    mem_operand (void) : mem_access (type_mem_operand) { };

    virtual bool try_replace_addr (const addr_expr& new_addr);
    virtual bool replace_addr (const addr_expr& new_addr);

  private:
    // References into the rtx_insn where the mem rtx'es reside.
    static_vector<rtx*, 16> m_mem_ref;
  };

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // An address reg modification.
  // Usually this will be an insn that sets the reg to some other rtx.
  // It could also be a side-effect of an auto-inc or auto-mod mem access.
  class reg_mod : public sequence_element
  {
  public:
    reg_mod (void) : sequence_element (type_reg_mod) { };

    // The address reg that is being modified / defined.
    rtx reg (void) const { return m_reg; }

    // The rtx the reg is being set to.
    rtx value (void) const { return m_value; }

    // The address expression the reg is being set to.
    // Might be invalid if AMS was not able to understand it (-> barrier)
    const addr_expr& addr (void) const { return m_addr; }

    // The effective address expression the reg is being set to.
    // Might be invalid if AMS was not able to understand it (-> barrier)
    const addr_expr& effective_addr (void) const { return m_effective_addr; }

  private:
    rtx m_reg;
    rtx m_value;
    addr_expr m_addr;
    addr_expr m_effective_addr;
  };

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // A barrier for AMS which is inserted during dependency/def analysis
  // if AMS doesn't understand the value/calculation of some address register.
  // This barrier can't be removed by AMS.
  class reg_barrier : public sequence_element
  {
  public:
    reg_barrier (void) : sequence_element (type_reg_barrier) { };

    // The address reg which is being referenced by this barrier.
    rtx reg (void) const { return m_reg; }

  private:
    rtx m_reg;
  };

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // An address reg usage.
  // The usage consists of a single address reg and the expected value
  // which the reg must have at this point.
  // An access sequence which has no reg uses at the end is considered
  // an "open access sequence", i.e. the address reg of the last access
  // can have any value.
  // There can be multiple reg uses at the same insn.  For example after
  // two mem stores at different addresses, the two address regs are
  // combined in some calculation insn.  In this case there will be two
  // reg-use elements pointing at the same insn.
  // The (intermediate) result of a reg-mod could also be used either
  // by some interleaved access sequence unrelated code or after the
  // access sequence.  In this case the reg-mods can't be removed.  To know
  // that, add an artificial unspecified reg-use for the result reg.  If
  // it occurs "during" an access sequence, we can state the used reg directly
  // along with the expression.  If it occurs after the access sequence (i.e.
  // that reg doesn't die along the way), add an unspecified reg-use after
  // the access sequence.

  class reg_use : public sequence_element
  {
  public:
    reg_use (void) : sequence_element (type_reg_use) { };

    reg_use (rtx reg, const addr_expr& effective_addr);

    // construct a reg-use from an existing element.  this is usually used
    // when replacing an non-optimizable element into a reg-use.
    reg_use (const ref_counting_ptr<sequence_element>& e);

    virtual const adjacent_chain_info&
    inc_chain (void) const { return m_inc_chain; }

    virtual const adjacent_chain_info&
    dec_chain (void) const { return m_dec_chain; }

    virtual void
    set_inc_chain (const adjacent_chain_info& c) { m_inc_chain = c; }

    virtual void
    set_dec_chain (const adjacent_chain_info& c) { m_dec_chain = c; }

    // The reg that is being used.
    rtx reg (void) const { return *m_reg_ref; }

    // The effective address expression the reg is expected to have.
    const addr_expr& effective_addr (void) const { return m_effective_addr; }

  private:
    // if a mem access is not to be optimized, it is converted into a
    // reg-use.  in this case maybe it's useful to keep the original element
    // around.  the original element could also be a reg_mod, in case it's
    // an insn that AMS understands.  in this case AMS can optimize it away.
    // ref_counted_ptr<sequence_element> m_original;

    // The reg rtx inside the insn.
    rtx* m_reg_ref;

    addr_expr m_effective_addr;

    adjacent_chain_info m_inc_chain;
    adjacent_chain_info m_dec_chain;
  };


  class start_addr_list;
  typedef std::multimap<rtx, sequence_iterator, cmp_by_regno> addr_reg_map;

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // The access sequence that contains the memory accesses of some part of
  // the code (usually a basic block), along with other relevant information
  // (reg uses, reg mods, etc.).
  class sequence
  {
  public:
    // Update the original insn stream with the changes in this sequence.
    void update_insn_stream (bool allow_mem_addr_change_new_insns);

    // The total cost of the accesses in the sequence.
    int cost (void) const;

    // Re-calculate the cost.
    void update_cost (delegate& dlg);

    // Check whether the cost of the sequence is already minimal and
    // can't be improved further.
    bool cost_already_minimal (void) const;

    // Check whether REG is used in any of the sequence's accesses.
    bool reg_used_in_sequence (rtx reg);

    // Update the alternatives of the sequence's accesses.
    void update_access_alternatives (delegate& d, bool force_validation,
				     bool disable_validation);

    // Insert a new element into the sequence.  Return an iterator pointing
    // to the newly inserted element.
    sequence_iterator::iterator insert_element (sequence_iterator insert_before,
                                                sequence_element& el);

    // Remove an element from the sequence.  Return an iterator pointing
    // to the next element.
    sequence_iterator::iterator remove_element (sequence_iterator el);

    // The first insn and basic block in the sequence.
    rtx_insn* start_insn (void) const;
    basic_block start_bb (void) const;

    // A map containing the all the address regs used in the sequence
    // and the reg_mods that modify them.
    addr_reg_map& addr_regs (void) { return m_addr_regs; }

    // A structure for retrieving the starting addresses that could be
    // used to arrive at a given destination address.
    start_addr_list& start_addresses (void)  { return m_start_addr_list; }

    std::list<sequence_element>& elements (void) { return m_els; }
    const std::list<access>& elements (void) const { return m_els; }

    // iterator decorator for iterating over different types of elements
    // in the access sequence.
    template <typename Match>
    filter_iterator<iterator, Match> begin (void)
    {
      typedef filter_iterator<iterator, Match> iter;
      return iter (m_els.begin (), m_els.end ());
    }

    template <typename Match>
    filter_iterator<iterator, Match> end (void)
    {
      typedef filter_iterator<iterator, Match> iter;
      return iter (m_els.end (), m_els.end ());
    }

    template <typename Match>
    filter_iterator<const_iterator, Match> begin (void) const
    {
      typedef filter_iterator<const_iterator, Match> iter;
      return iter (m_els.begin (), m_els.end ());
    }

    template <typename Match>
    filter_iterator<const_iterator, Match> end (void) const
    {
      typedef filter_iterator<const_iterator, Match> iter;
      return iter (m_els.end (), m_els.end ());
    }

  private:
    std::list<sequence_element> m_els;
    addr_reg_map m_addr_regs;
    start_addr_list m_start_addr_list;

  };

  // A structure for keeping track of modifications to an access sequence.
  // Used in address mod generation for backtracking.
  class mod_tracker
  {
  public:
    mod_tracker (void)
      {
        m_inserted_accs.reserve (8);
        m_use_changed_accs.reserve (4);
        m_addr_changed_accs.reserve (4);
      }

    void reset_changes (sequence &as);

    // List of elements that were inserted into the sequence.
    std::vector<sequence_iterator>&
      inserted_els (void) { return m_inserted_els; }

    // List of elements that got visited.
    std::vector<sequence_iterator>&
      visited_els (void) { return m_visited_els; }

    // List of mem accesses whose address changed, along/ with their previous
    // values.
    std::vector<std::pair <sequence_iterator, addr_expr> >&
      addr_changed_accs (void) { return m_addr_changed_accs; }

  private:
    std::vector<sequence_iterator> m_inserted_els;
    std::vector<sequence_iterator> m_visited_els;
    std::vector<std::pair <sequence_iterator, addr_expr> > m_addr_changed_accs;
  };

  typedef std::list<sequence_element>::iterator sequence_iterator;
  typedef std::list<sequence_element>::const_iterator sequence_const_iterator;
  typedef std::list<sequence_element>::reverse_iterator sequence_reverse_iterator;
  typedef std::list<sequence_element>::const_reverse_iterator sequence_const_reverse_iterator;

  // A structure used to store the address regs that can be used as a starting
  // point to arrive at another address during address mod generation.
  class start_addr_list
  {
  public:

    typedef std::list<sequence_iterator>::iterator iterator;
    std::list<sequence_iterator>
      get_relevant_addresses (const addr_expr& end_addr);

    void add (sequence_iterator start_addr);
    void remove (sequence_iterator start_addr);

  private:

    // List of addresses that only have a constant displacement.
    std::list<sequence_iterator> m_const_addresses;

    // A map for storing addresses that have a base and/or index reg.
    // The key of each stored address is its base or index reg (the
    // address is stored twice if it has both).
    addr_reg_map m_reg_addresses;
  };

  // a delegate for the ams pass.  usually implemented by the target.
  struct delegate
  {
    // provide alternatives for the specified access.
    // use access::add_alternative.
    virtual void
    alternatives (alternative_set& alt, const sequence& as,
		  sequence_const_iterator acc, bool& validate_alternatives);

    // adjust the costs of the specified alternative of the specified
    // access.  called after the alternatives of all accesses have
    // been retrieved.
    virtual void
    adjust_alternative_costs (alternative& alt,
			      const sequence& as,
			      sequence_const_iterator acc);

    // provide the number of subsequent accesses that should be taken into
    // account when trying to minimize the costs of the specified access.
    virtual int
    adjust_lookahead_count (const sequence& as,
			    sequence_const_iterator acc);

    // provide the cost for setting the specified address register to
    // an rtx expression.
    // the cost must be somehow relative to the cost provided for access
    // alternatives.
    virtual int
    addr_reg_mod_cost (const_rtx reg, const_rtx val,
		       const sequence& as,
		       sequence_const_iterator acc);

    // provide the cost for cloning the address register, which is usually
    // required when splitting an access sequence.  if (address) register
    // pressure is high, return a higher cost to avoid splitting.
    //
    // FIXME: alternative would be 'sequence_split_cost'
    virtual int
    addr_reg_clone_cost (const_rtx reg, const sequence& as,
			 sequence_const_iterator acc);
  };

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -


  sh_ams2 (gcc::context* ctx, const char* name, delegate& dlg,
	  const options& opt = options ());

  virtual ~sh_ams2 (void);
  virtual bool gate (function* fun);
  virtual unsigned int execute (function* fun);

  void set_options (const options& opt);

private:
  static const pass_data default_pass_data;

  delegate& m_delegate;
  options m_options;
};

// ---------------------------------------------------------------------------

inline sh_ams2::regno_t
sh_ams2::get_regno (const_rtx x)
{
  if (x == NULL)
    return -1;
  if (x == any_regno)
    return -2;
  return REGNO (x);
}

inline sh_ams2::addr_expr
sh_ams2::make_reg_addr (rtx base_reg)
{
  return non_mod_addr (base_reg, invalid_regno, 0, 0, 0, 0, 0, 0);
}

inline sh_ams2::addr_expr
sh_ams2::make_disp_addr (disp_t disp_min, disp_t disp_max)
{
  return non_mod_addr (any_regno, invalid_regno, 0, 0, 0, 0, disp_min, disp_max);
}

inline sh_ams2::addr_expr
sh_ams2::make_disp_addr (rtx base_reg, disp_t disp_min, disp_t disp_max)
{
  return non_mod_addr (base_reg, invalid_regno, 0, 0, 0, 0, disp_min, disp_max);
}

inline sh_ams2::addr_expr
sh_ams2::make_const_addr (disp_t disp)
{
  return non_mod_addr (invalid_regno, invalid_regno, 0, 0, 0, disp, disp, disp);
}

inline sh_ams2::addr_expr
sh_ams2::make_const_addr (rtx disp)
{
  gcc_assert (CONST_INT_P (disp));
  return make_const_addr (INTVAL (disp));
}

inline sh_ams2::addr_expr
sh_ams2::make_index_addr (scale_t scale_min, scale_t scale_max)
{
  return non_mod_addr (any_regno, any_regno, 1, scale_min, scale_max, 0, 0, 0);
}

inline sh_ams2::addr_expr
sh_ams2::make_index_addr (void)
{
  return make_index_addr (1, 1);
}

inline sh_ams2::addr_expr
sh_ams2::make_post_inc_addr (machine_mode mode, rtx base_reg)
{
  const int mode_sz = GET_MODE_SIZE (mode);
  return post_mod_addr (base_reg, mode_sz, mode_sz, mode_sz);
}

inline sh_ams2::addr_expr
sh_ams2::make_post_dec_addr (machine_mode mode, rtx base_reg)
{
  const int mode_sz = -GET_MODE_SIZE (mode);
  return post_mod_addr (base_reg, mode_sz, mode_sz, mode_sz);
}

inline sh_ams2::addr_expr
sh_ams2::make_pre_inc_addr (machine_mode mode, rtx base_reg)
{
  const int mode_sz = GET_MODE_SIZE (mode);
  return pre_mod_addr (base_reg, mode_sz, mode_sz, mode_sz);
}

inline sh_ams2::addr_expr
sh_ams2::make_pre_dec_addr (machine_mode mode, rtx base_reg)
{
  const int mode_sz = -GET_MODE_SIZE (mode);
  return pre_mod_addr (base_reg, mode_sz, mode_sz, mode_sz);
}

inline sh_ams2::addr_expr
sh_ams2::make_invalid_addr (void)
{
  return make_disp_addr (-1, -2);
}

inline bool
sh_ams2::addr_expr::operator == (const addr_expr& other) const
{
  return base_reg () == other.base_reg ()
	 && index_reg () == other.index_reg ()
	 && scale () == other.scale ()
	 && disp () == other.disp ();
}

inline std::pair<sh_ams2::disp_t, bool>
sh_ams2::addr_expr::operator - (const addr_expr& other) const
{
  if (base_reg () == other.base_reg ()
      && index_reg () == other.index_reg ()
      && (scale () == other.scale () || has_no_index_reg ()))
    return std::make_pair (disp () - other.disp (), true);

  return std::make_pair (0, false);
}

inline sh_ams2::non_mod_addr
::non_mod_addr (rtx base_reg, rtx index_reg, scale_t scale,
		scale_t scale_min, scale_t scale_max,
		disp_t disp, disp_t disp_min, disp_t disp_max)
{
  m_type = non_mod;
  m_base_reg = base_reg;
  m_disp = disp;
  m_disp_min = disp_min;
  m_disp_max = disp_max;
  m_index_reg = index_reg;
  m_scale = scale;
  if (m_scale == 0)
    m_index_reg = invalid_regno;
  m_scale_min = scale_min;
  m_scale_max = scale_max;
}

inline sh_ams2::non_mod_addr
::non_mod_addr (rtx base_reg, rtx index_reg, scale_t scale, disp_t disp)
{
  m_type = non_mod;
  m_base_reg = base_reg;
  m_disp = disp;
  m_disp_min = disp;
  m_disp_max = disp;
  m_index_reg = index_reg;
  m_scale = scale;
  if (m_scale == 0)
    m_index_reg = invalid_regno;
  m_scale_min = scale;
  m_scale_max = scale;
}

inline sh_ams2::pre_mod_addr
::pre_mod_addr (rtx base_reg, disp_t disp, disp_t disp_min, disp_t disp_max)
{
  m_type = pre_mod;
  m_base_reg = base_reg;
  m_disp = disp;
  m_disp_min = disp_min;
  m_disp_max = disp_max;
  m_index_reg = invalid_regno;
  m_scale = m_scale_min = m_scale_max = 0;
}

inline sh_ams2::pre_mod_addr
::pre_mod_addr (rtx base_reg, disp_t disp)
{
  m_type = pre_mod;
  m_base_reg = base_reg;
  m_disp = disp;
  m_disp_min = disp;
  m_disp_max = disp;
  m_index_reg = invalid_regno;
  m_scale = m_scale_min = m_scale_max = 0;
}

inline sh_ams2::post_mod_addr
::post_mod_addr (rtx base_reg, disp_t disp, disp_t disp_min, disp_t disp_max)
{
  m_type = post_mod;
  m_base_reg = base_reg;
  m_disp = disp;
  m_disp_min = disp_min;
  m_disp_max = disp_max;
  m_index_reg = invalid_regno;
  m_scale = m_scale_min = m_scale_max = 0;
}

inline sh_ams2::post_mod_addr
::post_mod_addr (rtx base_reg, disp_t disp)
{
  m_type = post_mod;
  m_base_reg = base_reg;
  m_disp = disp;
  m_disp_min = disp;
  m_disp_max = disp;
  m_index_reg = invalid_regno;
  m_scale = m_scale_min = m_scale_max = 0;
}

#endif // includeguard_gcc_sh_ams2_includeguard
