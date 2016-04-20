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


#ifndef includeguard_gcc_sh_ams_includeguard
#define includeguard_gcc_sh_ams_includeguard

#include "tree-pass.h"
#include <limits>
#include <list>
#include <vector>
#include <functional>
#include <map>
#include <set>
#include <string>

#include "filter_iterator.h"

class sh_ams : public rtl_opt_pass
{
public:
  enum addr_type_t { non_mod, pre_mod, post_mod };

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

  class access;
  class access_sequence;
  class addr_expr;
  struct delegate;

  // Comparison struct for sets and maps containing reg rtx-es.
  struct cmp_by_regno
  {
    bool operator () (const rtx a, const rtx b) const
    {
      return REGNO (a) < REGNO (b);
    }
  };

  // Comparison struct for sets and maps containing address expressions.
  struct cmp_addr_expr
  {
    bool operator () (const sh_ams::addr_expr& a,
                      const sh_ams::addr_expr& b) const
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
  class addr_expr
  {
  public:
    addr_expr (void) : m_cached_to_rtx (NULL) { }

    addr_type_t type (void) const { return m_type; }

    rtx base_reg (void) const
    {
      gcc_assert (!is_invalid ());
      return m_base_reg;
    }
    bool has_base_reg (void) const { return base_reg () != invalid_regno; }
    bool has_no_base_reg (void) const { return !has_base_reg (); }

    disp_t disp (void) const { return m_disp; }
    disp_t disp_min (void) const { return m_disp_min; }
    disp_t disp_max (void) const { return m_disp_max; }
    bool has_disp (void) const { return disp () != 0; }
    bool has_no_disp (void) const { return !has_disp (); }

    rtx index_reg (void) const
    {
      gcc_assert (!is_invalid ());
      return m_index_reg;
    }
    bool has_index_reg (void) const { return index_reg () != invalid_regno; }
    bool has_no_index_reg (void) const { return !has_index_reg (); }

    scale_t scale (void) const { return m_scale; }
    scale_t scale_min (void) const { return m_scale_min; }
    scale_t scale_max (void) const { return m_scale_max; }

    template <typename OutputIterator> void
    get_all_subterms (OutputIterator out) const;

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

  // an element in the access sequence.  can be a real memory access insn
  // or address register modification or address register use insn.
  // FIXME: extend this to handle
  //         - memory operands (e.g. SH's GBR mem logic insns)
  //         - some kind of multiple use (e.g. SH's atomic insns)
  enum access_type_t { load, store, reg_mod, reg_use };

  class access
  {
  public:

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
      bool m_valid;
      addr_expr m_addr_expr;
      int m_cost;
    };

    struct alternative_valid;
    struct alternative_invalid;

    // for now the alternative set is basically a boost::static_vector.
    class alternative_set
    {
    public:
      typedef alternative value_type;

      // copied from std::array
      typedef value_type*			      pointer;
      typedef const value_type*                       const_pointer;
      typedef value_type&                   	      reference;
      typedef const value_type&             	      const_reference;
      typedef value_type*          		      iterator;
      typedef const value_type*			      const_iterator;
      typedef unsigned int                    	      size_type;
      typedef std::ptrdiff_t                   	      difference_type;
      typedef std::reverse_iterator<iterator>	      reverse_iterator;
      typedef std::reverse_iterator<const_iterator>   const_reverse_iterator;

      alternative_set (void) : m_size (0) { }

      reference at (size_type pos);
      const_reference at (size_type pos) const;

      reference operator [] (size_type pos) { return m_data[pos]; }
      const_reference operator [] (size_type pos) const { return m_data[pos]; }

      reference front (void) { return m_data[0]; }
      const_reference front (void) const { return m_data[0]; }

      reference back (void) { return m_data[m_size - 1]; }
      const_reference back (void) const { return m_data[m_size - 1]; }

      pointer data (void) { return m_data; }
      const_pointer data (void) const { return m_data; }

      iterator begin (void) { return m_data; }
      const_iterator begin (void) const { return m_data; }
      const_iterator cbegin (void) const { return m_data; }

      iterator end (void) { return m_data + size (); }
      const_iterator end (void) const { return m_data + size (); }
      const_iterator cend (void) const { return m_data + size (); }

      reverse_iterator rbegin (void) { return reverse_iterator (end ()); }

      const_reverse_iterator
      rbegin (void) const { return const_reverse_iterator (end ()); }

      const_reverse_iterator
      crbegin (void) const { return const_reverse_iterator (end ()); }

      reverse_iterator rend (void) { return reverse_iterator (begin ()); }

      const_reverse_iterator
      rend (void) const { return const_reverse_iterator (begin ()); }

      const_reverse_iterator
      crend (void) const { return const_reverse_iterator (begin ()); }

      bool empty (void) const { return size () == 0; }
      size_type size (void) const { return m_size; }
      size_type max_size (void) const { return max_data_size; }
      size_type capacity (void) const { return max_data_size; }

      void clear (void) { m_size = 0; }
      void push_back (const value_type& v);
      void pop_back (void) { --m_size; }

    private:
      enum { max_data_size = 16 };

      size_type m_size;
      alternative m_data[max_data_size];
    };

    class adjacent_chain
    {
    public:
      adjacent_chain (void) : m_pos (0), m_len (1) { }
      adjacent_chain (int p, int l) : m_pos (p), m_len (l) { }

      int pos (void) const { return m_pos; }
      int length (void) const { return m_len; }

      bool first (void) const { return m_pos == 0; }
      bool last (void) const { return m_pos == m_len - 1; }

    private:
      int m_pos;
      int m_len;
    };

    access (rtx_insn* insn, rtx* mem, access_type_t access_type,
	    addr_expr original_addr_expr, addr_expr addr_expr,
	    bool should_optimize, int cost = infinite_costs);
    access (rtx_insn* insn, addr_expr original_addr_expr, addr_expr addr_expr,
	    rtx addr_rtx, rtx alias_mod_reg, rtx real_mod_reg, int cost);
    access (rtx_insn* insn, std::vector<rtx_insn*> trailing_insns,
            rtx* reg_ref, addr_expr original_addr_expr,
	    addr_expr addr_expr, int cost);
    access (rtx addr_reg, addr_expr reg_value);

    // If m_access_type is REG_MOD, this access represents the modification
    // of an address register.  In this case, 'address_reg' returns the
    // register that's modified and 'address' returns its new address.
    // If the original address is invalid, appropriate reg-mods are inserted
    // during address mod generation to arrive at the effective address.
    //
    // If the type is REG_USE, the access represents the use of an address
    // reg outside of a memory access.  In this case, 'address' returns the
    // effective address of the address reg during the use and m_mem_ref is
    // a reference to the rtx inside the insn that uses the reg.
    access_type_t access_type (void) const { return m_access_type; }

    // the effective address expression, i.e. the register and constant value
    // have been traced through reg copies etc and the address expression has
    // been canonicalized.
    const addr_expr& address (void) const { return m_addr_expr; }

    // the original address expression as it was found in the insn stream.
    // if the original address expression does not fit into our scheme, we
    // ignore it.
    const addr_expr& original_address (void) const { return m_original_addr_expr; }
    addr_expr& original_address (void) { return m_original_addr_expr; }

    machine_mode mach_mode (void) const { return m_machine_mode; }
    int access_size (void) const { return GET_MODE_SIZE (m_machine_mode); }
    addr_space_t addr_space (void) const { return m_addr_space; }
    int cost (void) const { return m_cost; }

    // the insn where this access occurs.
    rtx_insn* insn (void) const { return m_insn; }

    // for reg_mod accesses, the insn before or after which the access' insn
    // should be emitted during the insn update.
    rtx_insn* emit_before_insn (void) const { return m_emit_before_insn; }
    void set_emit_before_insn (rtx_insn* i) { m_emit_before_insn = i; }
    rtx_insn* emit_after_insn (void) const { return m_emit_after_insn; }
    void set_emit_after_insn (rtx_insn* i) { m_emit_after_insn = i; }

    // returns the rtx inside the insn that this access refers to.
    // for mem accesses it will be the address expression inside the mem.
    // for reg mods it will be the set source rtx.
    // FIXME: this should actually be addr_rtx.
    rtx addr_rtx_in_insn (void) const { return m_mem_ref ? *m_mem_ref : NULL; }

    // Returns the address rtx if the address expression can't be described
    // with an addr_expr, or null if the address is unknown.
    rtx addr_rtx (void) const { return m_addr_rtx; }

    // If false, AMS skips this access when optimizing.
    bool should_optimize (void) const { return m_should_optimize; }
    void set_should_optimize (bool val) { m_should_optimize = val; }

    // For reg_mod accesses, returns the register rtx that is being modified.
    rtx address_reg (void) const { return m_addr_reg; }

    // For reg_mod accesses that use an alias, returns the real address reg
    // that appears in the insn stream.
    rtx real_address_reg  (void) const { return m_real_addr_reg; }

    // For reg_mod accesses, tells whether the register is used in another
    // access or not.  If so, register cloning costs must be taken into
    // account when using it a second time.
    bool is_used (void) const { return m_used; }
    void set_used (void) { m_used = true; }
    void set_unused (void) { m_used = false; }

    bool visited (void) const { return m_visited; }
    void set_visited (void)  { m_visited = true; }
    void reset_visited (void)  { m_visited = true; }

    // For reg_mod accesses, true if the address reg still has the
    // same value at the sequence's end as in this access and the
    // register is not dead by that time.
    bool valid_at_end (void) const { return m_valid_at_end; }
    void set_valid_at_end (void) { m_valid_at_end = true; }
    void set_invalid_at_end (void) { m_valid_at_end = false; }

    // Return true if this is a trailing access, i,e. the first use or
    // modification of an address reg that follows the last access in the
    // sequence (which could be possibly in another BB).
    // There can be multiple trailing accesses if the addr reg is
    // set/used in more than one successor BBs.
    bool is_trailing (void) const { return !trailing_insns ().empty (); }

    // If the access is part of an increasing/decreasing chain of adjacent
    // accesses, return the length of that chain and its position in the
    // chain.
    const adjacent_chain& inc_chain (void) const { return m_inc_chain; }
    const adjacent_chain& dec_chain (void) const { return m_dec_chain; }

    void set_inc_chain (const adjacent_chain& c) { m_inc_chain = c; }
    void set_dec_chain (const adjacent_chain& c) { m_dec_chain = c; }

    // For a trailing access, the insns where the reg use/mod occur.
    const std::vector<rtx_insn*>& trailing_insns (void) const
    { return m_trailing_insns; }

    alternative_set& alternatives (void) { return m_alternatives; }
    const alternative_set& alternatives (void) const { return m_alternatives; }

    bool matches_alternative (const alternative& alt) const;
    bool displacement_fits_alternative (disp_t disp) const;

    void set_original_address (int new_cost, const addr_expr& new_addr_expr);
    void set_original_address (int new_cost, rtx new_addr_rtx);
    void set_effective_address (const addr_expr& new_addr_expr);

    void set_cost (int new_cost) { m_cost = new_cost; }
    void adjust_cost (int d) { m_cost += d; }

    bool set_insn_mem_rtx (rtx new_addr, bool allow_new_insns);
    bool try_set_insn_mem_rtx (rtx new_addr);

    bool set_insn_use_rtx (rtx new_expr);
    void set_insn (rtx_insn* new_insn);

    bool validate_alternatives (void) const { return m_validate_alternatives; }
    void set_validate_alternatives (bool val = true);

  private:
    addr_expr m_original_addr_expr;
    addr_expr m_addr_expr;
    addr_expr m_real_addr_expr;
    access_type_t m_access_type;
    machine_mode m_machine_mode;
    addr_space_t m_addr_space;
    int m_cost;
    rtx_insn* m_insn;
    rtx_insn* m_emit_before_insn;
    rtx_insn* m_emit_after_insn;
    std::vector<rtx_insn*> m_trailing_insns;
    rtx* m_mem_ref; // reference to the mem rtx inside the insn.
    bool m_should_optimize;
    rtx m_addr_rtx;
    rtx m_addr_reg;
    rtx m_real_addr_reg;
    bool m_used;
    bool m_visited;
    bool m_valid_at_end;
    bool m_validate_alternatives;

    adjacent_chain m_inc_chain;
    adjacent_chain m_dec_chain;

    alternative_set m_alternatives;
  };

  template <access_type_t T1, access_type_t T2 = T1, access_type_t T3 = T1>
  struct access_type_matches
  {
    bool operator () (const access& a) const
    {
      return a.access_type () == T1 || a.access_type () == T2
	     || a.access_type () == T3;
    }
  };

  struct access_to_optimize;


  // Return true if the effective address of FIRST and SECOND only differs in
  // the constant displacement and the difference is the access size of FIRST.
  static bool adjacent_inc (const access& first, const access& second);
  static bool not_adjacent_inc (const access& first, const access& second);

  // Same as adjacent_inc, except that the displacement of SECOND should
  // be the smaller one.
  static bool adjacent_dec (const access& first, const access& second);
  static bool not_adjacent_dec (const access& first, const access& second);

  class access_sequence
  {
  public:

    typedef std::list<access>::iterator iterator;
    typedef std::list<access>::const_iterator const_iterator;
    typedef std::list<access>::reverse_iterator reverse_iterator;
    typedef std::list<access>::const_reverse_iterator const_reverse_iterator;

    access_sequence (void) : m_modify_insns (false) {}

    void gen_address_mod (delegate& dlg, int base_lookahead);

    void eliminate_reg_copies (void);

    void update_insn_stream (bool allow_mem_addr_change_new_insns);
    bool modify_insns (void) const { return m_modify_insns; }
    void set_modify_insns (bool mod) { m_modify_insns = mod; }

    int cost (void) const;
    void update_cost (delegate& dlg);
    bool cost_already_minimal (void) const;

    void find_addr_regs (bool handle_call_used_regs = false);
    void add_missing_reg_mods (void);

    bool reg_used_in_sequence (rtx reg, access_sequence::iterator search_start);
    bool reg_used_in_sequence (rtx reg);

    void find_reg_uses (delegate& dlg);
    void find_reg_end_values (void);

    void calculate_adjacency_info (void);

    void update_access_alternatives (delegate& d, access_sequence::iterator a,
				     bool force_validation,
				     bool disable_validation);

    access&
    add_mem_access (rtx_insn* insn, rtx* mem, access_type_t access_type);

    access&
    add_reg_mod (rtx_insn* insn, const addr_expr& original_addr_expr,
                 const addr_expr& addr_expr, rtx addr_rtx,
                 rtx_insn* mod_insn, rtx reg, rtx real_reg,
                 int cost = infinite_costs);

    access&
    add_reg_mod (rtx_insn* insn, const addr_expr& original_addr_expr,
                 const addr_expr& addr_expr, rtx_insn* mod_insn,
                 rtx reg, rtx real_reg, int cost = infinite_costs);

    access&
    add_reg_mod (rtx_insn* insn, rtx addr_rtx, rtx_insn* mod_insn,
                 rtx reg, rtx real_reg, int cost = infinite_costs);

    access&
    add_reg_mod (access_sequence::iterator insert_before,
                 const addr_expr& original_addr_expr,
                 const addr_expr& addr_expr, rtx_insn* mod_insn,
                 rtx reg, rtx real_reg, int cost = infinite_costs,
		 bool use_as_start_addr = true);

    access&
    add_reg_mod (access_sequence::iterator insert_before,
                 const addr_expr& original_addr_expr,
                 const addr_expr& addr_expr, rtx_insn* mod_insn,
                 rtx reg, int cost = infinite_costs,
                 bool use_as_start_addr = true);

    access&
    add_reg_use (access_sequence::iterator insert_before,
		 const addr_expr& original_addr_expr,
		 const addr_expr& addr_expr,
		 rtx* reg_ref,
		 rtx_insn* use_insn, int cost);
    access&
    add_reg_use (access_sequence::iterator insert_before,
		 const addr_expr& original_addr_expr,
		 const addr_expr& addr_expr,
		 rtx* reg_ref,
		 std::vector<rtx_insn*> use_insns, int cost);

    access_sequence::iterator
    remove_access (access_sequence::iterator acc);

    basic_block start_bb (void) const;
    rtx_insn* start_insn (void) const;

    std::list<access>& accesses (void) { return m_accs; }
    const std::list<access>& accesses (void) const { return m_accs; }

    typedef std::multimap<rtx, access_sequence::iterator, cmp_by_regno> addr_reg_map;

    // A map containing the address regs of the sequence and the last
    // reg_mod access that modified them.
    addr_reg_map& addr_regs (void) { return m_addr_regs; }

    // A structure used to store the address regs that can be used as a starting
    // point to arrive at another address during address mod generation.
    class start_addr_list
    {
    public:

      typedef std::list<access_sequence::iterator>::iterator iterator;
      std::list<sh_ams::access_sequence::iterator>
      get_relevant_addresses (const addr_expr& end_addr);

      void add (access_sequence::iterator start_addr);
      void remove (access_sequence::iterator start_addr);

    private:

      // List of addresses that only have a constant displacement.
      std::list<access_sequence::iterator> m_const_addresses;

      // A map for storing addresses that have a base and/or index reg.
      // The key of each stored address is its base or index reg (the
      // address is stored twice if it has both).
      addr_reg_map m_reg_addresses;
    };

    // A structure storing the reg_mod accesses from the sequence in such way
    // that they can be searched through efficiently when looking for possible
    // starting addresses to use for arriving at a given end address.
    start_addr_list& start_addresses (void)  { return m_start_addr_list; }

    // A structure used to store the reg aliases.  A register gets an alias when
    // it's set to an unknown value so that the reg that holds the new value
    // can be distinguished from the reg that holds the old value when tracing
    // back address expressions.
    class reg_alias_list
    {
    public:

      // Get the alias for REG, if any.
      rtx get_alias (const rtx reg) const {
        alias_map::const_iterator alias_reg = m_aliases.find (reg);
        return (alias_reg == m_aliases.end ()) ? reg : alias_reg->second;
      }

      rtx substitute_regs_with_aliases (rtx x);
      void add_alias_at_insn (rtx reg, rtx alias_reg, rtx_insn* insn);
      void remove_aliases_between_insns (rtx_insn* start_insn,
                                         rtx_insn* end_insn);
      void add_aliases_between_insns (rtx_insn* start_insn,
                                      rtx_insn* end_insn);

    private:

      struct alias_state_change
      {
        rtx reg, alias, prev_alias;
        alias_state_change (rtx r, rtx a, rtx p)
        : reg (r), alias (a), prev_alias (p) {}
      };

      typedef std::map<rtx, rtx, cmp_by_regno> alias_map;
      typedef std::multimap<rtx_insn*, alias_state_change> state_change_map;

      state_change_map m_state_changes;
      alias_map m_aliases;
    };

    // The reg aliases in this sequence.
    reg_alias_list& reg_aliases (void)  { return m_reg_alias_list; }

    // iterator decorator for iterating over different types of elements
    // in the access sequence.
    template <typename Match>
    filter_iterator<iterator, Match> begin (void)
    {
      typedef filter_iterator<iterator, Match> iter;
      return iter (m_accs.begin (), m_accs.end ());
    }

    template <typename Match>
    filter_iterator<iterator, Match> end (void)
    {
      typedef filter_iterator<iterator, Match> iter;
      return iter (m_accs.end (), m_accs.end ());
    }

    template <typename Match>
    filter_iterator<const_iterator, Match> begin (void) const
    {
      typedef filter_iterator<const_iterator, Match> iter;
      return iter (m_accs.begin (), m_accs.end ());
    }

    template <typename Match>
    filter_iterator<const_iterator, Match> end (void) const
    {
      typedef filter_iterator<const_iterator, Match> iter;
      return iter (m_accs.end (), m_accs.end ());
    }

  private:

    // A structure for keeping track of modifications to the access sequence.
    // Used in gen_min_mod for backtracking.
    class mod_tracker
    {
    public:
      mod_tracker (void)
      {
        m_inserted_accs.reserve (8);
        m_use_changed_accs.reserve (4);
        m_addr_changed_accs.reserve (4);
      }

      void reset_changes (access_sequence &as)
      {
        std::for_each (inserted_accs ().rbegin (), inserted_accs ().rend (),
            std::bind1st (std::mem_fun (&access_sequence::remove_access), &as));
        inserted_accs ().clear ();

        for (std::vector<access_sequence::iterator>::iterator
               it = use_changed_accs ().begin ();
             it != use_changed_accs ().end (); ++it)
          (*it)->set_unused ();
        use_changed_accs ().clear ();

        for (std::vector<std::pair <access_sequence::iterator, addr_expr> >::reverse_iterator
               it = addr_changed_accs ().rbegin ();
             it != addr_changed_accs ().rend (); ++it)
          it->first->set_original_address (0, it->second);
        addr_changed_accs ().clear ();
      }

      // List of accesses that were inserted into the sequence.
      std::vector<access_sequence::iterator>&
      inserted_accs (void) { return m_inserted_accs; }

      // List of accesses whose M_USED field was changed.
      std::vector<access_sequence::iterator>&
      use_changed_accs (void) { return m_use_changed_accs; }

      // List of accesses whose M_ORIGINAL_ADDR_EXPR changed, along
      // with their previous values.
      std::vector<std::pair <access_sequence::iterator, addr_expr> >&
      addr_changed_accs (void) { return m_addr_changed_accs; }

    private:
      std::vector<access_sequence::iterator> m_inserted_accs;
      std::vector<access_sequence::iterator> m_use_changed_accs;
      std::vector<std::pair <access_sequence::iterator, addr_expr> > m_addr_changed_accs;
    };

    // Used for keeping track of register copying accesses
    // in eliminate_reg_copies.
    struct reg_copy
    {
      rtx src, dest;
      access_sequence::iterator acc;
      bool reg_modified;
      bool can_be_removed;
      reg_copy (rtx s, rtx d, access_sequence::iterator a)
      : src (s), dest (d), acc (a),
        reg_modified (false), can_be_removed (true) {}
    };

    int get_clone_cost (access_sequence::iterator &acc, delegate& dlg);

    void visit_insns_until_next_acc (access_sequence::iterator acc,
                                     std::set<rtx_insn*>& visited_insns,
                                     rtx_insn* last_insn);

    void gen_reg_mod_insn (access& acc);

    int gen_min_mod (filter_iterator<iterator, access_to_optimize> acc,
                     delegate& dlg, int lookahead_num,
                     bool record_in_sequence);

    void gen_mod_for_alt (access::alternative& alternative,
			  access_sequence::iterator start_base,
			  access_sequence::iterator start_index,
			  const addr_expr& end_base,
			  const addr_expr& end_index,
			  access_sequence::iterator acc,
			  mod_tracker& mod_tracker,
			  delegate& dlg);

    struct min_mod_cost_result
    {
      int cost;
      access_sequence::iterator min_start_addr;

      min_mod_cost_result (void)
      : cost (infinite_costs) { }

      min_mod_cost_result (int c, access_sequence::iterator a)
      : cost (c), min_start_addr (a) { }
    };

    min_mod_cost_result
    find_min_mod_cost (const addr_expr& end_addr,
		       access_sequence::iterator acc,
		       disp_t disp_min, disp_t disp_max,
		       addr_type_t addr_type, delegate& dlg);

    struct mod_addr_result
    {
      int cost;
      rtx addr_reg;
      disp_t addr_disp;

      mod_addr_result (void)
      : cost (infinite_costs), addr_reg (invalid_regno), addr_disp (0) { }

      mod_addr_result (rtx regno)
      : cost (infinite_costs), addr_reg (regno), addr_disp (0) { }

      mod_addr_result (rtx regno, disp_t disp)
      : cost (infinite_costs), addr_reg (regno), addr_disp (disp) { }

      mod_addr_result (int c, rtx regno, disp_t disp)
      : cost (c), addr_reg (regno), addr_disp (disp) { }
    };

    mod_addr_result
    try_modify_addr (access_sequence::iterator start_addr, const addr_expr& end_addr,
		     disp_t disp_min, disp_t disp_max, addr_type_t addr_type,
		     machine_mode mode,
		     access_sequence::iterator acc,
		     mod_tracker &mod_tracker,
		     delegate& dlg);

    access_sequence::iterator find_start_addr_for_reg (rtx reg);

    std::list<access> m_accs;
    addr_reg_map m_addr_regs;
    start_addr_list m_start_addr_list;
    reg_alias_list m_reg_alias_list;
    bool m_modify_insns;
  };

  // a delegate for the ams pass.  usually implemented by the target.
  struct delegate
  {
    // provide alternatives for the specified access.
    // use access::add_alternative.
    virtual void
    mem_access_alternatives (access::alternative_set& alt,
			     const access_sequence& as,
			     access_sequence::const_iterator acc,
			     bool& validate_alternatives) = 0;

    // adjust the costs of the specified alternative of the specified
    // access.  called after the alternatives of all accesses have
    // been retrieved.
    virtual void
    adjust_alternative_costs (access::alternative& alt,
			      const access_sequence& as,
			      access_sequence::const_iterator acc) = 0;

    // provide the number of subsequent accesses that should be taken into
    // account when trying to minimize the costs of the specified access.
    virtual int
    adjust_lookahead_count (const access_sequence& as,
			    access_sequence::const_iterator acc) = 0;

    // provide the cost for setting the specified address register to
    // an rtx expression.
    // the cost must be somehow relative to the cost provided for access
    // alternatives.
    virtual int
    addr_reg_mod_cost (const_rtx reg, const_rtx val,
		       const access_sequence& as,
		       access_sequence::const_iterator acc) = 0;

    // provide the cost for cloning the address register, which is usually
    // required when splitting an access sequence.  if (address) register
    // pressure is high, return a higher cost to avoid splitting.
    //
    // FIXME: alternative would be 'sequence_split_cost'
    virtual int
    addr_reg_clone_cost (const_rtx reg,
			 const access_sequence& as,
			 access_sequence::const_iterator acc) = 0;
  };

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

    // Simplify the sequences after optimization by removing unecessary
    // reg copies.  Default is true.
    bool remove_reg_copies;

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

  sh_ams (gcc::context* ctx, const char* name, delegate& dlg,
	  const options& opt = options ());

  virtual ~sh_ams (void);
  virtual bool gate (function* fun);
  virtual unsigned int execute (function* fun);

  void set_options (const options& opt);

private:
  static int
  get_reg_mod_cost (delegate &dlg, const_rtx reg, const_rtx val,
                    const access_sequence& as,
                    access_sequence::const_iterator acc);

  // Used to keep track of shared address (sub)expressions
  // during access sequence splitting.
  class shared_term
  {
  public:
    shared_term (addr_expr& t, access* acc)
      : m_term (t), m_sharing_accs () {
      m_sharing_accs.push_back (acc);
    }

    // The shared term.
    const addr_expr& term () { return m_term; }

    // The accesses that share this term.
    std::vector<access*>& sharing_accs () { return m_sharing_accs; }

    // A score that's used to determine which shared expressions should
    // be used for splitting access sequences.  A higher score means that
    // the shared term is more likely to be selected as a base for a
    // new sequence.
    unsigned int score (void) const
    {
      if (m_term.is_invalid ())
        return 0;

      unsigned int score = 10;

      // Displacement-only terms with large displacements are
      // represented with a constant 0 address.
      if (m_term.has_no_base_reg () && m_term.has_no_index_reg ()
          && m_term.has_no_disp ())
        score += 2;

      if (m_term.has_base_reg ())
        score += 2;
      if (m_term.has_index_reg ())
        {
          score += 2;
          if (m_term.scale () != 1)
            ++score;
        }
      if (m_term.has_disp ())
        ++score;

      return score*m_sharing_accs.size ();
    }

    static bool compare (shared_term* a, shared_term* b)
    { return a->score () > b->score (); }

  private:
    addr_expr m_term;
    std::vector<access*> m_sharing_accs;
  };

  // Used to store information about newly created sequences during
  // sequence splitting.
  class split_sequence_info
  {
  public:
    split_sequence_info (access_sequence* as)
      : m_as (as), m_addr_regs () {}

    // The sequence itself.
    access_sequence* as (void) const { return m_as; }

    // Return true if REG is present in m_addr_regs.
    bool uses_addr_reg (rtx reg) const
    {
      return m_addr_regs.find (reg) != m_addr_regs.end ();
    }

    // Add REG to the address reg lists.
    void add_reg (rtx reg) { m_addr_regs.insert (reg); }

  private:
    access_sequence *m_as;

    // A set of the address registers used in the sequence.
    std::set<rtx, cmp_by_regno> m_addr_regs;
  };

  static std::list<access_sequence>::iterator
  split_access_sequence (std::list<access_sequence>::iterator as_it,
                         std::list<access_sequence>& sequences);

  static void
  split_access_sequence_1 (
    std::map<addr_expr, split_sequence_info, cmp_addr_expr>& new_seqs,
    sh_ams::access &acc,
    bool add_to_front, bool add_to_back);

  static void
  split_access_sequence_2 (split_sequence_info& addr_regs, sh_ams::access& acc);

  template <typename OutputIterator> static void
  collect_addr_reg_uses (access_sequence& as, rtx addr_reg,
			 rtx_insn *start_insn, rtx abort_at_insn,
			 OutputIterator out,
                         bool skip_addr_reg_mods,
                         bool stay_in_curr_bb,
                         bool stop_after_first);

  template <typename OutputIterator> static void
  collect_addr_reg_uses (access_sequence& as, rtx_insn *start_insn,
                         rtx abort_at_insn, OutputIterator out,
                         bool skip_addr_reg_mods,
                         bool stay_in_curr_bb ,
                         bool stop_after_first)
  {
    collect_addr_reg_uses (as, NULL, start_insn, abort_at_insn, out,
			   skip_addr_reg_mods, stay_in_curr_bb,
			   stop_after_first);
  }

  template <typename OutputIterator> static void
  collect_addr_reg_uses_1 (access_sequence& as, rtx addr_reg,
                           rtx_insn *start_insn, basic_block bb,
                           std::vector<basic_block>& visited_bb,
                           rtx abort_at_insn, OutputIterator out,
                           bool skip_addr_reg_mods,
                           bool stay_in_curr_bb,
                           bool stop_after_first);

  template <typename OutputIterator> static bool
  collect_addr_reg_uses_2 (access_sequence& as, rtx addr_reg,
                           rtx_insn *insn, rtx& x, OutputIterator out,
                           bool skip_addr_reg_mods);

  static bool visited_addr_reg (rtx x, rtx addr_reg, access_sequence& as);

  struct find_reg_value_result
  {
    rtx value;
    rtx_insn* mod_insn;
    machine_mode auto_mod_mode;

    find_reg_value_result (void)
    : value (NULL), mod_insn (NULL), auto_mod_mode (Pmode) { }

    find_reg_value_result (rtx v, rtx_insn* i)
    : value (v), mod_insn (i), auto_mod_mode (Pmode) { }

    find_reg_value_result (rtx v, rtx_insn* i, machine_mode m)
    : value (v), mod_insn (i), auto_mod_mode (m) { }
  };

  static find_reg_value_result find_reg_value (rtx reg, rtx_insn* insn);
  static std::pair<rtx, bool> find_reg_value_1 (rtx reg, rtx insn);

  static addr_expr
  extract_addr_expr (rtx x, rtx_insn* search_start_i, rtx_insn* last_access_i,
		     machine_mode mem_mach_mode, access_sequence* as,
		     std::vector<access*>& inserted_reg_mods,
                     bool apply_post_disp = false);

  static addr_expr
  extract_addr_expr (rtx x, rtx_insn* search_start_i, rtx_insn* last_access_i,
		     machine_mode mem_mach_mode, access_sequence* as)
  {
    std::vector<access*> inserted_reg_mods;
    return extract_addr_expr (x, search_start_i, last_access_i,
                              mem_mach_mode, as, inserted_reg_mods);
  }

  static addr_expr
  extract_addr_expr (rtx x, machine_mode mem_mach_mode = Pmode)
  {
    std::vector<access*> inserted_reg_mods;
    return extract_addr_expr (x, NULL, NULL, mem_mach_mode, NULL,
                              inserted_reg_mods, true);
  }

  static const pass_data default_pass_data;

  delegate& m_delegate;
  options m_options;
};

// ---------------------------------------------------------------------------

inline sh_ams::regno_t
sh_ams::get_regno (const_rtx x)
{
  if (x == NULL)
    return -1;
  if (x == any_regno)
    return -2;
  return REGNO (x);
}

inline sh_ams::addr_expr
sh_ams::make_reg_addr (rtx base_reg)
{
  return non_mod_addr (base_reg, invalid_regno, 0, 0, 0, 0, 0, 0);
}

inline sh_ams::addr_expr
sh_ams::make_disp_addr (disp_t disp_min, disp_t disp_max)
{
  return non_mod_addr (any_regno, invalid_regno, 0, 0, 0, 0, disp_min, disp_max);
}

inline sh_ams::addr_expr
sh_ams::make_disp_addr (rtx base_reg, disp_t disp_min, disp_t disp_max)
{
  return non_mod_addr (base_reg, invalid_regno, 0, 0, 0, 0, disp_min, disp_max);
}

inline sh_ams::addr_expr
sh_ams::make_const_addr (disp_t disp)
{
  return non_mod_addr (invalid_regno, invalid_regno, 0, 0, 0, disp, disp, disp);
}

inline sh_ams::addr_expr
sh_ams::make_const_addr (rtx disp)
{
  gcc_assert (CONST_INT_P (disp));
  return make_const_addr (INTVAL (disp));
}

inline sh_ams::addr_expr
sh_ams::make_index_addr (scale_t scale_min, scale_t scale_max)
{
  return non_mod_addr (any_regno, any_regno, 1, scale_min, scale_max, 0, 0, 0);
}

inline sh_ams::addr_expr
sh_ams::make_index_addr (void)
{
  return make_index_addr (1, 1);
}

inline sh_ams::addr_expr
sh_ams::make_post_inc_addr (machine_mode mode, rtx base_reg)
{
  const int mode_sz = GET_MODE_SIZE (mode);
  return post_mod_addr (base_reg, mode_sz, mode_sz, mode_sz);
}

inline sh_ams::addr_expr
sh_ams::make_post_dec_addr (machine_mode mode, rtx base_reg)
{
  const int mode_sz = -GET_MODE_SIZE (mode);
  return post_mod_addr (base_reg, mode_sz, mode_sz, mode_sz);
}

inline sh_ams::addr_expr
sh_ams::make_pre_inc_addr (machine_mode mode, rtx base_reg)
{
  const int mode_sz = GET_MODE_SIZE (mode);
  return pre_mod_addr (base_reg, mode_sz, mode_sz, mode_sz);
}

inline sh_ams::addr_expr
sh_ams::make_pre_dec_addr (machine_mode mode, rtx base_reg)
{
  const int mode_sz = -GET_MODE_SIZE (mode);
  return pre_mod_addr (base_reg, mode_sz, mode_sz, mode_sz);
}

inline sh_ams::addr_expr
sh_ams::make_invalid_addr (void)
{
  return make_disp_addr (-1, -2);
}

inline bool
sh_ams::addr_expr::operator == (const addr_expr& other) const
{
  return base_reg () == other.base_reg ()
	 && index_reg () == other.index_reg ()
	 && scale () == other.scale ()
	 && disp () == other.disp ();
}

inline std::pair<sh_ams::disp_t, bool>
sh_ams::addr_expr::operator - (const addr_expr& other) const
{
  if (base_reg () == other.base_reg ()
      && index_reg () == other.index_reg ()
      && (scale () == other.scale () || has_no_index_reg ()))
    return std::make_pair (disp () - other.disp (), true);

  return std::make_pair (0, false);
}

inline sh_ams::non_mod_addr
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

inline sh_ams::non_mod_addr
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

inline sh_ams::pre_mod_addr
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

inline sh_ams::pre_mod_addr
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

inline sh_ams::post_mod_addr
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

inline sh_ams::post_mod_addr
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

inline sh_ams::access::alternative_set::reference
sh_ams::access::alternative_set::at (size_type pos)
{
  gcc_assert (pos < size ());
  return m_data[pos];
}

inline sh_ams::access::alternative_set::const_reference
sh_ams::access::alternative_set::at (size_type pos) const
{
  gcc_assert (pos < size ());
  return m_data[pos];
}

inline void
sh_ams::access::alternative_set::push_back (const value_type& e)
{
  gcc_assert (size () < max_size ());
  m_data[m_size++] = e;
}

inline void
sh_ams::access::set_validate_alternatives (bool val)
{
  m_validate_alternatives = val;
}

inline bool
sh_ams::adjacent_inc (const access& first, const access& second)
{
  if (first.address ().is_invalid () || second.address ().is_invalid ())
    return false;

  // FIXME: This one checks for adjacent loads/stores only for now.
  // This will miss cases where reg uses are interleaved with loads/stores.
  std::pair<disp_t, bool> distance = second.address () - first.address ();
  return (first.access_type () == load || first.access_type () == store)
	 && distance.second && distance.first == first.access_size ();
}

inline bool
sh_ams::not_adjacent_inc (const access& first, const access& second)
{
  return !adjacent_inc (first, second);
}

inline bool
sh_ams::adjacent_dec (const access& first, const access& second)
{
  if (first.address ().is_invalid () || second.address ().is_invalid ())
    return false;

  // FIXME: This one checks for adjacent loads/stores only for now.
  // This will miss cases where reg uses are interleaved with loads/stores.
  std::pair<disp_t, bool> distance = first.address () - second.address ();
  return (first.access_type () == load || first.access_type () == store)
	 && distance.second && distance.first == first.access_size ();
}

inline bool
sh_ams::not_adjacent_dec (const access& first, const access& second)
{
  return !adjacent_dec (first, second);
}

#endif // includeguard_gcc_sh_ams_includeguard
