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
#include "trv_iterator.h"
#include "static_vector.h"
#include "ref_counted.h"
#include "tmp_rtx.h"

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

    // Simplify the sequences after optimization by removing unecessary
    // reg copies.  Default is false.
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

  struct delegate;


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

  class sequence_element;
  class sequence;
  class addr_expr;

 private:
  class mod_tracker;
  class mod_addr_result;
  class find_reg_value_result;
  class reg_copy;

 public:
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

  static bool
  regs_match (const rtx r1, const rtx r2)
  {
    if (r1 == invalid_regno || r2 == invalid_regno)
      return false;

    if (r1 == any_regno || r2 == any_regno)
      return true;

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
  enum addr_type_t { invalid_addr_expr, non_mod, pre_mod, post_mod };

  class addr_expr
  {
  public:
    struct is_valid_regno
    {
      bool operator () (const rtx x) const { return x != invalid_regno; }
    };

    typedef filter_iterator<rtx*, is_valid_regno> regs_iterator;
    typedef filter_iterator<const rtx*, is_valid_regno> regs_const_iterator;

    addr_expr (void)
    : m_type (invalid_addr_expr), m_base_index_reg (), m_disp (0),
      m_disp_min (0), m_disp_max (0), m_scale (0), m_scale_min (0),
      m_scale_max (0), m_cached_to_rtx (0)
    {
    }

    addr_type_t type (void) const { return m_type; }

    regs_const_iterator regs_begin (void) const
    {
      return regs_const_iterator (m_base_index_reg + (is_invalid () ? 2 : 0),
                                  m_base_index_reg + 2);
    }
    regs_iterator regs_begin (void)
    {
      return regs_iterator (m_base_index_reg + (is_invalid () ? 2 : 0),
                                  m_base_index_reg + 2);
    }
    regs_const_iterator regs_end (void) const
    {
      return regs_const_iterator (m_base_index_reg + 2, m_base_index_reg + 2);
    }
    regs_iterator regs_end (void)
    {
      return regs_iterator (m_base_index_reg + 2, m_base_index_reg + 2);
    }

    bool regs_empty (void) const { return regs_begin () == regs_end (); }

    rtx base_reg (void) const
    {
      gcc_assert (is_valid ());
      return m_base_index_reg[0];
    }

    bool has_base_reg (void) const
    {
      gcc_assert (is_valid ());
      return base_reg () != invalid_regno;
    }

    bool has_no_base_reg (void) const { return !has_base_reg (); }

    disp_t disp (void) const { return m_disp; }
    disp_t disp_min (void) const { return m_disp_min; }
    disp_t disp_max (void) const { return m_disp_max; }
    bool has_disp (void) const { return disp () != 0; }
    bool has_no_disp (void) const { return !has_disp (); }

    rtx index_reg (void) const
    {
      gcc_assert (is_valid ());
      return m_base_index_reg[1];
    }

    bool has_index_reg (void) const
    {
      gcc_assert (is_valid ());
      return index_reg () != invalid_regno;
    }

    bool has_no_index_reg (void) const { return !has_index_reg (); }

    scale_t scale (void) const { return m_scale; }
    scale_t scale_min (void) const { return m_scale_min; }
    scale_t scale_max (void) const { return m_scale_max; }

    // Get all sub-expressions that are contained inside the addr_expr.
    template <typename OutputIterator> void
    get_all_subterms (OutputIterator out) const;

    bool operator == (const addr_expr& other) const;
    bool operator != (const addr_expr& other) const;
    bool operator < (const addr_expr& other) const;

    std::pair<disp_t, bool> operator - (const addr_expr& other) const;

    // tells if this address expression is valid or not.
    bool is_invalid (void) const { return type () == invalid_addr_expr; }
    bool is_valid (void) const { return !is_invalid (); }

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

    // Get all sub-expressions that are contained inside the addr_expr.
    // For an addr_expr of the form base+index*scale+disp, the following
    // sub-expressions are returned:
    //
    // nothing -> represented with an invalid address
    // base
    // index
    // index*scale
    // base+index*scale
    // disp
    // base+disp
    // index*scale+disp
    // base+index*scale+disp
    template <typename OutputIterator> void
    get_subterms (OutputIterator out) const;

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
        return a < b;
      }
    };

  protected:
    addr_type_t m_type;

    // FIXME: on some architectures constant addresses can be used directly.
    // in such cases, after the constant pool layout has been determined,
    // the value of the base register will be e.g. a constant label_ref.
    // currently we can't deal with those.

    rtx m_base_index_reg[2];
    disp_t m_disp;
    disp_t m_disp_min;
    disp_t m_disp_max;
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

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // An alternative for an address mode.  These are usually provided
  // to AMS by the delegate for each memory access in an (access) sequence.
  class alternative
  {
  public:
    alternative (void) : m_valid (false) { }

    alternative (int cost, const addr_expr& ae)
    : m_valid (true), m_cost (cost), m_addr_expr (ae) { }

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

  struct alternative_valid;
  struct alternative_invalid;

  // Support a limited number of alternatives only.
  typedef static_vector<alternative, 16> alternative_set;

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // A sequence element's adjacency information.
  // Probably only useful for mem access elements and reg-uses.
  class adjacent_chain_info
  {
  public:
    adjacent_chain_info (void)
      : m_pos (0), m_len (1), m_first_el (NULL), m_last_el (NULL) { }
    adjacent_chain_info (int p, int l, const sequence_element* fe,
                         const sequence_element* le)
      : m_pos (p), m_len (l), m_first_el (fe), m_last_el (le) { }

    int pos (void) const { return m_pos; }
    int length (void) const { return m_len; }

    bool is_first (void) const { return m_pos == 0; }
    bool is_last (void) const { return m_pos == m_len - 1; }

    const sequence_element* first (void) const { return m_first_el; }
    const sequence_element* last (void) const { return m_last_el; }

  private:
    int m_pos;
    int m_len;
    const sequence_element* m_first_el;
    const sequence_element* m_last_el;
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
  class mem_access;
  class mem_load;
  class mem_store;
  class mem_operand;
  class reg_mod;
  class reg_barrier;
  class reg_use;

  typedef std::map<rtx, unsigned, cmp_by_regno> addr_reg_map;

  // A structure used to store the address regs that can be used as a starting
  // point to arrive at another address during address mod generation.
  class start_addr_list
  {
  public:

    typedef std::list<reg_mod*>::iterator iterator;
    typedef std::multimap<rtx, reg_mod*, cmp_by_regno> reg_map;
    template <typename OutputIterator> void
    get_relevant_addresses (const addr_expr& end_addr, OutputIterator out);

    void add (reg_mod* start_addr);
    void remove (reg_mod* start_addr);

  private:

    // List of addresses that only have a constant displacement.
    std::list<reg_mod*> m_const_addresses;

    // A map for storing addresses that have a base and/or index reg.
    // The key of each stored address is its base or index reg (the
    // address is stored twice if it has both).
    reg_map m_reg_addresses;
  };

  template <element_type T1, element_type T2 = T1, element_type T3 = T1>
  struct element_type_matches
  {
    bool operator () (const sequence_element& e) const
    {
      return e.type () == T1 || e.type () == T2 || e.type () == T3;
    }
  };

  struct element_to_optimize;


  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // The access sequence that contains the memory accesses of some part of
  // the code (usually a basic block), along with other relevant information
  // (reg uses, reg mods, etc.).
  class sequence_element;

  class sequence
  {
  public:
    typedef trv_iterator<deref<std::list<ref_counting_ptr<sequence_element> >
			       ::iterator> > iterator;

    typedef trv_iterator<deref<std::list<ref_counting_ptr<sequence_element> >
			       ::const_iterator> > const_iterator;

    typedef trv_iterator<deref<std::list<ref_counting_ptr<sequence_element> >
			       ::reverse_iterator> > reverse_iterator;

    typedef trv_iterator<deref<std::list<ref_counting_ptr<sequence_element> >
			       ::const_reverse_iterator> > const_reverse_iterator;


    typedef std::multimap<rtx_insn*, iterator> insn_map;
    typedef std::multimap<rtx_insn*, sequence_element*> glob_insn_map;

    // Split the access sequence pointed to by SEQ into multiple sequences,
    // grouping the accesses that have common terms in their effective address
    // together.  Return an iterator to the sequence that comes after the newly
    // inserted sequences.
    static std::list<sequence>::iterator
    split (std::list<sequence>::iterator seq_it,
           std::list<sequence>& sequences);

    sequence (glob_insn_map& m, unsigned* i): m_glob_insn_el_map (m),
      m_next_id (i)
    {
    }

    ~sequence (void);

    // A reference to the global insn->element map.
    glob_insn_map& g_insn_el_map (void) const { return m_glob_insn_el_map; }

    // A reference to the the ID of the next element that gets inserted.
    unsigned* next_id (void) const { return m_next_id; }

    // Find all mem accesses in the insn I and add them to the sequence.
    void find_mem_accesses (rtx_insn* i);

    // Add a reg mod for every insn that modifies an address register.
    void find_addr_reg_mods (void);

    // Add a reg use for every use of an address register that's not a
    // memory access
    void find_addr_reg_uses (void);

    // Generate the address modifications needed to arrive at the
    // addresses in the sequence.
    void gen_address_mod (delegate& dlg, int base_lookahead);

    // Try to eliminate unnecessary reg -> reg copies.
    void eliminate_reg_copies (void);

    // Update the original insn stream with the changes in this sequence.
    void update_insn_stream (void);

    // Fill the m_inc/dec_chain fields of the sequence elements.
    void calculate_adjacency_info (void);

    // Check whether REG is used in any element after START.
    bool reg_used_in_sequence (rtx reg, const_iterator start) const;

    // Check whether REG is used in any of the sequence's accesses.
    bool
    reg_used_in_sequence (rtx reg) const
    {
      return reg_used_in_sequence (reg, begin ());
    }

    // The total cost of the accesses in the sequence.
    int cost (void) const;

    // Re-calculate the cost.
    void update_cost (delegate& d);

    // Check whether the cost of the sequence is already minimal and
    // can't be improved further.
    bool cost_already_minimal (void) const;

    // Update the alternatives of the sequence's accesses.
    void update_access_alternatives (delegate& d, bool force_validation,
                                     bool disable_validation,
                                     bool adjust_costs = false);

    // Insert a new element into the sequence.  Return an iterator pointing
    // to the newly inserted element.
    iterator insert_element (const ref_counting_ptr<sequence_element>& el,
			     iterator insert_before);

    // If the EL is unique, insert it into the sequence and return an iterator
    // pointing to it.  If it already has a duplicate in the sequence, don't
    // insert it and return an iterator to the already inserted duplicate
    // instead.
    // The place of the element is determined by its insn.
    iterator insert_unique (const ref_counting_ptr<sequence_element>& el);

    // Remove an element from the sequence.  Return an iterator pointing
    // to the next element.
    iterator remove_element (iterator el, bool clear_deps = true);

    // Find the value that REG was last set to, starting the search from
    // START_INSN.
    find_reg_value_result find_reg_value (rtx reg, rtx_insn* start_insn);

    // The first insn and basic block in the sequence.
    const_iterator start_insn_element (void) const;

    rtx_insn* start_insn (void) const;
    basic_block start_bb (void) const;

    // A map containing all the address regs used in the sequence
    // and the number of elements that use them.
    addr_reg_map& addr_regs (void) { return m_addr_regs; }

    // Return the sequence elements that INSN contains.
    std::pair<insn_map::iterator, insn_map::iterator>
    elements_in_insn (rtx_insn* insn) { return m_insn_el_map.equal_range (insn); }

    // A structure for retrieving the starting addresses that could be
    // used to arrive at a given destination address.
    start_addr_list& start_addresses (void)  { return m_start_addr_list; }

    bool empty (void) const { return m_els.empty (); }
    size_t size (void) const { return m_els.size (); }

    iterator begin (void) { return iterator (m_els.begin ()); }
    iterator end (void) { return iterator (m_els.end ()); }

    const_iterator begin (void) const { return const_iterator (m_els.begin ()); }
    const_iterator end (void) const { return const_iterator (m_els.end ()); }

    reverse_iterator rbegin (void) { return reverse_iterator (m_els.rbegin ()); }
    reverse_iterator rend (void) { return reverse_iterator (m_els.rend ()); }

    const_reverse_iterator rbegin (void) const { return const_reverse_iterator (m_els.rbegin ()); }
    const_reverse_iterator rend (void) const { return const_reverse_iterator (m_els.rend ()); }

    // iterator decorator for iterating over different types of elements
    // in the access sequence.
    template <typename Match>
    filter_iterator<iterator, Match> begin (void)
    {
      typedef filter_iterator<iterator, Match> iter;
      return iter (begin (), end ());
    }

    template <typename Match>
    filter_iterator<iterator, Match> end (void)
    {
      typedef filter_iterator<iterator, Match> iter;
      return iter (end (), end ());
    }

    template <typename Match>
    filter_iterator<const_iterator, Match> begin (void) const
    {
      typedef filter_iterator<const_iterator, Match> iter;
      return iter (begin (), end ());
    }

    template <typename Match>
    filter_iterator<const_iterator, Match> end (void) const
    {
      typedef filter_iterator<const_iterator, Match> iter;
      return iter (end (), end ());
    }

  private:
    static int split_1 (sequence& seq,
                        const ref_counting_ptr<sequence_element>& el);

    static bool sort_found_mems (const std::pair<rtx*, element_type>& a,
                                 const std::pair<rtx*, element_type>& b);

    int gen_address_mod_1 (filter_iterator<iterator, element_to_optimize> el,
                           delegate& dlg,
                           std::set<reg_mod*>& used_reg_mods,
                           std::map<rtx, reg_mod*, cmp_by_regno>&
                             visited_reg_mods, unsigned* next_tmp_regno,
                           int lookahead_num, bool record_in_sequence = true);

    std::pair<int, reg_mod*>
    find_cheapest_start_addr (const addr_expr& end_addr,
                              iterator el, rtx addr_reg,
                              disp_t min_disp, disp_t max_disp,
                              addr_type_t addr_type,
                              delegate& dlg, std::set<reg_mod*>& used_reg_mods,
                              std::map<rtx, reg_mod*, cmp_by_regno>&
                                visited_reg_mods, unsigned* next_tmp_regno);

    void insert_address_mods (alternative_set::const_iterator alt,
                              reg_mod* base_start_addr,
                              reg_mod* index_start_addr,
                              const addr_expr& base_end_addr,
                              const addr_expr& index_end_addr,
                              iterator el, mod_tracker& tracker,
                              std::set<reg_mod*>& used_reg_mods,
                              std::map<rtx, reg_mod*, cmp_by_regno>&
                                visited_reg_mods,
                              delegate& dlg, unsigned* next_tmp_regno);

    mod_addr_result
    try_insert_address_mods (reg_mod* start_addr, const addr_expr& end_addr,
                             disp_t min_disp, disp_t max_disp,
                             addr_type_t addr_type, machine_mode acc_mode,
                             iterator el, mod_tracker& tracker,
                             std::set<reg_mod*>& used_reg_mods,
                             std::map<rtx, reg_mod*, cmp_by_regno>&
                               visited_reg_mods,
                             delegate& dlg, unsigned* next_tmp_regno);

    reg_mod*
    insert_addr_mod (reg_mod* used_rm, machine_mode acc_mode,
                     rtx curr_addr_rtx, const addr_expr& curr_addr,
                     const addr_expr& effective_addr,
                     iterator el, mod_tracker& tracker,
                     std::set<reg_mod*>& used_reg_mods,
                     delegate& dlg, unsigned* next_tmp_regno);

    reg_mod* find_start_addr_for_reg (
      rtx reg, std::set<reg_mod*>& used_reg_mods,
      std::map<rtx, reg_mod*, cmp_by_regno>& visited_reg_mods);

    std::pair<rtx, bool> find_reg_value_1 (rtx reg, const_rtx insn);
    template <typename OutputIterator> void
    find_addr_reg_uses_1 (rtx reg, rtx& x, OutputIterator out,
                          bool check_every_rtx = false);

    template <typename OutputIterator> void
    find_mem_accesses_1 (rtx& x, OutputIterator out,
                         element_type type = type_mem_load);

    // FIXME: m_els is the primary container for the sequence_elements.
    // use std::auto_ptr for that instead of raw pointers.  actually it should
    // be std::unique_ptr, but we don't have that (yet).  std::auto_ptr is OK
    // with node based containers like std::list.
    // when transferring auto_ptr'ed sequence elements from one sequence list
    // to another, use std::list::splice to move elements without having to
    // copy auto_ptr.
    // if multiple sequence lists need to share the same sequence_element,
    // need to use ref_counted_ptr (or std::tr1::shared_ptr).
    std::list<ref_counting_ptr<sequence_element> > m_els;
    addr_reg_map m_addr_regs;
    insn_map m_insn_el_map;

    glob_insn_map& m_glob_insn_el_map;
    unsigned* m_next_id;
    start_addr_list m_start_addr_list;

  };

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // Base class of an (access) sequence element.

  class sequence_element : public ref_counted
  {
  public:
    static const unsigned invalid_id;

    virtual ~sequence_element (void)
      {
        m_sequences.clear ();
      }

    struct equals
    {
      const sequence_element* e;

      equals (const sequence_element* se) : e (se) { }
      equals (const sequence_element& se) : e (&se) { }

      // assume that T is some kind of pointer or iterator to sequence_element
      // that can be dereferenced.
      template <typename T> bool operator () (const T& a) { return *a == *e; }
    };

    virtual bool operator == (const sequence_element& other) const
    {
      return type () == other.type () && insn () == other.insn ();
    }

    // Returns the type of the element.  Could also use RTTI for this.
    element_type type (void) const { return m_type; }

    bool is_mem_access (void) const
    {
      return m_type == type_mem_load || m_type == type_mem_store
        || m_type == type_mem_operand;
    }

    // A unique ID used to order the elements in containers like std::set.
    unsigned id (void) const { return m_id; }
    void set_id (unsigned new_id) { m_id = new_id; }

    // The cost of this element in the sequence.
    int cost (void) const { return m_cost; }
    void set_cost (int new_cost) { m_cost = new_cost; }
    void adjust_cost (int d) { m_cost += d; }
    virtual void
    update_cost (delegate& d ATTRIBUTE_UNUSED, sequence& seq ATTRIBUTE_UNUSED,
                 sequence::iterator el_it ATTRIBUTE_UNUSED) { }
    virtual void
    add_cloning_cost (rtx reused_reg, delegate& d, sequence& seq,
                      sequence::iterator el_it);

    // The insn rtx of this element.  Maybe null if it has been inserted
    // by AMS into the sequence and is not present in the original insn list.
    rtx_insn* insn (void) const { return m_insn; }
    void set_insn (rtx_insn* i) { m_insn = i; }

    // The address expression that is currently being used.
    // Might be invalid if AMS was not able to understand it.
    const addr_expr& current_addr (void) const { return m_current_addr; }
    void set_current_addr (const addr_expr& addr) { m_current_addr = addr; }

    // The effective address expression.
    // Might be invalid if AMS was not able to understand it.
    const addr_expr& effective_addr (void) const { return m_effective_addr; }
    void set_effective_addr (const addr_expr& addr) { m_effective_addr = addr; }

    // If false, AMS skips this element when optimizing.
    bool optimization_enabled (void) const { return m_optimization_enabled; }
    void set_optimization_enabled (void) { m_optimization_enabled = true; }
    void set_optimization_disabled (void) { m_optimization_enabled = false; }

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

    // List of all the immediate dependencies for this element in both
    // directions. E.g. if a reg-mod is required by a mem access, the reg-mod
    // will be listed in the mem's dependencies and the mem will be listed in
    // the reg-mod's dependent elements.
    // Another case are reg-mods that require the result of other reg-mods.

/*
NOTE:
    specify the max number of predecessor BBs to visit when trying to trace
    back defs.  if the limit is exceeded a reg_barrier should be placed in
    the BB where the limit was exceeded.
*/
    struct compare;
    typedef std::set<sequence_element*, compare>
      dependency_list;

    const dependency_list&
    dependencies (void) const { return m_dependencies; }

    dependency_list&
    dependencies (void) { return m_dependencies; }

    const dependency_list&
    dependent_els (void) const { return m_dependent_els; }

    dependency_list&
    dependent_els (void) { return m_dependent_els; }

    void add_dependency (sequence_element* dep)
    {
      m_dependencies.insert (dep);
    }
    void remove_dependency (sequence_element* dep)
    {
      m_dependencies.erase (dep);
    }
    void add_dependent_el (sequence_element* dep)
    {
      m_dependent_els.insert (dep);
    }
    void remove_dependent_el (sequence_element* dep)
    {
      m_dependent_els.erase (dep);
    }

    // The sequences that use or have previously used this element.
    std::set<sequence*>& sequences (void) { return m_sequences; }

    // Return true if the element can be removed or changed by an optimization
    // subpass.
    virtual bool can_be_optimized (void) const;

    // Return true if the effective address of FIRST and SECOND only differs in
    // the constant displacement and the difference is DIFF.
    static bool distance_equals (
      const sequence_element& first,
      const sequence_element& second,
      disp_t diff);

    // Return true if the effective address of FIRST and SECOND only differs in
    // the constant displacement and the difference is the access size of FIRST.
    static bool adjacent_inc (
      const sequence_element& first,
      const sequence_element& second);
    static bool not_adjacent_inc (
      const sequence_element& first,
      const sequence_element& second);

    // Same as adjacent_inc, except that the displacement of SECOND should
    // be the smaller one.
    static bool adjacent_dec (
      const sequence_element& first,
      const sequence_element& second);
    static bool not_adjacent_dec (
      const sequence_element& first,
      const sequence_element& second);

    // Update the insn that holds this element or generate a new insn
    // that corresponds to this element.  INSN_SEQUENCE_STARTED indicates
    // whether we're in the middle of an insn sequence.
    // Return the updated value of INSN_SEQUENCE_STARTED.
    virtual bool generate_new_insns (bool insn_sequence_started)
    {
      return insn_sequence_started;
    }

    // Comparison struct for sets and maps containing sequence elements.
    struct compare
    {
      bool operator () (const sequence_element* a,
                        const sequence_element* b) const
      {
        return a->id () < b->id ();
      }
    };

  protected:
    sequence_element (element_type t, rtx_insn* i,
		      const addr_expr& ca = addr_expr (),
                      const addr_expr& ea = addr_expr ())
    : m_type (t), m_id (invalid_id), m_cost (0), m_insn (i),
      m_current_addr (ca), m_effective_addr (ea), m_optimization_enabled (true)
    {
    }

  private:
    static const adjacent_chain_info g_no_incdec_chain;

    // Changing the type after construction is not supported.
    const element_type m_type;

    unsigned m_id;
    int m_cost;
    rtx_insn* m_insn;
    addr_expr m_current_addr, m_effective_addr;
    bool m_optimization_enabled;

    dependency_list m_dependencies;
    dependency_list m_dependent_els;

    std::set<sequence*> m_sequences;
  };

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // Base class for a memory access element.
  class mem_access : public sequence_element
  {
  public:
    virtual ~mem_access (void) { }

    virtual bool operator == (const sequence_element& other) const;

    static bool allow_new_insns;

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

    void update_access_alternatives (const sequence& seq,
                                     sequence::const_iterator it,
                                     delegate& d, bool force_validation,
				     bool disable_validation);

    // FIXME: find shorter name.
    bool alternative_validation_enabled (void) const { return m_validate_alts; }
    void set_alternative_validation (bool val) { m_validate_alts = val; }

    bool matches_alternative (const alternative& alt) const;

    // Check if DISP can be used as constant displacement in any of the address
    // alternatives of the access.
    bool displacement_fits_alternative (disp_t disp) const;

    // The address alternative that is currently being used.
    const alternative_set::const_iterator& current_alt (void) const
    {
      return m_current_alt;
    }

    void set_current_addr_and_alt (const addr_expr& addr,
                                   alternative_set::const_iterator alt)
    {
      sequence_element::set_current_addr (addr);
      m_current_alt = alt;
    }

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

    // The address expression rtx as it is currently being used in the mem
    // rtx in the insn.
    rtx current_addr_rtx (void) const { return m_current_addr_rtx; }
    void set_current_addr_rtx (const rtx x) { m_current_addr_rtx = x; }

    machine_mode mach_mode (void) const { return m_machine_mode; }
    void set_mach_mode (machine_mode m) { m_machine_mode = m; }
    int access_size (void) const { return GET_MODE_SIZE (m_machine_mode); }

    virtual void update_cost (delegate& d, sequence& seq,
                              sequence::iterator el_it);
    virtual bool generate_new_insns (bool insn_sequence_started);

  protected:
    mem_access (element_type t, rtx_insn* i, machine_mode m,
                const addr_expr& addr, rtx addr_rtx)
    : sequence_element (t, i, addr),
      m_current_addr_rtx (addr_rtx), m_current_alt (m_alternatives.end ()),
      m_machine_mode (m)
    {
    }

    mem_access (element_type t, rtx_insn* i)
    : sequence_element (t, i), m_current_addr_rtx (NULL),
      m_current_alt (m_alternatives.end ()), m_machine_mode (Pmode)
    {
    }

    // The current address expressions are usually set/updated by the sub-class.
    rtx m_current_addr_rtx;

  private:
    bool m_validate_alts;
    alternative_set m_alternatives;
    alternative_set::const_iterator m_current_alt;
    adjacent_chain_info m_inc_chain;
    adjacent_chain_info m_dec_chain;
    machine_mode m_machine_mode;
  };

  typedef element_type_matches<type_mem_load, type_mem_store,
			       type_mem_operand> mem_match;

  typedef trv_iterator<cast <
	    filter_iterator<sequence::iterator, mem_match>,
	    mem_access> > mem_acc_iter;

  typedef trv_iterator<cast <
	    filter_iterator<sequence::const_iterator, mem_match>,
	    mem_access> > mem_acc_const_iter;

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // A memory load -- an insn with only one mem rtx.
  class mem_load : public mem_access
  {
  public:
    mem_load (rtx_insn* i, machine_mode m, rtx* mem_ref,
              const addr_expr& addr, rtx addr_rtx)
    : mem_access (type_mem_load, i, m, addr, addr_rtx), m_mem_ref (mem_ref)
    {
    };

    mem_load (rtx_insn* i, rtx* mem_ref)
    : mem_access (type_mem_load, i), m_mem_ref (mem_ref)
    {
    };

    virtual bool try_replace_addr (const addr_expr& new_addr);
    virtual bool replace_addr (const addr_expr& new_addr);

    rtx* mem_ref (void) const { return m_mem_ref; }

  private:
    // Reference into the rtx_insn where the mem rtx resides.
    rtx* m_mem_ref;
  };

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // A memory store -- an insn with only one mem rtx.
  class mem_store : public mem_access
  {
  public:
    mem_store (rtx_insn* i, machine_mode m, rtx* mem_ref,
               const addr_expr& addr, rtx addr_rtx)
    : mem_access (type_mem_store, i, m, addr, addr_rtx), m_mem_ref (mem_ref)
    {
    };

    mem_store (rtx_insn* i, rtx* mem_ref)
    : mem_access (type_mem_store, i), m_mem_ref (mem_ref)
    {
    };

    virtual bool try_replace_addr (const addr_expr& new_addr);
    virtual bool replace_addr (const addr_expr& new_addr);

    rtx* mem_ref (void) const { return m_mem_ref; }

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
    mem_operand (rtx_insn* i, machine_mode m,
                 const static_vector<rtx*, 16>& mem_refs,
                 const addr_expr& addr, rtx addr_rtx)
    : mem_access (type_mem_operand, i, m, addr, addr_rtx), m_mem_refs (mem_refs)
    {
    };

    mem_operand (rtx_insn* i, const static_vector<rtx*, 16>& mem_refs)
    : mem_access (type_mem_operand, i), m_mem_refs (mem_refs)
    {
    };

    virtual bool try_replace_addr (const addr_expr& new_addr);
    virtual bool replace_addr (const addr_expr& new_addr);

  private:
    // References into the rtx_insn where the mem rtx'es reside.
    static_vector<rtx*, 16> m_mem_refs;
  };

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // An address reg modification.
  // Usually this will be an insn that sets the reg to some other rtx.
  // It could also be a side-effect of an auto-inc or auto-mod mem access.
  class reg_mod : public sequence_element
  {
  public:
    reg_mod (rtx_insn* i, rtx r, rtx v, const addr_expr& a = addr_expr (),
	     const addr_expr& ea = addr_expr (), mem_access* ma = NULL)
      : sequence_element (type_reg_mod, i, a, ea), m_tmp_reg (Pmode, ~0u),
      m_reg (r), m_value (v), m_auto_mod_acc (ma)
    {
    }

    reg_mod (rtx_insn* i, unsigned tmp_regno, machine_mode tmp_mode, rtx v,
             const addr_expr& a = addr_expr (),
	     const addr_expr& ea = addr_expr (), mem_access* ma = NULL)
      : sequence_element (type_reg_mod, i, a, ea), m_tmp_reg (tmp_mode, tmp_regno),
      m_reg (m_tmp_reg), m_value (v), m_auto_mod_acc (ma)
    {
    }

    virtual bool operator == (const sequence_element& other) const;
    virtual bool can_be_optimized (void) const;

    // A temporary reg RTX that isn't garbage-collected. Used for storing
    // the address reg of reg-mods that only exist temporarily (e.g. during
    // address mod generation).
    const tmp_rtx<REG>& tmp_reg (void) const { return m_tmp_reg; }

    // The address reg that is being modified / defined.
    rtx reg (void) const { return m_reg; }
    void set_reg (const rtx reg) { m_reg = reg; }

    // The rtx the reg is being set to.
    rtx value (void) const { return m_value; }

    // The mem_access for reg-mods that are caused by auto-mod accesses.
    mem_access* auto_mod_acc (void) const { return m_auto_mod_acc; }
    void set_auto_mod_acc (mem_access* a)  { m_auto_mod_acc = a; }


    virtual void update_cost (delegate& d, sequence& seq,
                              sequence::iterator el_it);
    virtual bool generate_new_insns (bool insn_sequence_started);

  private:
    tmp_rtx<REG> m_tmp_reg;
    rtx m_reg;
    rtx m_value;
    mem_access* m_auto_mod_acc;
  };

  typedef element_type_matches<type_reg_mod> reg_mod_match;

  typedef trv_iterator<cast <
	    filter_iterator<sequence::iterator, reg_mod_match>,
	    reg_mod> > reg_mod_iter;

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // A barrier for AMS which is inserted during dependency/def analysis
  // if AMS doesn't understand the value/calculation of some address register.
  // This barrier can't be removed by AMS.
  class reg_barrier : public sequence_element
  {
  public:
    reg_barrier (rtx_insn* i) : sequence_element (type_reg_barrier, i) { };

    virtual bool operator == (const sequence_element& other) const;

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
    reg_use (rtx_insn* i, rtx reg)
    : sequence_element (type_reg_use, i), m_reg (reg), m_reg_ref (NULL)
    {
    }

    reg_use (rtx_insn* i, rtx reg, rtx* ref, const addr_expr& a,
             const addr_expr& ea = addr_expr ())
    : sequence_element (type_reg_use, i, a, ea), m_reg (reg), m_reg_ref (ref)
    {
    }

    virtual bool operator == (const sequence_element& other) const;

    virtual const adjacent_chain_info&
    inc_chain (void) const { return m_inc_chain; }

    virtual const adjacent_chain_info&
    dec_chain (void) const { return m_dec_chain; }

    virtual void
    set_inc_chain (const adjacent_chain_info& c) { m_inc_chain = c; }

    virtual void
    set_dec_chain (const adjacent_chain_info& c) { m_dec_chain = c; }

    // The reg that is being used.
    rtx reg (void) const { return m_reg; }
    void set_reg (const rtx reg) { m_reg = reg; }

    // The reg rtx inside the insn. Can also be a (PLUS reg const_int)
    // expression. If NULL, the reg use is unspecified.
    const rtx* reg_ref (void) const { return m_reg_ref; }
    bool set_reg_ref (rtx new_reg);

    virtual void update_cost (delegate& d, sequence& seq,
                              sequence::iterator el_it);

    virtual bool generate_new_insns (bool insn_sequence_started);

  private:
    // if a mem access is not to be optimized, it is converted into a
    // reg-use.  in this case maybe it's useful to keep the original element
    // around.  the original element could also be a reg_mod, in case it's
    // an insn that AMS understands.  in this case AMS can optimize it away.
    // ref_counted_ptr<sequence_element> m_original;

    rtx m_reg;
    rtx* m_reg_ref;

    adjacent_chain_info m_inc_chain;
    adjacent_chain_info m_dec_chain;
  };

  typedef element_type_matches<type_reg_use> reg_use_match;

  typedef trv_iterator<cast <
	    filter_iterator<sequence::iterator, reg_use_match>,
	    reg_use> > reg_use_iter;

  // a delegate for the ams pass.  usually implemented by the target.
  struct delegate
  {
    // provide alternatives for the specified access.
    virtual void
    mem_access_alternatives (alternative_set& alt,
			     const sequence& seq,
			     sequence::const_iterator acc,
			     bool& validate_alternatives) = 0;

    // adjust the costs of the specified alternative of the specified
    // access.  called after the alternatives of all accesses have
    // been retrieved.
    virtual void
    adjust_alternative_costs (alternative& alt,
			      const sequence& seq,
                              sequence::const_iterator acc) = 0;

    // provide the number of subsequent accesses that should be taken into
    // account when trying to minimize the costs of the specified access.
    virtual int
    adjust_lookahead_count (const sequence& as,
			    sequence::const_iterator acc) = 0;

    // provide the cost for setting the specified address register to
    // an rtx expression.
    // the cost must be somehow relative to the cost provided for access
    // alternatives.
    // the cost of cloning regs should be ignored because it's calculated
    // separately using the addr_reg_clone_cost function.
    virtual int
    addr_reg_mod_cost (const_rtx reg, const_rtx val,
		       const sequence& seq,
		       sequence::const_iterator acc) = 0;

    // provide the cost for cloning the address register, which is usually
    // required when splitting an access sequence.  if (address) register
    // pressure is high, return a higher cost to avoid splitting.
    //
    // FIXME: alternative would be 'sequence_split_cost'
    virtual int
    addr_reg_clone_cost (const_rtx reg,
			 const sequence& seq,
			 sequence::const_iterator acc) = 0;
  };

  // Used to keep track of shared address (sub)expressions
  // during access sequence splitting.
  class shared_term;

  sh_ams2 (gcc::context* ctx, const char* name, delegate& dlg,
	  const options& opt = options ());

  virtual ~sh_ams2 (void);
  virtual bool gate (function* fun);
  virtual unsigned int execute (function* fun);

  // Extract an addr_expr of the form (base_reg + index_reg * scale + disp)
  // from the rtx X.
  // If SEQ and EL is not null, trace back the effective addresses of the
  // registers in X (starting from EL) and insert a reg mod into the sequence
  // for every address modifying insn that was used.
  static addr_expr rtx_to_addr_expr (rtx x, machine_mode mem_mode,
				     sequence* seq, sequence_element& el)
  {
    return rtx_to_addr_expr (x, mem_mode, seq, &el);
  }

  static addr_expr rtx_to_addr_expr (rtx x, machine_mode mem_mach_mode,
                                     sequence* seq, sequence_element* el);

  static addr_expr rtx_to_addr_expr (rtx x, machine_mode mem_mach_mode)
  {
    return rtx_to_addr_expr(x, mem_mach_mode, NULL, NULL);
  }

  static addr_expr rtx_to_addr_expr (rtx x)
  {
    return rtx_to_addr_expr(x, Pmode, NULL, NULL);
  }

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

inline bool
sh_ams2::addr_expr::operator == (const addr_expr& other) const
{
  if (is_invalid () || other.is_invalid ())
    return is_invalid () && other.is_invalid ();

  return regs_equal (base_reg (), other.base_reg ())
         && regs_equal (index_reg (), other.index_reg ())
         && scale () == other.scale ()
         && disp () == other.disp ();
}

inline bool
sh_ams2::addr_expr::operator != (const addr_expr& other) const
{
  return !addr_expr::operator == (other);
}

inline bool
sh_ams2::addr_expr::operator < (const addr_expr& other) const
{
  if (is_invalid () && other.is_invalid ())
    return false;
  if (is_invalid () || other.is_invalid ())
    return is_invalid ();

  regno_t br0 = get_regno (base_reg ()), br1 = get_regno (other.base_reg ());
  if (br0 != br1)
    return br0 > br1;

  regno_t ir0 = get_regno (index_reg ()), ir1 = get_regno (other.index_reg ());
  if (ir0 != ir1)
    return ir0 > ir1;

  if (has_index_reg () && other.has_index_reg ())
    {
      scale_t s0 = scale (), s1 = other.scale ();
      if (s0 != s1)
        return s0 > s1;
    }

  return disp () > other.disp ();
}

inline std::pair<sh_ams2::disp_t, bool>
sh_ams2::addr_expr::operator - (const addr_expr& other) const
{
  if (regs_equal (base_reg (), other.base_reg ())
      && regs_equal (index_reg (), other.index_reg ())
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
  m_base_index_reg[0] = base_reg;
  m_disp = disp;
  m_disp_min = disp_min;
  m_disp_max = disp_max;
  m_base_index_reg[1] = index_reg;
  m_scale = scale;
  if (m_scale == 0)
    m_base_index_reg[1] = invalid_regno;
  m_scale_min = scale_min;
  m_scale_max = scale_max;
}

inline sh_ams2::non_mod_addr
::non_mod_addr (rtx base_reg, rtx index_reg, scale_t scale, disp_t disp)
{
  m_type = non_mod;
  m_base_index_reg[0] = base_reg;
  m_disp = disp;
  m_disp_min = disp;
  m_disp_max = disp;
  m_base_index_reg[1] = index_reg;
  m_scale = scale;
  if (m_scale == 0)
    m_base_index_reg[1] = invalid_regno;
  m_scale_min = scale;
  m_scale_max = scale;
}

inline sh_ams2::pre_mod_addr
::pre_mod_addr (rtx base_reg, disp_t disp, disp_t disp_min, disp_t disp_max)
{
  m_type = pre_mod;
  m_base_index_reg[0] = base_reg;
  m_disp = disp;
  m_disp_min = disp_min;
  m_disp_max = disp_max;
  m_base_index_reg[1] = invalid_regno;
  m_scale = m_scale_min = m_scale_max = 0;
}

inline sh_ams2::pre_mod_addr
::pre_mod_addr (rtx base_reg, disp_t disp)
{
  m_type = pre_mod;
  m_base_index_reg[0] = base_reg;
  m_disp = disp;
  m_disp_min = disp;
  m_disp_max = disp;
  m_base_index_reg[1] = invalid_regno;
  m_scale = m_scale_min = m_scale_max = 0;
}

inline sh_ams2::post_mod_addr
::post_mod_addr (rtx base_reg, disp_t disp, disp_t disp_min, disp_t disp_max)
{
  m_type = post_mod;
  m_base_index_reg[0] = base_reg;
  m_disp = disp;
  m_disp_min = disp_min;
  m_disp_max = disp_max;
  m_base_index_reg[1] = invalid_regno;
  m_scale = m_scale_min = m_scale_max = 0;
}

inline sh_ams2::post_mod_addr
::post_mod_addr (rtx base_reg, disp_t disp)
{
  m_type = post_mod;
  m_base_index_reg[0] = base_reg;
  m_disp = disp;
  m_disp_min = disp;
  m_disp_max = disp;
  m_base_index_reg[1] = invalid_regno;
  m_scale = m_scale_min = m_scale_max = 0;
}

#endif // includeguard_gcc_sh_ams2_includeguard
