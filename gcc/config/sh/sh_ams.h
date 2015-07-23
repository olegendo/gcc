
#ifndef includeguard_gcc_sh_ams_includeguard
#define includeguard_gcc_sh_ams_includeguard

#include "tree-pass.h"
#include <limits>
#include <list>
#include <vector>
#include <functional>
#include <map>

class sh_ams : public rtl_opt_pass
{
public:

  // the most complex non modifying address is of the form
  // 'base_reg + index_reg*scale + disp'.

  // a post/pre-modifying address can be of the form 'base_reg += disp'
  // or 'base_reg += mod_reg', although for now we support only the former.
  // if 'disp' is positive, it is a post/pre-increment.
  // if 'disp' is negative, it is a post/pre-decrement.
  // if abs ('disp') == access mode size it's a {PRE,POST}_{INC_DEC}.

  enum addr_type_t { non_mod, pre_mod, post_mod };
  enum access_type_t { load, store, reg_mod, reg_use };

  typedef int regno_t;

  // for a constant displacement using a 32 bit int should be sufficient.
  // however, we use it also to represent constant addresses.
  typedef HOST_WIDE_INT disp_t;
  typedef int scale_t;

  enum
  {
    infinite_costs = INT_MAX// std::numeric_limits<int>::max ();
  };

  static const rtx invalid_regno;
  static const rtx any_regno;

  static regno_t get_regno (const_rtx x)
  {
    if (x == NULL)
      return -1;
    if (x == any_regno)
      return -2;
    return REGNO (x);
  }

  // we could use an abstract base class etc etc, but that usually implies
  // that we need to store objects thereof on the free store and keep the
  // pointers.  i.e. we can't pass/copy the whole thing by value and keep the
  // type info.  because of that we have one fat address expression base class
  // that keeps all the possible members of all subclasses.
  class addr_expr
  {
  public:
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

    bool operator==(const addr_expr &other) const
    {
      return (base_reg () == other.base_reg ()
              && (index_reg () == other.index_reg ())
              && (scale () == other.scale ())
              && (disp () == other.disp ()));
    }

    // returns true if the original address expression is more complex than
    // what AMS can handle.
    bool is_invalid (void) const
    {
      return disp_min () > disp_max ();
    }

    // displacement relative to the base reg before the actual memory access.
    // e.g. a pre-dec access will have a pre-disp of -mode_size.
    disp_t entry_disp (void) const
    {
      return type () == pre_mod ? disp () : 0;
    }

    // displacement relative to the base reg after the actual memory access.
    // e.g. a post-inc access will have a post-disp of +mode_size.
    disp_t exit_disp (void) const
    {
      return type () == post_mod ? disp () : 0;
    }

  protected:
    addr_type_t m_type;

    // although constant addresses can be grouped and a base reg can be
    // derived, on some architectures (8051) using a constant address directly
    // is possible.
    // after the constant pool layout has been determined, the value of the
    // base register will be a constant label_ref or something.
    rtx m_base_reg;
    disp_t m_disp;
    disp_t m_disp_min;
    disp_t m_disp_max;
    rtx m_index_reg;
    scale_t m_scale;
    scale_t m_scale_min;
    scale_t m_scale_max;
  };

  class non_mod_addr : public addr_expr
  {
  public:
    non_mod_addr (rtx base_reg, rtx index_reg, scale_t scale,
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
      m_scale_min = scale_min;
      m_scale_max = scale_max;
    }

    non_mod_addr (rtx base_reg, rtx index_reg, scale_t scale, disp_t disp)
    {
      m_type = non_mod;
      m_base_reg = base_reg;
      m_disp = disp;
      m_disp_min = disp;
      m_disp_max = disp;
      m_index_reg = index_reg;
      m_scale = scale;
      m_scale_min = scale;
      m_scale_max = scale;
    }

//   non_mod_addr (regno_t base_reg, disp_t disp, disp_t min_disp, disp_t max_disp)
  };

  class pre_mod_addr : public addr_expr
  {
  public:
    pre_mod_addr (rtx base_reg, disp_t disp, disp_t disp_min, disp_t disp_max)
    {
      m_type = pre_mod;
      m_base_reg = base_reg;
      m_disp = disp;
      m_disp_min = disp_min;
      m_disp_max = disp_max;
      m_index_reg = invalid_regno;
      m_scale = m_scale_min = m_scale_max = 0;
    }

    pre_mod_addr (rtx base_reg, disp_t disp)
    {
      m_type = pre_mod;
      m_base_reg = base_reg;
      m_disp = disp;
      m_disp_min = disp;
      m_disp_max = disp;
      m_index_reg = invalid_regno;
      m_scale = m_scale_min = m_scale_max = 0;
    }
  };

  class post_mod_addr : public addr_expr
  {
  public:
    post_mod_addr (rtx base_reg, disp_t disp, disp_t disp_min, disp_t disp_max)
    {
      m_type = post_mod;
      m_base_reg = base_reg;
      m_disp = disp;
      m_disp_min = disp_min;
      m_disp_max = disp_max;
      m_index_reg = invalid_regno;
      m_scale = m_scale_min = m_scale_max = 0;
    }

    post_mod_addr (rtx base_reg, disp_t disp)
    {
      m_type = post_mod;
      m_base_reg = base_reg;
      m_disp = disp;
      m_disp_min = disp;
      m_disp_max = disp;
      m_index_reg = invalid_regno;
      m_scale = m_scale_min = m_scale_max = 0;
    }
  };

  class access;
  class access_sequence;

  template <typename OutputIterator> static void
  find_mem_accesses (rtx& x, OutputIterator out,
		     access_type_t access_type = load);

  template <typename OutputIterator> static void
  collect_addr_reg_uses (access_sequence& as, rtx addr_reg, rtx_insn *start_insn,
                         rtx abort_at_insn, OutputIterator out,
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

  static void find_reg_value (rtx reg, rtx_insn* insn, rtx* mod_expr,
			      rtx_insn** mod_insn, machine_mode* auto_mod_mode);

  static addr_expr extract_addr_expr (rtx x, rtx_insn* insn, rtx_insn *root_insn,
				      machine_mode mem_mach_mode,
				      access_sequence* as,
				      std::vector<access*>& inserted_reg_mods);

  static addr_expr extract_addr_expr (rtx x, rtx_insn* insn, rtx_insn* root_insn,
				      machine_mode mem_mach_mode,
				      access_sequence* as)
  {
    std::vector<access*> inserted_reg_mods;
    return extract_addr_expr (x, insn, root_insn, mem_mach_mode, as,
			      inserted_reg_mods);
  }

  static addr_expr extract_addr_expr (rtx x, machine_mode mem_mach_mode = Pmode)
  {
    return extract_addr_expr (x, NULL, NULL, mem_mach_mode, NULL);
  }

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

  // a memory access in the insn stream.
  class access
  {
  public:
    // the ams pass obtains a set of alternatives for a given access from the
    // delegate (the target).  an alternative is simply a desired/supported
    // address expression and its cost.  the costs are allowed to vary for
    // each access independently, so the target can estimate the costs based
    // on the context.
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

    class alternative
    {
    public:
      alternative (const addr_expr& ae, int costs)
      : m_addr_expr (ae), m_costs (costs) { }

      alternative () {  }

      const addr_expr& address (void) const { return m_addr_expr; }
      int costs (void) const { return m_costs; }
      void update_costs (int new_cost) { m_costs = new_cost; }

    private:
      addr_expr m_addr_expr;
      int m_costs;
    };

    access (rtx_insn* insn, rtx* mem, access_type_t access_type,
	    addr_expr original_addr_expr, addr_expr addr_expr,
	    bool should_optimize, int cost = infinite_costs);
    access (rtx_insn* insn, addr_expr original_addr_expr, addr_expr addr_expr,
	    rtx addr_rtx, rtx mod_reg, int cost, bool removable);
    access (rtx_insn* insn, std::vector<rtx_insn*> trailing_insns,
            rtx* reg_ref, addr_expr original_addr_expr,
	    addr_expr addr_expr);
    access (rtx addr_reg, addr_expr reg_value);

    // the resolved address expression, i.e. the register and constant value
    // have been traced through reg copies etc and the address expression has
    // been canonicalized.
    const addr_expr& address (void) const { return m_addr_expr; }

    // the original address expression as it was found in the insn stream.
    // if the original address expression does not fit into our scheme, we
    // ignore it.
    const addr_expr& original_address (void) const { return m_original_addr_expr; }

    // If m_access_type is REG_MOD, this access represents the modification
    // of an address register.  In this case, m_addr_reg stores the register
    // that's modified and m_addr_expr is its new address.
    // If m_original_addr_expr is invalid, appropriate reg-mods are inserted
    // during address mod generation to arrive at the effective address.
    //
    // If the type is REG_USE, the access represents the use of an address
    // reg outside of a memory access.  In this case, m_addr_expr is the
    // effective address of the address reg during the use and
    // m_mem_ref is a reference to the rtx inside the insn that uses the reg.
    access_type_t access_type (void) const { return m_access_type; }

    machine_mode mach_mode (void) const { return m_machine_mode; }
    int access_size (void) const { return GET_MODE_SIZE (m_machine_mode); }
    addr_space_t addr_space (void) const { return m_addr_space; }
    int cost (void) const { return m_cost; }

    // the insn where this access occurs.
    rtx_insn* insn (void) const { return m_insn; }

    // Stores the address if it can't be described with an
    // addr_expr, or NULL_RTX if the address is unknown.
    rtx addr_rtx (void) const { return m_addr_rtx; }

    // For reg_mod accesses, true if the access can be removed during
    // gen_address_mod.  Set to true for most of the reg_mod accesses
    // found in the original insn list.
    bool removable (void) const { return m_removable; }

    void mark_unremovable (void) { m_removable = false; }

    // If false, AMS skips this access when optimizing.
    bool should_optimize (void) const { return m_should_optimize; }

    // For reg_mod accesses, shows the register rtx that was modified.
    rtx address_reg (void) const { return m_addr_reg; }

    // For reg_mod accesses, shows whether the register is used
    // in another access. If so, register cloning costs must be
    // taken into account when using it a second time.
    // FIXME: It might be better for M_USED to be public instead of having 3
    // accessing/modifying functions.
    bool is_used (void) const { return m_used; }

    void set_used () { m_used = true; }
    void reset_used () { m_used = false; }

    // Return true if this is a trailing access, i,e. the first use or
    // modification of an address reg in the access sequence's successor
    // BBs. There can be multiple trailing accesses if the addr reg is
    // set/used in more than one successor BBs.  In this case, AMS only
    // handles them if they are equivalent, and they're represented by a
    // single access.
    bool is_trailing (void) const { return !trailing_insns ().empty (); }

    // For a trailing access, the insns where the reg use/mod occur. These
    // can be multiple insns if the access represents multiple equivalent
    // uses or mods.
    const std::vector<rtx_insn*>& trailing_insns (void) const
    { return m_trailing_insns; }

    access& add_alternative (int costs, const addr_expr& ae)
    {
      gcc_assert (m_alternatives_count < MAX_ALTERNATIVES);
      m_alternatives[m_alternatives_count++] = alternative (ae, costs);
      return *this;
    }

    void clear_alternatives (void) { m_alternatives_count = 0; }

    int alternatives_count (void) const { return m_alternatives_count; }

    alternative* begin_alternatives (void)
    {
      return &(m_alternatives[0]);
    }

    alternative* end_alternatives (void)
    {
      return begin_alternatives () + m_alternatives_count;
    }

    const alternative* begin_alternatives (void) const
    {
      return &(m_alternatives[0]);
    }

    const alternative* end_alternatives (void) const
    {
      return begin_alternatives () + m_alternatives_count;
    }

    bool matches_alternative (const alternative* alt) const;

    void update_original_address (int new_cost, addr_expr new_addr_expr)
    {
      m_cost = new_cost;
      m_original_addr_expr = new_addr_expr;
      m_addr_rtx = NULL;
    }

    void update_original_address (int new_cost, rtx new_addr_rtx)
    {
      m_cost = new_cost;
      m_original_addr_expr = make_invalid_addr ();
      m_addr_rtx = new_addr_rtx;
    }

    void update_effective_address (addr_expr new_addr_expr)
    {
      m_addr_expr = new_addr_expr;
      m_addr_rtx = NULL;
    }

    void update_cost (int new_cost) { m_cost = new_cost; }

    bool update_mem (rtx new_addr)
    {
      bool val = validate_change (m_insn, m_mem_ref,
				  replace_equiv_address (*m_mem_ref, new_addr),
				  false);
      return val;
    }

    void update_use_expr (rtx new_expr)
    {
      validate_change (m_insn, m_mem_ref, new_expr, false);
    }

    void update_insn (rtx_insn *new_insn)
    {
      m_insn = new_insn;
    }

    static bool registers_match (rtx reg, rtx alt_reg)
    {
      if (alt_reg == any_regno)
	return (reg != invalid_regno);
      return (reg == alt_reg);
    }

    static bool adjacent_with_auto_mod (const access& first, const access& second);
    static bool not_adjacent_with_auto_mod
      (const access& first, const access& second)
    {
      return !adjacent_with_auto_mod (first, second);
    }

  private:
    addr_expr m_original_addr_expr;
    addr_expr m_addr_expr;
    access_type_t m_access_type;
    machine_mode m_machine_mode;
    addr_space_t m_addr_space;
    int m_cost;
    rtx_insn* m_insn;
    std::vector<rtx_insn*> m_trailing_insns;
    rtx* m_mem_ref; // reference to the mem rtx inside the insn.
    bool m_removable;
    bool m_should_optimize;
    rtx m_addr_rtx;
    rtx m_addr_reg;
    bool m_used;

    // all available alternatives for this access as reported by the target.
    enum
    {
      MAX_ALTERNATIVES = 16
    };

    int m_alternatives_count;
    alternative m_alternatives[MAX_ALTERNATIVES];
  };

  class access_sequence
  {
  public:

    typedef std::list<access>::iterator iterator;
    typedef std::list<access>::const_iterator const_iterator;
    typedef std::list<access>::reverse_iterator reverse_iterator;
    typedef std::list<access>::const_reverse_iterator const_reverse_iterator;

    void gen_address_mod (delegate& dlg);

    void update_insn_stream (void);

    int cost (void) const;
    void update_cost (delegate& dlg);

    void find_addr_regs (void);
    void add_missing_reg_mods (void);

    bool reg_used_in_sequence (rtx reg, access_sequence::iterator search_start);
    bool reg_used_in_sequence (rtx reg)
    {
      return reg_used_in_sequence (reg, accesses ().begin ());
    }

    void find_reg_uses (void);
    void find_reg_end_values (void);

    void update_access_alternatives (delegate& dlg,
				     access_sequence::iterator acc)
    {
      if (acc->access_type () == load || acc->access_type () == store)
	dlg.mem_access_alternatives (*acc, *this, acc);
      else
	// If the access isn't a true memory access, the
	// address has to be loaded into a single register.
	acc->add_alternative (0, make_reg_addr ());
    }

    access&
    add_mem_access (rtx_insn* insn, rtx* mem, access_type_t access_type);

    access&
    add_reg_mod (rtx_insn* insn, const addr_expr& original_addr_expr,
		 const addr_expr& addr_expr, rtx addr_rtx,
		 rtx_insn* mod_insn, rtx reg,
		 int cost = infinite_costs, bool removable = false);

    access&
    add_reg_mod (rtx_insn* insn, const addr_expr& original_addr_expr,
		 const addr_expr& addr_expr, rtx_insn* mod_insn,
		 rtx reg, int cost = infinite_costs, bool removable = false);

    access&
    add_reg_mod (rtx_insn* insn, rtx addr_rtx, rtx_insn* mod_insn,
		 rtx reg, int cost = infinite_costs, bool removable = false);

    access&
    add_reg_mod (access_sequence::iterator insert_before,
		 const addr_expr& original_addr_expr,
		 const addr_expr& addr_expr, rtx_insn* mod_insn,
		 rtx reg, int cost = infinite_costs, bool removable = false,
		 bool use_as_start_addr = true);

    access&
    add_reg_use (access_sequence::iterator insert_before,
		 const addr_expr& original_addr_expr,
		 const addr_expr& addr_expr,
		 rtx* reg_ref,
		 rtx_insn* use_insn);
    access&
    add_reg_use (access_sequence::iterator insert_before,
		 const addr_expr& original_addr_expr,
		 const addr_expr& addr_expr,
		 rtx* reg_ref,
		 std::vector<rtx_insn*> use_insns);

    access_sequence::iterator
    remove_access (access_sequence::iterator acc);

    basic_block bb (void)
    {
      for (iterator accs = accesses ().begin (); accs != accesses ().end ();
           ++accs)
        {
          if (accs->insn ())
            return BLOCK_FOR_INSN (accs->insn ());
        }
      gcc_unreachable ();
    }

    std::list<access>& accesses (void) { return m_accs; }
    const std::list<access>& accesses (void) const { return m_accs; }

    // The address modifying insns related to this access sequence
    // that are in the insn stream.  Used to delete the original insns
    // in update_insn_stream.
    // FIXME: Make different versions of the same access sequence share
    // the same reg-mod insn list.
    std::vector<rtx_insn*>& reg_mod_insns (void) { return m_reg_mod_insns; }

    // A hash_map containing the address regs of the sequence and the last
    // reg_mod access that modified them.
    hash_map<rtx, access*>& addr_regs (void) { return m_addr_regs; }

    // A structure used to store the address regs that can be used as a starting
    // point to arrive at another address during address mod generation.
    class start_addr_list
    {
    public:

      std::list<access*>
      get_relevant_addresses (const addr_expr& end_addr);

      void add (access* start_addr);
      void remove (access* start_addr);

    private:

      // List of addresses that only have a constant displacement.
      std::list<access*> m_const_addresses;

      // A map for storing addresses that have a base and/or index reg.
      // The key of each stored address is its base or index reg (the
      // address is stored twice if it has both).
      std::multimap<rtx, access*> m_reg_addresses;
    };

    // A structure storing the reg_mod accesses from the sequence in such way
    // that they can be searched through efficiently when looking for possible
    // starting addresses to use for arriving at a given end address.
    start_addr_list& start_addresses (void)  { return m_start_addr_list; }

    // find the first/next true mem access in this access sequence.  returns
    // the end iterator if nothing is found.
    // FIXME: convert this into an iterator decorator and also add variants
    // to iterate over other things than mem accesses.
    iterator first_mem_access (void);
    iterator next_mem_access (iterator i);
    const_iterator first_mem_access (void) const;
    const_iterator next_mem_access (const_iterator i) const;

    // find the first/next access in this sequence that should be
    // optimized by gen_address_mod.
    iterator first_access_to_optimize (void);
    iterator next_access_to_optimize (iterator i);
    const_iterator first_access_to_optimize (void) const;
    const_iterator next_access_to_optimize (const_iterator i) const;

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
      }

      void reset_changes (access_sequence &as)
      {
	std::for_each (inserted_accs ().begin (), inserted_accs ().end (),
            std::bind1st (std::mem_fun (&access_sequence::remove_access), &as));
	inserted_accs ().clear ();

	std::for_each (use_changed_accs ().begin (), use_changed_accs ().end (),
            std::mem_fun (&access::reset_used));
	use_changed_accs ().clear ();
      }

      // List of accesses that were inserted into the sequence.
      std::vector<access_sequence::iterator>&
      inserted_accs (void) { return m_inserted_accs; }

      // List of accesses whose M_USED field was changed.
      std::vector<access*>&
      use_changed_accs (void) { return m_use_changed_accs; }

    private:
      std::vector<access_sequence::iterator> m_inserted_accs;
      std::vector<access*> m_use_changed_accs;
    };

    int get_clone_cost (access_sequence::iterator &acc, delegate& dlg);

    int gen_min_mod (access_sequence::iterator acc,
                     delegate& dlg, int lookahead_num,
                     bool record_in_sequence);

    void gen_mod_for_alt (access::alternative& alternative,
			  access* start_base,
			  access* start_index,
			  const addr_expr& end_base,
			  const addr_expr& end_index,
			  access_sequence::iterator acc,
			  mod_tracker& mod_tracker,
			  delegate& dlg);

    struct min_mod_cost_result
    {
      int cost;
      access* min_start_addr;

      min_mod_cost_result (void)
      : cost (infinite_costs), min_start_addr (NULL) { }

      min_mod_cost_result (int c, access* a)
      : cost (c), min_start_addr (a) { }
    };

    min_mod_cost_result
    find_min_mod_cost (const addr_expr& end_addr,
		       access_sequence::iterator insert_before,
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
    try_modify_addr (access* start_addr, const addr_expr& end_addr,
		     disp_t disp_min, disp_t disp_max, addr_type_t addr_type,
		     access_sequence::iterator &access_place,
		     mod_tracker &mod_tracker,
		     delegate& dlg);

    std::list<access> m_accs;
    hash_map<rtx, access*> m_addr_regs;
    start_addr_list m_start_addr_list;
    std::vector<rtx_insn*> m_reg_mod_insns;
  };

  // a delegate for the ams pass.  usually implemented by the target.
  struct delegate
  {
    // provide alternatives for the specified access.
    // use access::add_alternative.
    virtual void mem_access_alternatives (sh_ams::access& a,
                                          const access_sequence& as,
                                          access_sequence::const_iterator acc) = 0;

    // adjust the costs of the specified alternative of the specified
    // access.  called after the alternatives of all accesses have
    // been retrieved.
    virtual void adjust_alternative_costs (access::alternative& alt,
                                           const access_sequence& as,
                                           access_sequence::const_iterator acc) = 0;

    // provide the number of subsequent accesses that should be taken into
    // account when trying to minimize the costs of the specified access.
    virtual int lookahead_count (const access_sequence& as,
                                 access_sequence::const_iterator acc) = 0;

    // provide the cost for adding a constant to the specified
    // address register.
    // the cost must be somehow relative to the cost provided for access
    // alternatives.
    virtual int addr_reg_disp_cost (const_rtx reg, sh_ams::disp_t disp,
                                    const access_sequence& as,
                                    access_sequence::const_iterator acc) = 0;

    // provide the cost for multiplying the specified address register
    // by a constant.
    virtual int addr_reg_scale_cost (const_rtx reg, sh_ams::scale_t scale,
                                     const access_sequence& as,
                                     access_sequence::const_iterator acc) = 0;

    // provide the cost for adding another register to the specified
    // address register.
    virtual int addr_reg_plus_reg_cost (const_rtx reg, const_rtx disp_reg,
                                        const access_sequence& as,
                                        access_sequence::const_iterator acc) = 0;

    // provide the cost for cloning the address register, which is usually
    // required when splitting an access sequence.  if (address) register
    // pressure is high, return a higher cost to avoid splitting.
    //
    // FIXME: alternative would be 'sequence_split_cost'
    virtual int addr_reg_clone_cost (const_rtx reg,
                                     const access_sequence& as,
                                     access_sequence::const_iterator acc) = 0;

  };

  sh_ams (gcc::context* ctx, const char* name, delegate& dlg);
  virtual ~sh_ams (void);
  virtual bool gate (function* fun);
  virtual unsigned int execute (function* fun);

private:
  static const pass_data default_pass_data;

  delegate& m_delegate;
};


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

#endif // includeguard_gcc_sh_ams_includeguard
