
#ifndef includeguard_gcc_sh_ams_includeguard
#define includeguard_gcc_sh_ams_includeguard

#include "tree-pass.h"
#include <limits>
#include <list>
#include <vector>

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
  enum access_mode_t { load, store, reg_mod };

  typedef int regno_t;
  typedef int disp_t;
  typedef int scale_t;

  enum
  {
    invalid_regno = -1,
    any_regno = -2,
    infinite_costs = INT_MAX// std::numeric_limits<int>::max ();
  };

  // we could use an abstract base class etc etc, but that usually implies
  // that we need to store objects thereof on the free store and keep the
  // pointers.  i.e. we can't pass/copy the whole thing by value and keep the
  // type info.  because of that we have one fat address expression base class
  // that keeps all the possible members of all subclasses.
  class addr_expr
  {
  public:
    addr_type_t type (void) const { return m_type; }
    regno_t base_reg (void) const { return m_base_reg; }
    disp_t disp (void) const { return m_disp; }
    disp_t disp_min (void) const { return m_disp_min; }
    disp_t disp_max (void) const { return m_disp_max; }
    regno_t index_reg (void) const { return m_index_reg; }
    scale_t scale (void) const { return m_scale; }
    scale_t scale_min (void) const { return m_scale_min; }
    scale_t scale_max (void) const { return m_scale_max; }

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

    // FIXME: probably it's better to use an rtx for the base reg, because
    // of things such as addresses into constant pool or constant address
    // accesses.
    // although constant addresses can be grouped and a base reg can be
    // derived, on some architectures (8051) using a constant address directly
    // is possible.
    // after the constant pool layout has been determined, the value of the
    // base register will be a constant label_ref or something.
    regno_t m_base_reg;
    disp_t m_disp;
    disp_t m_disp_min;
    disp_t m_disp_max;
    regno_t m_index_reg;
    scale_t m_scale;
    scale_t m_scale_min;
    scale_t m_scale_max;
  };

  class non_mod_addr : public addr_expr
  {
  public:
    non_mod_addr (regno_t base_reg, regno_t index_reg, scale_t scale,
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

    non_mod_addr (regno_t base_reg, regno_t index_reg, scale_t scale, disp_t disp)
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
    pre_mod_addr (regno_t base_reg, disp_t disp, disp_t disp_min, disp_t disp_max)
    {
      m_type = pre_mod;
      m_base_reg = base_reg;
      m_disp = disp;
      m_disp_min = disp_min;
      m_disp_max = disp_max;
      m_index_reg = invalid_regno;
      m_scale = m_scale_min = m_scale_max = 0;
    }
  };

  class post_mod_addr : public addr_expr
  {
  public:
    post_mod_addr (regno_t base_reg, disp_t disp, disp_t disp_min, disp_t disp_max)
    {
      m_type = post_mod;
      m_base_reg = base_reg;
      m_disp = disp;
      m_disp_min = disp_min;
      m_disp_max = disp_max;
      m_index_reg = invalid_regno;
      m_scale = m_scale_min = m_scale_max = 0;
    }
  };

  class access;
  class access_sequence;

  static void add_new_access
    (access_sequence& as, rtx_insn* insn, rtx* mem,
     access_mode_t access_mode, std::list<rtx_insn*>& reg_mod_insns);
  static void add_reg_mod_access
    (access_sequence& as, rtx_insn* insn, rtx mod_expr,
     rtx_insn* mod_insn, regno_t reg);
  static void find_mem_accesses
    (rtx* x_ref, std::list<std::pair<rtx*, access_mode_t> >& mem_list,
     access_mode_t access_mode = load);
  static void find_reg_value
    (rtx reg, rtx_insn* insn, rtx* mod_expr, rtx_insn** mod_insn);
  static bool find_reg_value_1 (rtx reg, rtx pattern, rtx* value);
  static addr_expr extract_addr_expr
    (rtx x, rtx_insn* insn, rtx_insn* root_insn, machine_mode mem_mach_mode,
     access_sequence& as, bool expand, std::list<rtx_insn*> *reg_mod_insns);

  // helper functions to create a particular type of address expression.
  static addr_expr
  make_reg_addr (regno_t base_reg = any_regno);

  static addr_expr
  make_disp_addr (disp_t disp_min, disp_t disp_max);

  static addr_expr
  make_disp_addr (regno_t base_reg, disp_t disp_min, disp_t disp_max);

  static addr_expr
  make_index_addr (scale_t scale_min, scale_t scale_max);

  static addr_expr
  make_index_addr (void);

  static addr_expr
  make_post_inc_addr (machine_mode mode, regno_t base_reg = any_regno);

  static addr_expr
  make_post_dec_addr (machine_mode mode, regno_t base_reg = any_regno);

  static addr_expr
  make_pre_inc_addr (machine_mode mode, regno_t base_reg = any_regno);

  static addr_expr
  make_pre_dec_addr (machine_mode mode, regno_t base_reg = any_regno);

  static addr_expr
  make_invalid_addr (void);

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

    private:
      addr_expr m_addr_expr;
      int m_costs;
    };

    access (rtx_insn* insn, rtx* mem, access_mode_t access_mode,
	    addr_expr original_addr_expr, addr_expr addr_expr);
    access (rtx_insn* insn, rtx mod_expr, regno_t reg);

    // the resolved address expression, i.e. the register and constant value
    // have been traced through reg copies etc and the address expression has
    // been canonicalized.
    const addr_expr& address (void) const { return m_addr_expr; }

    // the original address expression as it was found in the insn stream.
    // if the original address expression does not fit into our scheme, we
    // ignore it.
    const addr_expr& original_address (void) const { return m_original_addr_expr; }

    // If m_access_mode is REG_MOD, this access represents the modification
    // of an address register.
    access_mode_t access_mode (void) const { return m_access_mode; }

    machine_mode mach_mode (void) const { return m_machine_mode; }
    int access_size (void) const { return GET_MODE_SIZE (m_machine_mode); }
    addr_space_t addr_space (void) const { return m_addr_space; }

    // the insn where this access occurs.
    rtx_insn* insn (void) const { return m_insn; }

    // reference to the mem rtx inside the insn.
    rtx* mem_ref (void) const { return m_mem_ref; }

    // if m_access_mode is REG_MOD, this stores the expression
    // that the register is set to (NULL_RTX if the value is
    // unknown).
    rtx reg_mod_expr (void) const { return m_reg_mod_expr; }

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

  private:
    addr_expr m_original_addr_expr;
    addr_expr m_addr_expr;
    access_mode_t m_access_mode;
    machine_mode m_machine_mode;
    addr_space_t m_addr_space;
    rtx_insn* m_insn;
    rtx* m_mem_ref;
    rtx m_reg_mod_expr;

    // all available alternatives for this access as reported by the target.
    enum
    {
      MAX_ALTERNATIVES = 16
    };

    int m_alternatives_count;
    alternative m_alternatives[MAX_ALTERNATIVES];
  };

  struct delegate;

  class access_sequence : public std::list<access>
  {
  public:
    void update_insn_stream
      (std::list<rtx_insn*>& reg_mod_insns, delegate& dlg);

    // A structure used to keep track of the address registers' values when
    // generating new address modifying insns.  Each generated insn has a
    // corresponding reg_value struct.
    class reg_value
    {
    public:
      reg_value (regno_t reg, addr_expr value)
        : m_reg (reg), m_value (value), m_used (false) { }
      reg_value (regno_t reg)
        : m_reg (reg), m_value (make_reg_addr (reg)), m_used (false) { }

      // The register that was set by the insn.
      int reg (void) const { return m_reg; }

      // The value that the register is set to, expressed with the original
      // address registers.
      const addr_expr& value (void) const { return m_value; }

      // Shows whether this register is used in another address-modifying
      // insn.  If so, register cloning costs must be taken into account
      // when using it a second time.
      bool is_used (void) const { return m_used; }

      void set_used () { m_used = true; }

    private:
      regno_t m_reg;
      addr_expr m_value;
      bool m_used;
    };

    int find_min_mod_cost
      (std::vector<reg_value>& addr_reg_values,
       reg_value **min_start_addr, const addr_expr& end_addr,
       disp_t disp_min, disp_t disp_max, delegate& dlg);
    regno_t insert_reg_mod_insns
      (reg_value* start_value, const addr_expr& end_addr,
       rtx_insn* insn, std::vector<reg_value>& addr_reg_values,
       disp_t disp_min, disp_t disp_max, delegate& dlg);
    int try_modify_addr
      (reg_value* start_value, const addr_expr& end_addr,
       disp_t disp_min, disp_t disp_max,
       std::vector<reg_value>* addr_reg_values, rtx_insn* insn,
       regno_t* final_addr_regno, delegate& dlg);
    int try_modify_addr
      (reg_value* start_value, const addr_expr& end_addr,
       disp_t disp_min, disp_t disp_max, delegate& dlg);

  };

  // a delegate for the ams pass.  usually implemented by the target.
  struct delegate
  {
    // provide alternatives for the specified access.
    // use access::add_alternative.
    virtual void mem_access_alternatives (sh_ams::access& a) = 0;

    // provide the cost for adding a constant to the specified
    // address register.
    // the cost must be somehow relative to the cost provided for access
    // alternatives.
    virtual int addr_reg_disp_cost (sh_ams::regno_t reg, sh_ams::disp_t disp/*, const access_sequence& as*/) = 0;

    // provide the cost for multiplying the specified address register
    // by a constant.
    virtual int addr_reg_scale_cost (sh_ams::regno_t reg, sh_ams::scale_t scale/*, const access_sequence& as*/) = 0;

    // provide the cost for adding another register to the specified
    // address register.
    virtual int addr_reg_plus_reg_cost (sh_ams::regno_t reg, sh_ams::regno_t disp_reg/*, const access_sequence& as*/) = 0;

    // provide the cost for cloning the address register, which is usually
    // required when splitting an access sequence.  if (address) register
    // pressure is high, return a higher cost to avoid splitting.
    //
    // FIXME: alternative would be 'sequence_split_cost'
    virtual int addr_reg_clone_cost (sh_ams::regno_t reg /*, const access_sequence& as*/) = 0;
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
sh_ams::make_reg_addr (regno_t base_reg)
{
  return non_mod_addr (base_reg, invalid_regno, 0, 0, 0, 0, 0, 0);
}

inline sh_ams::addr_expr
sh_ams::make_disp_addr (disp_t disp_min, disp_t disp_max)
{
  return non_mod_addr (any_regno, invalid_regno, 0, 0, 0, 0, disp_min, disp_max);
}

inline sh_ams::addr_expr
sh_ams::make_disp_addr (regno_t base_reg, disp_t disp_min, disp_t disp_max)
{
  return non_mod_addr (base_reg, invalid_regno, 0, 0, 0, 0, disp_min, disp_max);
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
sh_ams::make_post_inc_addr (machine_mode mode, regno_t base_reg)
{
  const int mode_sz = GET_MODE_SIZE (mode);
  return post_mod_addr (base_reg, mode_sz, mode_sz, mode_sz);
}

inline sh_ams::addr_expr
sh_ams::make_post_dec_addr (machine_mode mode, regno_t base_reg)
{
  const int mode_sz = -GET_MODE_SIZE (mode);
  return post_mod_addr (base_reg, mode_sz, mode_sz, mode_sz);
}

inline sh_ams::addr_expr
sh_ams::make_pre_inc_addr (machine_mode mode, regno_t base_reg)
{
  const int mode_sz = GET_MODE_SIZE (mode);
  return pre_mod_addr (base_reg, mode_sz, mode_sz, mode_sz);
}

inline sh_ams::addr_expr
sh_ams::make_pre_dec_addr (machine_mode mode, regno_t base_reg)
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
