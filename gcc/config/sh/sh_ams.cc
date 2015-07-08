
#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "machmode.h"
#include "predict.h"
#include "vec.h"
#include "hashtab.h"
#include "hash-set.h"
#include "tm.h"
#include "hard-reg-set.h"
#include "input.h"
#include "function.h"
#include "dominance.h"
#include "cfg.h"
#include "cfgrtl.h"
#include "cfganal.h"
#include "lcm.h"
#include "cfgbuild.h"
#include "cfgcleanup.h"
#include "basic-block.h"
#include "df.h"
#include "rtl.h"
#include "insn-config.h"
#include "insn-codes.h"
#include "emit-rtl.h"
#include "recog.h"
#include "tree-pass.h"
#include "target.h"
#include "symtab.h"
#include "inchash.h"
#include "tree.h"
#include "optabs.h"
#include "flags.h"
#include "statistics.h"
#include "double-int.h"
#include "real.h"
#include "fixed-value.h"
#include "alias.h"
#include "wide-int.h"
#include "expmed.h"
#include "dojump.h"
#include "explow.h"
#include "calls.h"
#include "varasm.h"
#include "stmt.h"
#include "expr.h"

#include <algorithm>
#include <list>
#include <vector>

#include "sh_ams.h"

#include "sh-protos.h"


// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Helper functions

#define log_msg(...)\
  do { if (dump_file != NULL) fprintf (dump_file, __VA_ARGS__); } while (0)

#define log_insn(i)\
  do { if (dump_file != NULL) print_rtl_single (dump_file, \
						(const_rtx)i); } while (0)

#define log_rtx(r)\
  do { if (dump_file != NULL) print_rtl (dump_file, (const_rtx)r); } while (0)

#define log_return(retval, ...)\
  do { if (dump_file != NULL) fprintf (dump_file, __VA_ARGS__); \
       return retval; } while (0)

#define log_return_void(...)\
  do { if (dump_file != NULL) fprintf (dump_file, __VA_ARGS__); \
       return; } while (0)

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// RTL pass class

const pass_data sh_ams::default_pass_data =
{
  RTL_PASS,		// type
  "",			// name (overwritten by the constructor)
  OPTGROUP_NONE,	// optinfo_flags
  TV_AUTO_INC_DEC,	// tv_id
  0,			// properties_required
  0,			// properties_provided
  0,			// properties_destroyed
  0,			// todo_flags_start
  TODO_df_finish	// todo_flags_finish
};

const rtx sh_ams::invalid_regno = (const rtx)0;
const rtx sh_ams::any_regno = (const rtx)1;
std::vector<rtx_insn*>
sh_ams::access_sequence::m_reg_mod_insns = std::vector<rtx_insn*> ();

sh_ams::sh_ams (gcc::context* ctx, const char* name, delegate& dlg)
: rtl_opt_pass (default_pass_data, ctx),
  m_delegate (dlg)
{
  this->name = name;
}

sh_ams::~sh_ams (void)
{
}

bool sh_ams::gate (function* /*fun*/)
{
  return optimize > 0 && flag_auto_inc_dec;
}

namespace
{

void log_reg (rtx x)
{
  if (x == sh_ams::invalid_regno)
    log_msg ("(nil)");
  else if (x == sh_ams::any_regno)
    log_msg ("(reg:%s *)", GET_MODE_NAME (Pmode));
  else
    log_rtx (x);
}

void
log_addr_expr (const sh_ams::addr_expr& ae)
{
  if (dump_file == NULL)
    return;

  if (ae.type () == sh_ams::pre_mod)
    {
      log_msg ("@( += %lld ", ae.disp ());
      log_reg (ae.base_reg ());
      log_msg (" )");
      return;
    }

  if (ae.type () == sh_ams::post_mod)
    {
      log_msg ("@( ");
      log_reg (ae.base_reg ());
      log_msg (" += %lld )", ae.disp ());
      return;
    }

  if (ae.type () == sh_ams::non_mod)
    {
      log_msg ("@( ");

      log_reg (ae.base_reg ());

      if (ae.index_reg () != sh_ams::invalid_regno)
	{
	  log_msg (" + ");
	  log_reg (ae.index_reg ());
	  if (ae.scale () != 1)
	    log_msg (" * %d", ae.scale ());
	}

      if (ae.disp () != 0)
	log_msg (" + %lld", ae.disp ());
      else if (ae.disp_min () != ae.disp_max ()
	       && (ae.disp_min () != 0 || ae.disp_max () != 0))
	log_msg (" + (%lld ... %lld)", ae.disp_min (), ae.disp_max ());

      log_msg (" )");
      return;
    }

  gcc_unreachable ();
}

void
log_access (const sh_ams::access& a, bool log_alternatives = true)
{
  if (dump_file == NULL)
    return;

  if (a.access_type () == sh_ams::load)
    log_msg ("load ");
  else if (a.access_type () == sh_ams::store)
    log_msg ("store");
  else if (a.access_type () == sh_ams::reg_mod)
    {
      log_msg ("reg_mod:\n  ");
      log_rtx (a.address_reg ());
      log_msg (" set\n");
    }
  else if (a.access_type () == sh_ams::reg_use)
    log_msg ("reg_use:\n");
  else if (a.access_type () == sh_ams::reg_value)
    {
      log_msg ("reg_value:\n  value of ");
      log_rtx (a.address_reg ());
      log_msg (" should be\n  ");
      log_addr_expr (a.address ());
      log_msg ("\n");
      return;
    }
  else
    gcc_unreachable ();

  if (a.access_type () == sh_ams::load || a.access_type () == sh_ams::store)
    log_msg (" %smode (%d):\n",
             GET_MODE_NAME (a.mach_mode ()), a.access_size ());

  log_msg ("  original addr:   ");

  if (a.original_address ().is_invalid ())
    {
      if (a.addr_rtx ()) log_rtx (a.addr_rtx ());
      else log_msg ("unknown");
    }
  else log_addr_expr (a.original_address ());

  if (!a.address ().is_invalid ())
    {
      log_msg ("\n  effective addr:  ");
      log_addr_expr (a.address ());
    }

  if (a.cost () == sh_ams::infinite_costs) log_msg ("\n  cost: infinite");
  else log_msg ("\n  cost: %d", a.cost ());

  if (a.removable ()) log_msg ("\n  (removable)");

  if (a.access_type () == sh_ams::reg_use)
    {
      log_msg ("\n  used in ");
      log_insn (a.insn ());
    }

  if (log_alternatives
      && (a.access_type () == sh_ams::load
	  || a.access_type () == sh_ams::store))
    {
      log_msg ("\n  %d alternatives:\n", a.alternatives_count ());
      int alt_count = 0;
      for (const sh_ams::access::alternative* alt = a.begin_alternatives ();
           alt != a.end_alternatives (); ++alt)
        {
          if (alt_count > 0)
            log_msg ("\n");

          log_msg ("    alt %d, costs %d: ", alt_count, alt->costs ());
          log_addr_expr (alt->address ());
          ++alt_count;
        }
    }
}

// FIXME: Is it OK to use Pmode for the index reg and signed ops?
rtx
expand_mult (rtx a, rtx b)
{
  log_msg ("\nexpand_mult ");
  log_rtx (a);
  log_msg (" * ");
  log_rtx (b);
  log_msg ("\n");

  return expand_mult (Pmode, a, b, NULL, false);
}

rtx
expand_mult (rtx a, HOST_WIDE_INT b)
{
  return expand_mult (a, GEN_INT (b));
}

rtx
expand_plus (rtx a, rtx b)
{
  log_msg ("\nexpand_plus ");
  log_rtx (a);
  log_msg (" + ");
  log_rtx (b);
  log_msg ("\n");

  if (b == const0_rtx)
    return a;

  return expand_binop (Pmode, add_optab, a, b, NULL, false, OPTAB_LIB_WIDEN);
}

rtx
expand_plus (rtx a, HOST_WIDE_INT b)
{
  if (b == 0)
    return a;

  return expand_plus (a, GEN_INT (b));
}

rtx
expand_minus (rtx a, rtx b)
{
  log_msg ("\nexpand_minus ");
  log_rtx (a);
  log_msg (" - ");
  log_rtx (b);
  log_msg ("\n");

  if (b == const0_rtx)
    return a;

  return expand_binop (Pmode, sub_optab, a, b, NULL, false, OPTAB_LIB_WIDEN);
}

rtx
expand_minus (rtx a, HOST_WIDE_INT b)
{
  if (b == 0)
    return a;

  return expand_minus (a, GEN_INT (b));
}

} // anonymous namespace

// borrowed from C++11

namespace stdx
{

template<class ForwardIt> ForwardIt
next (ForwardIt it,
      typename std::iterator_traits<ForwardIt>::difference_type n = 1)
{
  std::advance (it, n);
  return it;
}

} // namespace stdx


sh_ams::access::access
(rtx_insn* insn, rtx* mem, access_type_t access_type,
 addr_expr original_addr_expr, addr_expr addr_expr,
 bool should_optimize, int cost)
{
  m_access_type = access_type;
  m_machine_mode = GET_MODE (*mem);
  m_addr_space = MEM_ADDR_SPACE (*mem);
  m_cost = cost;
  m_insn = insn;
  m_mem_ref = mem;
  m_original_addr_expr = original_addr_expr;
  m_addr_expr = addr_expr;
  m_addr_rtx = NULL;
  m_removable = false;
  m_should_optimize = should_optimize;
  m_addr_reg = NULL;
  m_used = false;
  m_alternatives_count = 0;
}

// Constructor for reg_mod accesses.
sh_ams::access::access
(rtx_insn* insn, addr_expr original_addr_expr, addr_expr addr_expr,
 rtx addr_rtx, rtx mod_reg, int cost, bool removable)
{
  m_access_type = reg_mod;
  m_cost = cost;
  m_insn = insn;
  m_mem_ref = NULL;
  m_original_addr_expr = original_addr_expr;
  m_addr_expr = addr_expr;
  m_addr_rtx = addr_rtx;
  m_removable = removable;
  m_should_optimize = true;
  m_addr_reg = mod_reg;
  // Mark reg <- constant accesses  as used so that cloning
  // costs are always added during address modification generation.
  // This encourages the generator to reuse the base regs
  // of previous constant accesses.
  m_used = (original_addr_expr.has_no_base_reg ()
            && original_addr_expr.has_no_index_reg ());
  m_alternatives_count = 0;
}

// Constructor for reg_use accesses.
sh_ams::access::access
(rtx_insn* insn, rtx* reg_ref, addr_expr original_addr_expr,
 addr_expr addr_expr, rtx addr_rtx)
{
  m_access_type = reg_use;
  m_cost = 0;
  m_insn = insn;
  m_mem_ref = reg_ref;
  m_original_addr_expr = original_addr_expr;
  m_addr_expr = addr_expr;
  m_addr_rtx = addr_rtx;
  m_removable = false;
  m_should_optimize = !addr_expr.is_invalid ();
  m_addr_reg = NULL;
  m_used = false;
  m_alternatives_count = 0;
}

// Constructor for reg_value accesses.
sh_ams::access::access
(rtx addr_reg, addr_expr addr_reg_value)
{
  m_access_type = reg_value;
  m_cost = 0;
  m_insn = NULL;
  m_mem_ref = NULL;
  m_original_addr_expr = make_invalid_addr ();
  m_addr_expr = addr_reg_value;
  m_addr_rtx = NULL;
  m_removable = false;
  m_should_optimize = true;
  m_addr_reg = addr_reg;
  m_used = false;
  m_alternatives_count = 0;
}

bool sh_ams::access::
matches_alternative (const alternative* alt) const
{
  const addr_expr &ae = original_address (), &alt_ae = alt->address ();

  if (ae.type () != alt_ae.type ()) return false;

  if (!registers_match (ae.base_reg (), alt_ae.base_reg ())
      || !registers_match (ae.index_reg (), alt_ae.index_reg ()))
    return false;

  if (ae.disp () < alt_ae.disp_min () || ae.disp () > alt_ae.disp_max ())
    return false;

  if (ae.has_index_reg ()
      && (ae.scale () < alt_ae.scale_min ()
          || ae.scale () > alt_ae.scale_max ()))

  if (ae.has_index_reg ()
      && (ae.scale () < alt_ae.scale_min ()
          || ae.scale () > alt_ae.scale_max ()))
    return false;

  return true;
}

// Add a normal access to the end of the access sequence.
sh_ams::access&
sh_ams::access_sequence::add_mem_access (rtx_insn* insn, rtx* mem,
					 access_type_t access_type)
{
  machine_mode m_mode = GET_MODE (*mem);

  // Create an ADDR_EXPR struct from the address expression of MEM.
  addr_expr original_expr =
    extract_addr_expr ((XEXP (*mem, 0)), insn, insn, m_mode, *this, false);

  std::vector<access*> inserted_reg_mods;
  addr_expr expr =
    extract_addr_expr ((XEXP (*mem, 0)), insn, insn,
                       m_mode, *this, inserted_reg_mods, true);

  // If the effective address doesn't fit into an addr_expr,
  // don't try to optimize it.
  bool should_optimize;
  if (expr.is_invalid ())
    {
      expr = original_expr;
      should_optimize = false;

      // The reg modifications that were used to arrive at the address
      // shouldn't be removed in this case.
      for (std::vector<access*>::iterator ins = inserted_reg_mods.begin ();
           ins != inserted_reg_mods.end (); ++ins)
        (*ins)->mark_unremovable ();
    } else should_optimize = true;

  push_back (access (insn, mem, access_type,
                     original_expr, expr, should_optimize));
  return back ();
}

// Create a reg_mod access and add it to the access sequence.
// This function traverses the insn list backwards starting from INSN to
// find the correct place inside AS where the access needs to be inserted.
sh_ams::access&
sh_ams::access_sequence::add_reg_mod (rtx_insn* insn,
				      const addr_expr& original_addr_expr,
				      const addr_expr& addr_expr, rtx addr_rtx,
				      rtx_insn* mod_insn, rtx reg, int cost,
                                      bool removable)
{
  if (empty ())
    {
      push_back (access (mod_insn, original_addr_expr, addr_expr,
                         addr_rtx, reg, cost, removable));
      return back ();
    }

  // Place accesses that have no insn (i.e. the ones that represent the initial
  // values of the hard regs) into the start of the sequence if they haven't
  // been placed there already.
  if (!mod_insn)
    {
      for (access_sequence::iterator as_it = begin ();
           as_it != end () && !as_it->insn (); ++as_it)
        {
          if (as_it->access_type () == reg_mod
              && as_it->address_reg () == reg)
            return *as_it;
        }

      push_front (access (mod_insn, original_addr_expr, addr_expr,
                          addr_rtx, reg, cost, removable));
      return front ();
    }

  access_sequence::reverse_iterator as_it = rbegin ();
  for (rtx_insn* i = insn; i != NULL_RTX; i = PREV_INSN (i))
    {
      if (!INSN_P (i) || !NONDEBUG_INSN_P (i))
        continue;

      // Keep track of the current insn in the sequence.
      while (as_it->insn () && INSN_UID (as_it->insn ()) == INSN_UID (i))
        {
          ++as_it;

          if (as_it == rend () || !as_it->insn ()) break;

          // If the reg_mod access is already inside the access
          // sequence, don't add it a second time.
          if (as_it->access_type () == reg_mod
              && as_it->insn () == mod_insn && as_it->address_reg () == reg
              && as_it->original_address ().base_reg ()
                  == original_addr_expr.base_reg ())
            return *as_it;

        }
      if (as_it == rend () || INSN_UID (i) == INSN_UID (mod_insn))
        {
          // We found mod_insn inside the insn list, so we know where to
          // insert the access.
          insert (as_it.base (),
                  access (mod_insn, original_addr_expr, addr_expr,
                          addr_rtx, reg, cost, removable));
          return *as_it;
        }
    }
  gcc_unreachable ();
}

sh_ams::access&
sh_ams::access_sequence::add_reg_mod (rtx_insn* insn,
                                      const addr_expr& original_addr_expr,
                                      const addr_expr& addr_expr,
                                      rtx_insn* mod_insn, rtx reg, int cost,
                                      bool removable)
{
  return add_reg_mod (insn, original_addr_expr, addr_expr, NULL, mod_insn,
                      reg, cost, removable);
}

sh_ams::access&
sh_ams::access_sequence::add_reg_mod (rtx_insn* insn, rtx addr_rtx,
                                      rtx_insn* mod_insn, rtx reg, int cost,
                                      bool removable)
{
  return add_reg_mod (insn, make_invalid_addr (), make_invalid_addr (),
                      addr_rtx, mod_insn, reg, cost, removable);
}
// Create a reg_mod access and place it before INSERT_BEFORE
// in the access sequence.
sh_ams::access&
sh_ams::access_sequence::add_reg_mod (access_sequence::iterator insert_before,
                                      const addr_expr& original_addr_expr,
                                      const addr_expr& addr_expr,
                                      rtx_insn* mod_insn, rtx reg, int cost,
                                      bool removable)
{
  insert (insert_before,
          access (mod_insn, original_addr_expr, addr_expr,
                  NULL_RTX, reg, cost, removable));
  return *(--insert_before);
}

// Create a reg_use access and place it before INSERT_BEFORE
// in the access sequence.
sh_ams::access&
sh_ams::access_sequence::add_reg_use (access_sequence::iterator insert_before,
                                      const addr_expr& original_addr_expr,
                                      const addr_expr& addr_expr,
                                      rtx addr_rtx,
                                      rtx* reg_ref,
                                      rtx_insn* use_insn)
{
  insert (insert_before,
          access (use_insn, reg_ref, original_addr_expr, addr_expr, addr_rtx));
  return *(--insert_before);
}

sh_ams::access_sequence::iterator
sh_ams::access_sequence::first_mem_access (void)
{
  for (iterator i = begin (); i != end (); ++i)
    if (i->access_type () == load || i->access_type () == store)
      return i;

  return end ();
}

sh_ams::access_sequence::iterator
sh_ams::access_sequence::next_mem_access (iterator i)
{
  if (i == end ())
    return i;

  for (++i; i != end (); ++i)
    if (i->access_type () == load || i->access_type () == store)
      return i;

  return end ();
}

sh_ams::access_sequence::iterator
sh_ams::access_sequence::first_access_to_optimize (void)
{
  for (iterator i = begin (); i != end (); ++i)
    if ((i->access_type () == load || i->access_type () == store
         || i->access_type () == reg_use || i->access_type () == reg_value)
        && i->should_optimize ())
      return i;

  return end ();
}

sh_ams::access_sequence::iterator
sh_ams::access_sequence::next_access_to_optimize (iterator i)
{
  if (i == end ())
    return i;

  for (++i; i != end (); ++i)
    if ((i->access_type () == load || i->access_type () == store
         || i->access_type () == reg_use || i->access_type () == reg_value)
        && i->should_optimize ())
      return i;

  return end ();
}

sh_ams::access_sequence::const_iterator
sh_ams::access_sequence::first_mem_access (void) const
{
  return const_cast<access_sequence*> (this)->first_mem_access ();
}

sh_ams::access_sequence::const_iterator
sh_ams::access_sequence::next_mem_access (const_iterator i) const
{
  return const_cast<access_sequence*> (this)->next_mem_access (i);
}

sh_ams::access_sequence::const_iterator
sh_ams::access_sequence::first_access_to_optimize (void) const
{
  return const_cast<access_sequence*> (this)->first_access_to_optimize ();
}

sh_ams::access_sequence::const_iterator
sh_ams::access_sequence::next_access_to_optimize (const_iterator i) const
{
  return const_cast<access_sequence*> (this)->next_access_to_optimize (i);
}

// The recursive part of find_reg_value. If REG is modified in INSN,
// set VALUE to REG's value and return true. Otherwise, return false.
//
// FIXME: see if we can re-use find_set_of_reg_bb from sh_treg_combine.cc
static std::pair<rtx, bool>
find_reg_value_1 (rtx reg, rtx pat)
{
  switch (GET_CODE (pat))
    {
    case SET:
      {
        rtx dest = SET_DEST (pat);
        if (REG_P (dest) && REGNO (dest) == REGNO (reg))
          {
            // We're in the last insn that modified REG, so return
            // the expression in SET_SRC.
            return std::make_pair (SET_SRC (pat), true);
          }
      }
      break;

    case CLOBBER:
      {
        rtx dest = XEXP (pat, 0);
        if (REG_P (dest) && REGNO (dest) == REGNO (reg))
	  {
	    // The value of REG is unknown.
	    return std::make_pair (NULL_RTX, true);
	  }
      }
      break;

    case PARALLEL:
      for (int i = 0; i < XVECLEN (pat, 0); i++)
        {
          std::pair<rtx, bool> r = find_reg_value_1 (reg, XVECEXP (pat, 0, i));
          if (r.second)
            return r;
        }
      break;

    default:
      break;
    }
  return std::make_pair (NULL_RTX, false);
}

// Find the value that REG was last set to. Write the register value
// into mod_expr and the modifying insn into mod_insn.
// FIXME: make use of other info such as REG_EQUAL notes.
void sh_ams::find_reg_value
(rtx reg, rtx_insn* insn, rtx* mod_expr, rtx_insn** mod_insn)
{
  std::vector<std::pair<rtx*, access_type_t> > mems;

  // Go back through the insn list until we find the last instruction
  // that modified the register.
  for (rtx_insn* i = prev_nonnote_insn_bb (insn); i != NULL_RTX;
       i = prev_nonnote_insn_bb (i))
    {
      if (BARRIER_P (i))
	break;
      if (!NONDEBUG_INSN_P (i) || !NONJUMP_INSN_P (i))
        continue;

      std::pair<rtx, bool> r = find_reg_value_1 (reg, PATTERN (i));
      if (r.second)
        {
          *mod_expr = r.first;
          *mod_insn = i;
          return;
        }
      else if (find_regno_note (i, REG_INC, REGNO (reg)) != NULL)
        {
          // Search for auto-mod memory accesses in the current
          // insn that modify REG.
          mems.clear ();
	  mems.reserve (32);

          find_mem_accesses (PATTERN (i), std::back_inserter (mems));
          for (std::vector<std::pair<rtx*, access_type_t> >
	       ::reverse_iterator m = mems.rbegin (); m != mems.rend (); ++m)
            {
              rtx mem_addr = XEXP (*(m->first), 0);
              rtx_code code = GET_CODE (mem_addr);
              if (GET_RTX_CLASS (code) == RTX_AUTOINC
                  && REG_P (XEXP (mem_addr, 0))
                  && REGNO (XEXP (mem_addr, 0)) == REGNO (reg))
                {
                  *mod_expr = mem_addr;
                  *mod_insn = i;
                  return;
                }
            }
        }
    }
  *mod_expr = reg;
}

// Try to create an ADDR_EXPR struct of the form
// base_reg + index_reg * scale + disp from the access expression X.
// If EXPAND is true, trace the original value of the registers in X
// as far back as possible.
// INSN is the insn in which the access happens.  ROOT_INSN is the INSN
// argument that was passed to the function at the top level of recursion
// (used as the start insn when calling add_reg_mod).
sh_ams::addr_expr
sh_ams::extract_addr_expr (rtx x, rtx_insn* insn, rtx_insn *root_insn,
			   machine_mode mem_mach_mode,
			   access_sequence& as,
                           std::vector<access*>& inserted_reg_mods,
                           bool expand)
{
  addr_expr op0 = make_invalid_addr ();
  addr_expr op1 = make_invalid_addr ();
  disp_t disp;
  scale_t scale;
  rtx base_reg, index_reg;

  if (x == NULL_RTX) return make_invalid_addr ();

  enum rtx_code code = GET_CODE (x);

  // If X is an arithmetic operation, first create ADDR_EXPR structs
  // from its operands. These will later be combined into a single ADDR_EXPR.
  if (code == PLUS || code == MINUS || code == MULT || code == ASHIFT)
    {
      op0 = extract_addr_expr
        (XEXP (x, 0), insn, root_insn, mem_mach_mode, as,
         inserted_reg_mods, expand);
      op1 = extract_addr_expr
        (XEXP (x, 1), insn, root_insn, mem_mach_mode, as,
         inserted_reg_mods, expand);
      if (op0.is_invalid () || op1.is_invalid ())
        return make_invalid_addr ();
    }
  else if (code == NEG)
    {
      op1 = extract_addr_expr
        (XEXP (x, 0), insn, root_insn, mem_mach_mode, as,
         inserted_reg_mods, expand);
      if (op1.is_invalid ())
        return op1;
    }

  // Auto-mod accesses' effective address is found by offseting their constant
  // displacement, or by using the modified expression directly in the case
  // of PRE/POST_MODIFY.
  else if (GET_RTX_CLASS (code) == RTX_AUTOINC)
    {
      addr_type_t mod_type;

      // For post-mod accesses, the displacement is offset only when
      // tracing back the value of a register, or when extracting the
      // original address.  Otherwise, we're interested in the effective
      // address during the memory access, which isn't displaced at that point.
      bool use_post_disp = (INSN_UID (insn) != INSN_UID (root_insn) || !expand);

      switch (code)
        {
        case POST_DEC:
          disp = use_post_disp ? -GET_MODE_SIZE (mem_mach_mode) : 0;
          mod_type = post_mod;
          break;
        case POST_INC:
          disp = use_post_disp ? GET_MODE_SIZE (mem_mach_mode) : 0;
          mod_type = post_mod;
          break;
        case PRE_DEC:
          disp = -GET_MODE_SIZE (mem_mach_mode);
          mod_type = pre_mod;
          break;
        case PRE_INC:
          disp = GET_MODE_SIZE (mem_mach_mode);
          mod_type = pre_mod;
          break;
        case POST_MODIFY:
          op1 = extract_addr_expr (XEXP (x, use_post_disp ? 1 : 0),
                                   insn, root_insn,
                                   mem_mach_mode, as,
                                   inserted_reg_mods, expand);
          if (expand) return op1;
          return post_mod_addr (op1.base_reg (), op1.disp ());
        case PRE_MODIFY:
          op1 = extract_addr_expr (XEXP (x, 1),
                                   insn, root_insn,
                                   mem_mach_mode, as,
                                   inserted_reg_mods, expand);
          if (expand) return op1;
          return pre_mod_addr (op1.base_reg (), op1.disp ());
        default:
          return make_invalid_addr ();
        }

      op1 = extract_addr_expr
        (XEXP (x, 0), insn, root_insn, mem_mach_mode, as,
         inserted_reg_mods, expand);
      disp += op1.disp ();

      if (expand)
        return non_mod_addr (op1.base_reg (), invalid_regno, 1, disp);

      if (mod_type == post_mod)
        return post_mod_addr (op1.base_reg (), disp);
      else
        return pre_mod_addr (op1.base_reg (), disp);
    }

  switch (code)
    {

    // For CONST_INT and REG, the set the base register or the displacement
    // to the appropriate value.
    case CONST_INT:
      return make_const_addr (x);

    case REG:
      if (expand)
        {

          // Find the expression that the register was last set to
          // and convert it to an addr_expr.
          rtx reg_value;
          rtx_insn *reg_mod_insn = NULL;

          access* inserted_mod = NULL;

          find_reg_value (x, insn, &reg_value, &reg_mod_insn);
          // Stop expanding the reg if we reach a hardreg -> pseudo reg
          // copy, or if the reg can't be expanded any further.
          if (reg_value != NULL_RTX && REG_P (reg_value)
              && (REGNO (reg_value) == REGNO (x)
                  || HARD_REGISTER_P (reg_value)))
            {
              // Add a reg_mod access that sets the reg to itself.
              // This makes it easier for the address modification
              // generator to find all possible starting addresses.
              as.add_reg_mod (root_insn,
                              make_reg_addr (x), make_reg_addr (x),
                              reg_mod_insn, x);
              return make_reg_addr (x);
            }

          // Place all the insns that are used to arrive at the address
          // into AS in the form of reg_mod accesses that can be replaced
          // during address mod generation.
          // Auto-mod insns don't need to be inserted because they are
          // already inside the sequence as normal load/store accesses.
          if (!find_reg_note (reg_mod_insn, REG_INC, NULL_RTX))
            {
              addr_expr original_reg_addr_expr
                = extract_addr_expr (reg_value,
                                     reg_mod_insn, reg_mod_insn, mem_mach_mode,
                                     as, inserted_reg_mods, false);
              access* a = &as.add_reg_mod (root_insn,
                                           original_reg_addr_expr,
                                           make_invalid_addr (),
                                           reg_mod_insn, x, infinite_costs, true);
              inserted_reg_mods.push_back (a);
              inserted_mod = a;
            }

          addr_expr reg_addr_expr = extract_addr_expr
            (reg_value, reg_mod_insn, root_insn,
             mem_mach_mode, as, inserted_reg_mods, true);

          // If the expression is something AMS can't handle, use the original
          // reg instead, and update the INSERTED_MOD to store the reg's value
          // as an rtx instead of an addr_expr.
          if (reg_addr_expr.is_invalid ())
            {
              if (inserted_mod)
                {
                  inserted_mod->update_original_address (0, reg_value);

                  // Set all reg_mod accesses that were added while expanding this
                  // register to "unremovable".
                  while (true)
                    {
                      access* a = inserted_reg_mods.back ();
                      a->mark_unremovable ();
                      inserted_reg_mods.pop_back ();
                      if (a == inserted_mod) break;
                    }
                }

              // Add an (rx = rx) reg_mod access to help the
              // address modification generator.
              as.add_reg_mod (root_insn, make_reg_addr (x), make_reg_addr (x),
			      reg_mod_insn, x);

              return make_reg_addr (x);
            }

          if (inserted_mod)
            inserted_mod->update_effective_address (reg_addr_expr);

          return reg_addr_expr;
        }
      else
        return make_reg_addr (x);

    // Handle MINUS by inverting OP1 and proceeding to PLUS.
    // NEG is handled similarly, but returns with OP1 after inverting it.
    case NEG:
    case MINUS:

      // Only expressions of the form base + index * (-1) + disp
      // or base + disp are inverted.
      if (op1.has_index_reg () && op1.scale () != -1)
        break;

      if (op1.has_index_reg ())
        scale = op1.scale ();
      else scale = 1;

      op1 = non_mod_addr (op1.index_reg (), op1.base_reg (),
                          -scale, -op1.disp ());
      if (code == NEG) return op1;

    case PLUS:
      disp = op0.disp () + op1.disp ();
      index_reg = invalid_regno;
      scale = 0;

      // If the same reg is used in both addresses, try to
      // merge them into one reg.
      if (op0.base_reg () == op1.base_reg ())
        {
	  if (op0.has_no_index_reg ())
            {
              op1 = non_mod_addr (invalid_regno, op1.index_reg (),
                                  op1.scale (), op1.disp ());
              op0 = non_mod_addr (invalid_regno, op0.base_reg (),
                                  2, op0.disp ());
            }
          else if (op1.has_no_index_reg ())
            {
              op0 = non_mod_addr (invalid_regno, op0.index_reg (),
                                  op0.scale (), op0.disp ());
              op1 = non_mod_addr (invalid_regno, op1.base_reg (),
                                  2, op1.disp ());
            }
        }
      if (op0.base_reg () == op1.index_reg ())
        {
          op0 = non_mod_addr (invalid_regno, op0.index_reg (),
                              op0.scale (), op0.disp ());

          op1 = non_mod_addr (op1.base_reg (), op1.index_reg (),
                              op1.scale () + 1, op1.disp ());
        }
      if (op1.base_reg () == op0.index_reg ())
        {
          op1 = non_mod_addr (invalid_regno, op1.index_reg (),
                              op1.scale (), op1.disp ());
          op0 = non_mod_addr (op0.base_reg (), op0.index_reg (),
                              op0.scale () + 1, op0.disp ());
        }
      if (op0.index_reg () == op1.index_reg ())
        {
          op0 = non_mod_addr (op0.base_reg (), op0.index_reg (),
                              op0.scale () + op1.scale (), op0.disp ());
          op1 = non_mod_addr (op1.base_reg (), invalid_regno, 0, op1.disp ());
        }

      // If only one operand has a base register, that will
      // be the base register of the sum.
      if (op0.has_no_base_reg ())
        base_reg = op1.base_reg ();
      else if (op1.has_no_base_reg ())
        base_reg = op0.base_reg ();

      // Otherwise, one of the base regs becomes the index reg
      // (with scale = 1).
      else if (op0.has_no_index_reg () && op1.has_no_index_reg ())
        {
          base_reg = op0.base_reg ();
          index_reg = op1.base_reg ();
          scale = 1;
        }

      // If both operands have a base reg and one of them also has
      // an index reg, they can't be combined.
      else break;

      // If only one of the operands has a base reg and only one
      // has an index reg, combine them.
      if (index_reg == invalid_regno)
        {
          if (op0.has_no_index_reg ())
            {
              index_reg = op1.index_reg ();
              scale = op1.scale ();
            }
          else if (op1.has_no_index_reg ())
            {
              index_reg = op0.index_reg ();
              scale = op0.scale ();
            }
          else break;
        }
      return non_mod_addr (base_reg, index_reg, scale, disp);

    // Change shift into multiply.
    case ASHIFT:

      // OP1 must be a non-negative constant.
      if (op1.has_no_base_reg () && op1.has_no_index_reg ()
          && op1.disp () >= 0)
        {
          disp_t mul = disp_t (1) << op1.disp ();
          op1 = non_mod_addr (invalid_regno, invalid_regno, 0, mul);
        }
      else break;
    case MULT:

      // One of the operands must be a constant term.
      // Bring it to the right side.
      if (op0.has_no_base_reg () && op0.has_no_index_reg ())
        std::swap (op0, op1);
      if (op1.has_base_reg () || op1.has_index_reg ())
        break;

      // Only one register can be scaled, so OP0 can have either a
      // BASE_REG or an INDEX_REG.
      if (op0.has_no_base_reg ())
        {
          index_reg = op0.index_reg ();
          scale = op0.scale () * op1.disp ();
        }
      else if (op0.has_no_index_reg ())
        {
          index_reg = op0.base_reg ();
          scale = op1.disp ();
        }
      else break;
      return non_mod_addr (invalid_regno, index_reg,
                           scale, op0.disp () * op1.disp ());
    default:
      break;
    }
  return make_invalid_addr ();
}

// Find the memory accesses in X and add them to OUT, together with their
// access mode. ACCESS_TYPE indicates whether the next mem that we find is read
// or written to.
template <typename OutputIterator> void
sh_ams::find_mem_accesses (rtx& x, OutputIterator out,
			   access_type_t access_type)
{
  switch (GET_CODE (x))
    {
    case MEM:
      *out++ = std::make_pair (&x, access_type);
      break;
    case PARALLEL:
      for (int i = 0; i < XVECLEN (x, 0); i++)
        find_mem_accesses (XVECEXP (x, 0, i), out, access_type);
      break;
    case SET:
      find_mem_accesses (SET_DEST (x), out, store);
      find_mem_accesses (SET_SRC (x), out, load);
      break;
    case CALL:
      find_mem_accesses (XEXP (x, 0), out, load);
      break;
    default:
      if (UNARY_P (x) || ARITHMETIC_P (x))
        {
          for (int i = 0; i < GET_RTX_LENGTH (GET_CODE (x)); i++)
            find_mem_accesses (XEXP (x, i), out, access_type);
        }
      break;
    }
}

// Generate the address modifications needed to arrive at the addresses in
// the access sequence.  They are inserted in the form of reg_mod accesses
// between the regular accesses.
void sh_ams::access_sequence::
gen_address_mod (delegate& dlg)
{
  log_msg ("Generating address modifications\n");

  // Remove the original reg_mod accesses.
  for (access_sequence::iterator accs = begin (); accs != end ();)
    {
      if (accs->removable ()) accs = erase (accs);
      else ++accs;
    }

  for (access_sequence::iterator accs = first_access_to_optimize ();
       accs != end (); accs = next_access_to_optimize (accs))
    gen_min_mod (accs, dlg, true);

  // Mark the reg_mod accesses as "unused" again (except for the
  // reg <- constant copies, which are always marked used).
  for (access_sequence::iterator accs = begin ();
       accs != end (); ++accs)
    {
      if (accs->original_address ().has_base_reg ()
          || accs->original_address ().has_index_reg ())
        accs->reset_used ();
    }
}

// Generate reg_mod accesses needed to arrive at the address in ACC and
// return the cost of the address modifications.
// If RECORD_IN_SEQUENCE is false, don't insert the actual modifications
// in the sequence, only calculate the cost.
int sh_ams::access_sequence::
gen_min_mod
(access_sequence::iterator acc, delegate& dlg, bool record_in_sequence)
{
  const addr_expr& ae = acc->address ();

  if (record_in_sequence)
    {
      log_msg ("\nprocessing access ");
      log_access (*acc);
      log_msg ("\n");
    }

  int min_cost = infinite_costs;
  access::alternative* min_alternative = NULL;
  access *min_start_base = NULL, *min_start_index = NULL;
  addr_expr min_end_base, min_end_index;

  access_sequence::iterator next_acc = record_in_sequence
				       ? next_access_to_optimize (acc)
				       : end ();

  // Go through the alternatives for this access and keep
  // track of the one with minimal costs.
  for (access::alternative* alt = acc->begin_alternatives ();
       alt != acc->end_alternatives (); ++alt)
    {
      const addr_expr& alt_ae = alt->address ();
      addr_expr end_base, end_index;

      // Handle only SH-specific access alternatives for now.
      if (alt_ae.has_no_base_reg ()
          || (alt_ae.type () != non_mod && alt_ae.has_index_reg ())
          || (alt_ae.has_index_reg () && alt_ae.scale () != 1))
        continue;

      if (alt_ae.has_no_index_reg ())
        {
          // If the alternative only has one address register, it must
          // contain the whole address in AE.
          end_base = ae;
        }
      else
        {
          // For base+index type accesses, the base register of the generated
          // access will contain the base of the address in AE.
          end_base = make_reg_addr (ae.base_reg ());

          // The index reg will contain the rest (index*scale+disp).
          end_index =
            non_mod_addr (invalid_regno, ae.index_reg (),
                          ae.scale (), ae.disp ());
        }

      // Get the costs for using this alternative.
      int alt_min_cost = alt->costs ();

      min_mod_cost_result base_mod_cost =
        find_min_mod_cost (end_base,
                           alt_ae.disp_min (), alt_ae.disp_max (),
                           alt_ae.type (), dlg);

      if (base_mod_cost.cost == infinite_costs)
        continue;

      alt_min_cost += base_mod_cost.cost;

      min_mod_cost_result index_mod_cost;

      if (alt_ae.has_index_reg ())
        {
          index_mod_cost =
            find_min_mod_cost (end_index, 0, 0, alt_ae.type (), dlg);
          if (index_mod_cost.cost == infinite_costs)
            continue;

          alt_min_cost += index_mod_cost.cost;
        }

      // Calculate the costs of the next access when this alternative is used.
      // This is done by inserting the address modifications of this alt into the
      // sequence, calling gen_min_mod on the next access and then removing the
      // inserted address mods.
      if (next_acc != end ())
        {
          mod_tracker tracker;
          gen_mod_for_alt (*alt,
                           base_mod_cost.min_start_addr,
                           index_mod_cost.min_start_addr,
                           end_base, end_index,
                           acc, &tracker, dlg);

          int next_cost = gen_min_mod (next_acc, dlg, false);
          if (next_cost == infinite_costs)
            continue;
          alt_min_cost += next_cost;

          tracker.reset_changes (*this);
        }

      if (alt_min_cost < min_cost)
        {
          min_cost = alt_min_cost;
          min_start_base = base_mod_cost.min_start_addr;
          min_end_base = end_base;
          if (alt_ae.has_index_reg ())
            {
              min_start_index = index_mod_cost.min_start_addr;
              min_end_index = end_index;
            }
          min_alternative = alt;
        }
    }

  gcc_assert (min_cost != infinite_costs);

  if (record_in_sequence)
    {
      log_msg ("min alternative: %d  min costs = %d\n",
               (int)(min_alternative - acc->begin_alternatives ()),
               min_cost);
      gen_mod_for_alt (*min_alternative,
                       min_start_base, min_start_index,
                       min_end_base, min_end_index,
                       acc, NULL, dlg);
    }

  return min_cost;
}

// Generate the address modifications needed to arrive at END_BASE and
// END_INDEX from START_BASE/INDEX when using ALTERNATIVE as the access
// alternative.  Record any changes to the sequence in MOD_TRACKER.
void sh_ams::access_sequence::
gen_mod_for_alt
(access::alternative& alternative,
 access* start_base, access* start_index,
 const addr_expr& end_base, const addr_expr& end_index,
 access_sequence::iterator acc,
 mod_tracker *mod_tracker,
 delegate& dlg)
{
  // Insert the modifications needed to arrive at the address
  // in the base reg.
  mod_addr_result base_insert_result =
    try_modify_addr (start_base, end_base,
                     alternative.address ().disp_min (),
                     alternative.address ().disp_max (),
                     alternative.address ().type (),
                     &acc, mod_tracker, dlg);

  const addr_expr& ae = acc->address ();
  addr_expr new_addr_expr;
  if (alternative.address ().has_no_index_reg ())
    {
      disp_t disp = ae.disp () - base_insert_result.addr_disp;
      new_addr_expr = non_mod_addr (base_insert_result.addr_reg,
                                    invalid_regno, 1, disp);
    }
  else
    {
      // Insert the modifications needed to arrive at the address
      // in the index reg.
      mod_addr_result index_insert_result =
        try_modify_addr (start_index, end_index,
                         0, 0,
                         alternative.address ().type (),
                         &acc, mod_tracker, dlg);
      new_addr_expr = non_mod_addr (base_insert_result.addr_reg,
                                    index_insert_result.addr_reg, 1, 0);
    }

  if (alternative.address ().type () == pre_mod)
    new_addr_expr = pre_mod_addr (new_addr_expr.base_reg (),
                                  alternative.address ().disp_min ());
  else if (alternative.address ().type () == post_mod)
    new_addr_expr = post_mod_addr (new_addr_expr.base_reg (),
                                   alternative.address ().disp_min ());

  if (acc->access_type () == reg_value)
    // If this is a reg_value access, set the address reg to the register
    // that now holds its original value.
    add_reg_mod (acc, new_addr_expr, acc->address (),
                 NULL, acc->address_reg (), 0);
  else
    // Update the original_addr_expr of the access with the
    // alternative.
    acc->update_original_address (alternative.costs (), new_addr_expr);
}

// Write the sequence into the insn stream.
void sh_ams::access_sequence::update_insn_stream ()
{
  log_msg ("Updating insn list\n");

  // Remove all the insns that are originally used to arrive at
  // the required addresses.
  // FIXME: The address regs might be used outside of accesses, so
  // disable this until AMS can handle reg-uses.
  //for (std::vector<rtx_insn*>::iterator it = reg_mod_insns ().begin ();
  //     it != reg_mod_insns ().end (); ++it)
  //  set_insn_deleted (*it);
  //reg_mod_insns ().clear ();

  bool sequence_started = false;
  rtx_insn* last_insn = NULL;

  for (access_sequence::iterator accs = begin (); accs != end (); ++accs)
    {
      if (accs->access_type () == reg_mod)
        {
          // Skip accesses with unknown values and the ones that
          // don't modify anything.
          if (accs->original_address ().is_invalid ())
	    {
	      log_msg ("access original address not valid\n");
	      continue;
	    }
          if (accs->original_address ().base_reg () == accs->address_reg ()
              && accs->original_address ().has_no_index_reg ()
              && accs->original_address ().has_no_disp ())
	    {
	      log_msg ("skipping reg mod expr\n");
	      log_addr_expr (accs->original_address ());
	      log_msg ("\n");
	      continue;
	    }

          if (!sequence_started)
            {
              start_sequence ();
              sequence_started = true;
            }

          // Insert an address modifying insn according to the reg-mod access.

          rtx new_val;

          if (accs->original_address ().has_no_base_reg ()
              && accs->original_address ().has_no_index_reg ())
	    {
	      new_val = GEN_INT (accs->original_address ().disp ());
	      log_msg ("reg mod new val (1) = ");
	      log_rtx (new_val);
	      log_msg ("\n");
	    }
          else if (accs->original_address ().has_index_reg ())
            {
              bool subtract = (accs->original_address ().has_base_reg ()
                               && accs->original_address ().scale () == -1);
	      rtx index = subtract ? accs->original_address ().index_reg ()
                : expand_mult (accs->original_address ().index_reg (),
                               accs->original_address ().scale ());

              if (accs->original_address ().has_no_base_reg ())
                new_val = index;
              else if (subtract)
                new_val = expand_minus (accs->original_address ().base_reg (),
                                        index);
              else
		new_val = expand_plus (accs->original_address ().base_reg (),
				       index);
              log_msg ("reg mod new val (2) = ");
              log_rtx (new_val);
              log_msg ("\n");
            }
          else
            {
              new_val = accs->original_address ().base_reg ();
              log_msg ("reg mod new val (3) = ");
              log_rtx (new_val);
              log_msg ("\n");
            }

          new_val = expand_plus (new_val, accs->original_address ().disp ());

          accs->update_insn (emit_move_insn (accs->address_reg (), new_val));
          reg_mod_insns ().push_back (accs->insn ());
        }
      else if (accs->access_type () == reg_use)
        {
          gcc_assert (accs->original_address ().has_base_reg ());
          accs->update_used_reg (accs->original_address ().base_reg ());
        }
      else if (accs->access_type () == load || accs->access_type () == store)
        {
          // Update the access rtx to reflect ORIGINAL_ADDRESS.

          rtx new_addr = accs->original_address ().base_reg ();
          log_msg ("new addr (1) = ");
          log_rtx (new_addr);
          log_msg ("\n");

          // Add (possibly scaled) index reg.
          if (accs->original_address ().has_index_reg ())
            {
	      rtx index = accs->original_address ().index_reg ();
	      int scale = accs->original_address ().scale ();

	      if (scale != 1)
	        {
		  int shiftval = exact_log2 (scale);
		  index = shiftval != -1
			  ? gen_rtx_ASHIFT (Pmode, index, GEN_INT (shiftval))
			  : gen_rtx_MULT (Pmode, index, GEN_INT (scale));
		}

	      new_addr = gen_rtx_PLUS (Pmode, new_addr, index);

	      log_msg ("new addr (2) = ");
	      log_rtx (new_addr);
	      log_msg ("\n");
            }

          // Surround with POST/PRE_INC/DEC if ORIGINAL_ADDRESS is an
          // auto_mod type.
          if (accs->original_address ().type () == pre_mod)
            {
	      new_addr = accs->original_address ().disp () > 0
			 ? gen_rtx_PRE_INC (Pmode, new_addr)
			 : gen_rtx_PRE_DEC (Pmode, new_addr);

	      log_msg ("new addr (3) = ");
	      log_rtx (new_addr);
	      log_msg ("\n");
            }
          else if (accs->original_address ().type () == post_mod)
            {
	      new_addr = accs->original_address ().disp () > 0
			 ? gen_rtx_POST_INC (Pmode, new_addr)
			 : gen_rtx_POST_DEC (Pmode, new_addr);

	      log_msg ("new addr (4) = ");
	      log_rtx (new_addr);
	      log_msg ("\n");
            }
          else if (accs->original_address ().has_disp ())
            {
              // Add constant displacement.
	      new_addr =
		  gen_rtx_PLUS (Pmode, new_addr,
				GEN_INT (accs->original_address ().disp ()));

	      log_msg ("new addr (5) = ");
	      log_rtx (new_addr);
	      log_msg ("\n");
	    }

	  log_msg ("new addr (6) = ");
	  log_rtx (new_addr);
	  log_msg ("\n");

          bool mem_update_ok = accs->update_mem (new_addr);
          gcc_assert (mem_update_ok);

          sh_check_add_incdec_notes (accs->insn ());
        }

      access_sequence::iterator next_acc = accs;
      ++next_acc;
      if (accs->access_type () == load || accs->access_type () == store
          || accs->access_type () == reg_use || next_acc == end ())
        {
          if (accs->insn ())
            last_insn = accs->insn ();
          if (sequence_started)
            {
              rtx_insn* new_insns = get_insns ();
              end_sequence ();
              sequence_started = false;

              rtx emit_before_insn = (next_acc == end ()) ? NEXT_INSN (last_insn)
                                                          : accs->insn ();

              log_msg ("emitting new insns = \n");
              log_rtx (new_insns);
              log_msg ("\nbefore insn\n");
              log_insn (emit_before_insn);
              log_msg ("\n");
              emit_insn_before (new_insns, emit_before_insn);
            }
        }

    }
}

// Get the total cost of using this access sequence.
int sh_ams::access_sequence::cost (void) const
{
  int cost = 0;
  for (access_sequence::const_iterator accs = begin ();
       accs != end (); ++accs)
    cost += accs->cost ();
  return cost;
}

// Recalculate the cost of the accesses in the sequence.
void sh_ams::access_sequence::update_cost (delegate& dlg)
{
  for (access_sequence::iterator accs = begin ();
       accs != end (); ++accs)
    {
      if (accs->access_type () == load || accs->access_type () == store)
        {
          // Find the alternative that the access uses and update
          // its cost accordingly.
          for (const sh_ams::access::alternative* alt
                 = accs->begin_alternatives (); ; ++alt)
            {
              if (accs->matches_alternative (alt))
                {
                  accs->update_cost (alt->costs ());
                  break;
                }
              if (alt == accs->end_alternatives ())
                gcc_unreachable ();
            }
        }
      else if (accs->access_type () == reg_mod
               && !accs->original_address ().is_invalid ())
        {
          int cost = 0;
          const addr_expr &ae = accs->original_address ();

          // Scaling costs
          if (ae.has_no_base_reg () && ae.has_index_reg ()
              && ae.scale () != 1)
            cost += dlg.addr_reg_scale_cost (ae.index_reg (), ae.scale ());

          // Costs for adding or subtracting another reg
          else if (ae.has_no_disp () && std::abs (ae.scale ()) == 1
                   && ae.has_base_reg () && ae.has_index_reg ())
            cost += dlg.addr_reg_plus_reg_cost (ae.index_reg (), ae.base_reg ());

          // Constant displacement costs
          else if (ae.has_base_reg () && ae.has_no_index_reg ()
                   && ae.has_disp ())
            cost += dlg.addr_reg_disp_cost (ae.base_reg (), ae.disp ());

          // If none of the previous branches were taken, the reg_mod access
          // is either a (reg <- reg) or a (reg <- constant) copy, and doesn't
          // have any modification cost.
          else
            {
              gcc_assert ((ae.has_no_base_reg () && ae.has_no_index_reg ())
                          || (ae.has_base_reg () && ae.has_no_index_reg ()
                              && ae.has_no_disp ()));
              cost = 0;
            }

          // Cloning costs
          cost += get_clone_cost (*accs, dlg);

          accs->update_cost (cost);
        }
    }

  // Mark the reg_mod accesses as "unused" again (except for the
  // reg <- constant copies, which are always marked used).
  for (access_sequence::iterator accs = begin ();
       accs != end (); ++accs)
    {
      if (accs->original_address ().has_base_reg ()
          || accs->original_address ().has_index_reg ())
        accs->reset_used ();
    }
}

// Get the cloning costs associated with ACC, if any.
int sh_ams::access_sequence::get_clone_cost (access &acc, delegate& dlg)
{
  rtx reused_reg = NULL;
  if (acc.address ().has_base_reg ())
    reused_reg = acc.address ().base_reg ();
  else if (acc.address ().has_index_reg ())
    reused_reg = acc.address ().index_reg ();
  else return 0;

  // There's no cloning cost for accesses that set the reg to itself.
  if (reused_reg == acc.address_reg ()) return 0;

  for (access_sequence::iterator prev_accs = begin (); ; ++prev_accs)
    {
      if (prev_accs->access_type () == reg_mod
          && prev_accs->address_reg () == reused_reg)
        {
          // If the reused reg is already used by another access,
          // we'll have to clone it.
          if (prev_accs->is_used ())
            return  dlg.addr_reg_clone_cost (reused_reg);

          // Otherwise, we can use it without any cloning penalty.
          prev_accs->set_used ();
          return 0;
        }
    }
  gcc_unreachable ();
}

// Find the cheapest way END_ADDR can be arrived at from one of the addresses
// in the sequence.
// Return the reg_value that can be changed into END_ADDR with the least cost
// and the actual cost.
sh_ams::access_sequence::min_mod_cost_result
sh_ams::access_sequence
::find_min_mod_cost (const addr_expr& end_addr,
		     disp_t disp_min, disp_t disp_max,
                     addr_type_t addr_type, delegate& dlg)
{
  int min_cost = infinite_costs;
  access* min_start_addr = NULL;

  for (access_sequence::iterator it = begin (); it != end (); ++it)
    {
      if (it->access_type () != reg_mod || it->address ().is_invalid ())
        continue;

      int cost = try_modify_addr (&(*it), end_addr,
                                  disp_min, disp_max, addr_type, dlg).cost;

      if (cost < min_cost)
        {
          min_cost = cost;
          min_start_addr = &(*it);
        }
    }

  // If the end addr only has a constant displacement, try loading it into
  // the reg directly.
  if (end_addr.has_no_base_reg () && end_addr.has_no_index_reg ()
      && end_addr.has_disp ())
    {
      rtx const_reg = gen_reg_rtx (Pmode);
      add_reg_mod (begin (),
                   make_const_addr (end_addr.disp ()),
                   make_const_addr (end_addr.disp ()),
                   NULL, const_reg, 0);
      begin ()->set_used ();
      int cost = try_modify_addr (&(*begin ()), end_addr,
                                  disp_min, disp_max, addr_type, dlg).cost;
      if (cost < min_cost)
        {
          min_cost = cost;
          min_start_addr = &(*begin ());
        }
      // If this doesn't reduce the costs, remove the newly added
      // (reg <- const) copy.
      else pop_front ();
    }

  return min_mod_cost_result (min_cost, min_start_addr);
}

// Try to find address modifications that change the address in START_ADDR
// into END_ADDR.  If ACCESS_PLACE is not NULL, insert the generated reg_mod
// accesses into the sequence behind ACCESS_PLACE and record the sequence
// modifications in MOD_TRACKER (if it's not NULL).
// DISP_MIN and DISP_MAX shows the range of displacement that can be added to
// the address during the access (or after it, in case ADDR_TYPE is POST_MOD).
// If they are not zero, the final displacement of the generated address doesn't
// have to match the displacement of END_ADDR exactly.  Instead, it must be in
// the range [end_addr.disp ()+disp_min, end_addr.disp ()+disp_max].
// Return the total cost of the modifications (or INFINITE_COSTS if no
// suitable modifications have been found), the register in which the final
// address is stored (in case reg_mod accesses are inserted) and the constant
// displacement of the final address.
sh_ams::access_sequence::mod_addr_result
sh_ams::access_sequence::
try_modify_addr
(access* start_addr, const addr_expr& end_addr,
 disp_t disp_min, disp_t disp_max, addr_type_t addr_type,
 access_sequence::iterator *access_place,
 mod_tracker *mod_tracker,
 delegate& dlg)
{
  access_sequence::iterator ins_place;
  rtx new_reg = start_addr->address_reg ();
  int cost = start_addr->is_used ()
            ? dlg.addr_reg_clone_cost (start_addr->address_reg ()) : 0;
  int prev_cost = 0;
  rtx final_addr_regno = access_place
                        ? start_addr->address_reg () : invalid_regno;

  // Canonicalize the start and end addresses by converting
  // addresses of the form base+disp into index*1+disp.
  addr_expr c_start_addr = start_addr->address ();
  addr_expr c_end_addr = end_addr;
  if (c_start_addr.has_no_index_reg ())
    c_start_addr =
      non_mod_addr (invalid_regno, c_start_addr.base_reg (), 1,
                    c_start_addr.disp ());
  if (c_end_addr.has_no_index_reg ())
    c_end_addr =
      non_mod_addr (invalid_regno, c_end_addr.base_reg (), 1,
                    c_end_addr.disp ());

  // If one of the addresses has the form base+index*1, it
  // might be better to switch its base and index reg.
  if (c_start_addr.index_reg () == c_end_addr.base_reg ())
    {
      if (c_end_addr.has_base_reg ()
          && c_end_addr.has_index_reg () && c_end_addr.scale () == 1)
        {
          c_end_addr = non_mod_addr (c_end_addr.index_reg (),
                                     c_end_addr.base_reg (),
                                     1, c_end_addr.disp ());
        }
      else if (c_start_addr.has_base_reg ()
               && c_start_addr.has_index_reg () && c_start_addr.scale () == 1)
        {
          c_start_addr = non_mod_addr (c_start_addr.index_reg (),
                                       c_start_addr.base_reg (),
                                       1, c_start_addr.disp ());
        }
    }

  // If the start address has a base reg, and it's different
  // from that of the end address, give up.
  if (c_start_addr.has_base_reg ()
      && c_start_addr.base_reg () != c_end_addr.base_reg ())
    return mod_addr_result (infinite_costs, invalid_regno, 0);

  // Same for index regs, unless we can get to the end address
  // by subtracting.
  if (c_start_addr.index_reg () != c_end_addr.index_reg ())
    {
      if (!(c_start_addr.has_no_base_reg ()
            && c_end_addr.has_index_reg ()
            && c_start_addr.index_reg () == c_end_addr.base_reg ()
            && c_start_addr.scale () == 1
            && c_end_addr.scale () == -1))
        return mod_addr_result (infinite_costs, invalid_regno, 0);
    }

  // Add scaling.
  if (c_start_addr.has_index_reg ()
      && c_start_addr.index_reg () == c_end_addr.index_reg ()
      && c_start_addr.scale () != c_end_addr.scale ())
    {
      // We can't scale if the address has displacement or a base reg.
      if (c_start_addr.has_disp () || c_start_addr.has_base_reg ())
        return mod_addr_result (infinite_costs, invalid_regno, 0);

      // We can only scale by integers.
      if (c_end_addr.scale () % c_start_addr.scale () != 0)
        return mod_addr_result (infinite_costs, invalid_regno, 0);

      scale_t scale = c_end_addr.scale () / c_start_addr.scale ();
      c_start_addr = non_mod_addr (invalid_regno, c_start_addr.index_reg (),
                                   c_end_addr.scale (), 0);
      cost += dlg.addr_reg_scale_cost (start_addr->address_reg (), scale);
      if (access_place)
        {
          if (!start_addr->is_used ())
            {
              start_addr->set_used ();
              if (mod_tracker)
                mod_tracker->use_changed_accs ().push_back (start_addr);
            }

          new_reg = gen_reg_rtx (Pmode);
          start_addr = &add_reg_mod (
			   *access_place,
			   non_mod_addr (invalid_regno,
					 start_addr->address_reg (), scale, 0),
                           c_start_addr, NULL, new_reg, cost - prev_cost);
          final_addr_regno = new_reg;

          if (mod_tracker)
            {
              ins_place =  *access_place;
              --ins_place;
              mod_tracker->inserted_accs ().push_back (ins_place);
            }
        }
      prev_cost = cost;
    }

  // Try subtracting regs.
  if (c_start_addr.has_no_base_reg ()
      && c_end_addr.has_index_reg ()
      && c_start_addr.index_reg () == c_end_addr.base_reg ()
      && c_start_addr.scale () == 1
      && c_end_addr.scale () == -1)
    {
      c_start_addr = non_mod_addr (c_start_addr.index_reg (),
                                   c_end_addr.index_reg (),
                                   -1,
                                   c_start_addr.disp ());
      cost += dlg.addr_reg_plus_reg_cost (start_addr->address_reg (),
                                          c_end_addr.index_reg ());
      if (access_place)
        {
          if (!start_addr->is_used ())
            {
              start_addr->set_used ();
              if (mod_tracker)
                mod_tracker->use_changed_accs ().push_back (start_addr);
            }
          new_reg = gen_reg_rtx (Pmode);
          start_addr = &add_reg_mod (
                            *access_place,
                            non_mod_addr (start_addr->address_reg (),
                                          c_end_addr.index_reg (),
                                          -1, 0),
                            c_start_addr, NULL, new_reg, cost - prev_cost);
          final_addr_regno = new_reg;

          if (mod_tracker)
            {
              ins_place =  *access_place;
              --ins_place;
              mod_tracker->inserted_accs ().push_back (ins_place);
            }
        }
      prev_cost = cost;
    }

  // Add missing base reg.
  if (c_start_addr.has_no_base_reg () && c_end_addr.has_base_reg ())
    {
      c_start_addr = non_mod_addr (c_end_addr.base_reg (),
                                   c_start_addr.index_reg (),
                                   c_start_addr.scale (),
                                   c_start_addr.disp ());
      cost += dlg.addr_reg_plus_reg_cost (start_addr->address_reg (),
                                          c_end_addr.base_reg ());
      if (access_place)
        {
          if (!start_addr->is_used ())
            {
              start_addr->set_used ();
              if (mod_tracker)
                mod_tracker->use_changed_accs ().push_back (start_addr);
            }
          new_reg = gen_reg_rtx (Pmode);
          start_addr = &add_reg_mod (
			    *access_place,
			    non_mod_addr (c_start_addr.base_reg (),
					  start_addr->address_reg (), 1, 0),
			    c_start_addr, NULL, new_reg, cost - prev_cost);
          final_addr_regno = new_reg;

          if (mod_tracker)
            {
              ins_place =  *access_place;
              --ins_place;
              mod_tracker->inserted_accs ().push_back (ins_place);
            }
        }
      prev_cost = cost;
    }

  // Set auto-inc/dec displacement that's added to the base reg.
  disp_t auto_mod_disp = 0;
  if (addr_type != non_mod)
    {
      gcc_assert (disp_min == disp_max);
      auto_mod_disp = disp_min;

      // If the base is only modified after the access, the
      // displacement range should be considered to be zero.
      if (addr_type == post_mod)
          disp_min = disp_max = 0;
    }

  // Add displacement.
  if (c_start_addr.disp () + disp_min > c_end_addr.disp ()
      || c_start_addr.disp () + disp_max < c_end_addr.disp ())
    {
      // Make the displacement as small as possible, since
      // adding smaller constants often costs less.
      disp_t disp = c_end_addr.disp () - c_start_addr.disp () - disp_min;
      disp_t alt_disp = c_end_addr.disp () - c_start_addr.disp () - disp_max;
      if (std::abs (alt_disp) < std::abs (disp)) disp = alt_disp;

      c_start_addr = non_mod_addr (c_end_addr.base_reg (),
                                   c_start_addr.index_reg (),
                                   c_start_addr.scale (),
                                   c_start_addr.disp () + disp);
      cost += dlg.addr_reg_disp_cost (start_addr->address_reg (), disp);
      if (access_place)
        {
          if (!start_addr->is_used ())
            {
              start_addr->set_used ();
              if (mod_tracker)
                mod_tracker->use_changed_accs ().push_back (start_addr);
            }
          new_reg = gen_reg_rtx (Pmode);
          start_addr = &add_reg_mod (
			    *access_place,
			    non_mod_addr (start_addr->address_reg (),
					  invalid_regno, 1, disp),
			    c_start_addr, NULL, new_reg, cost - prev_cost);
          final_addr_regno = new_reg;

          if (mod_tracker)
            {
              ins_place =  *access_place;
              --ins_place;
              mod_tracker->inserted_accs ().push_back (ins_place);
            }
        }
      prev_cost = cost;
    }

  // For auto-mod accesses, copy the base reg into a new pseudo that will
  // be used by the auto-mod access.  This way, both the pre-access and
  // post-access version of the base reg can be reused by later accesses.
  // Do the same for constant displacement addresses so that there's no
  // cloning penalty for reusing the constant address in another access.
  if (addr_type != non_mod
      || (c_end_addr.has_no_base_reg () && c_end_addr.has_no_index_reg ()))
    {
      c_start_addr = non_mod_addr (c_end_addr.base_reg (),
                                   c_start_addr.index_reg (),
                                   c_start_addr.scale (),
                                   c_start_addr.disp () + auto_mod_disp);
      if (access_place)
        {
          if (!start_addr->is_used ())
            {
              start_addr->set_used ();
              if (mod_tracker)
                mod_tracker->use_changed_accs ().push_back (start_addr);
            }
          rtx pre_mod_reg = new_reg;
          new_reg = gen_reg_rtx (Pmode);
          start_addr = &add_reg_mod (*access_place, make_reg_addr (pre_mod_reg),
				     c_start_addr, NULL, new_reg,
                                     cost - prev_cost);
          final_addr_regno = new_reg;

          if (mod_tracker)
            {
              ins_place =  *access_place;
              --ins_place;
              mod_tracker->inserted_accs ().push_back (ins_place);
            }
          prev_cost = cost;
        }
    }

  return mod_addr_result (cost, final_addr_regno, c_start_addr.disp ());
}

sh_ams::access_sequence::mod_addr_result
sh_ams::access_sequence::try_modify_addr
(access* start_addr, const addr_expr& end_addr,
 disp_t disp_min, disp_t disp_max, addr_type_t addr_type,
 delegate& dlg)
{
  return try_modify_addr (start_addr, end_addr, disp_min, disp_max,
                          addr_type, NULL, NULL, dlg);
}

// Find all uses of the address registers that aren't mem loads/stores
// or address modifications, and add them to the sequence
// as reg_use accesses.
// Also find the values of all address registers that are still alive
// after the sequence's last insn, and add them to the sequence as
// reg_value accesses.
void sh_ams::access_sequence::find_reg_uses_and_values (basic_block bb)
{
  hash_map<rtx, access*> addr_regs;
  std::vector<rtx*> used_regs;
  access_sequence::iterator as_it = begin ();
  rtx_insn* i;
  FOR_BB_INSNS (bb, i)
    {
      if (!INSN_P (i) || !NONDEBUG_INSN_P (i))
        continue;

      // Keep track of the values of the address regs set before
      // the current insn.
      while (as_it != end () && (!as_it->insn () || as_it->insn () == i))
        {
          if (as_it->access_type () == reg_mod)
            addr_regs.put (as_it->address_reg (), &(*as_it));
          ++as_it;
        }

      used_regs.clear ();
      find_addr_regs (PATTERN (i), std::back_inserter (used_regs), addr_regs);

      for (std::vector<rtx*>::iterator it = used_regs.begin ();
           it != used_regs.end (); ++it)
        {
          rtx* reg_ref = *it;
          access *addr_reg = *addr_regs.get (*reg_ref);
          add_reg_use (as_it,
                       make_reg_addr (*reg_ref),
                       addr_reg->address (),
                       addr_reg->addr_rtx (),
                       reg_ref, i);
        }

      // Remove any address reg that's no longer alive after this insn.
      for (rtx note = REG_NOTES (i); note; note = XEXP (note, 1))
        {
          if (REG_NOTE_KIND (note) == REG_DEAD
              && addr_regs.get (XEXP (note, 0)))
            addr_regs.remove (XEXP (note, 0));
      }
    }

  // Add reg_value type accesses that force the addr regs to keep
  // their original values at the end of the sequence, even after new
  // address modifications are generated.
  for (hash_map<rtx, access*>::iterator it = addr_regs.begin ();
       it != addr_regs.end (); ++it)
    {
      access* acc = (*it).second;

      // Don't add the addr reg if it wasn't modified during the access.
      if (!acc->address ().is_invalid ()
          && !(acc->address ().has_no_index_reg ()
               && acc->address ().has_no_disp ()
               && acc->address ().base_reg () == acc->address_reg ()))
        push_back (access (acc->address_reg (), acc->address ()));
    }
}

// Find the address register rtx-es in X that were used for
// something other than address calculation and memory access,
// and add them to OUT.
template <typename OutputIterator> void
sh_ams::find_addr_regs (rtx& x, OutputIterator out,
                        hash_map<rtx, access*> &addr_regs)
{
  switch (GET_CODE (x))
    {
    case REG:
      if (addr_regs.get (x))
        *out++ = &x;
      break;
    case MEM:
      // Don't add regs used in memory accesses.
      break;
    case PARALLEL:
      for (int i = 0; i < XVECLEN (x, 0); i++)
        find_addr_regs (XVECEXP (x, 0, i), out, addr_regs);
      break;
    case SET:

      // If SET_DEST is an address reg, the regs in SET_SRC are
      // used for address calculation, so don't add them.
      if (!addr_regs.get (SET_DEST (x)))
        find_addr_regs (SET_SRC (x), out, addr_regs);
      break;
    default:
      if (UNARY_P (x) || ARITHMETIC_P (x))
        {
          for (int i = 0; i < GET_RTX_LENGTH (GET_CODE (x)); i++)
            find_addr_regs (XEXP (x, i), out, addr_regs);
        }
      break;
    }
}

unsigned int sh_ams::execute (function* fun)
{
  log_msg ("sh-ams pass\n");

//  df_set_flags (DF_DEFER_INSN_RESCAN); // needed?

  df_note_add_problem ();
  df_analyze ();

  std::vector<std::pair<rtx*, access_type_t> > mems;

  basic_block bb;
  FOR_EACH_BB_FN (bb, fun)
    {
      rtx_insn* i;

      log_msg ("BB #%d:\n", bb->index);
      log_msg ("insns:\n");
      FOR_BB_INSNS (bb, i)
        {
          if (!INSN_P (i) || !NONDEBUG_INSN_P (i))
            continue;

          log_insn (i);
        }
      log_msg ("---\n");

      // Construct the access sequence from the access insns.
      access_sequence as;
      FOR_BB_INSNS (bb, i)
        {
          if (!INSN_P (i) || !NONDEBUG_INSN_P (i))
            continue;

          // Search for memory accesses inside the current insn
          // and add them to the address sequence.
          mems.clear ();
          find_mem_accesses (PATTERN (i), std::back_inserter (mems));

          for (std::vector<std::pair<rtx*, access_type_t> >
	       ::reverse_iterator m = mems.rbegin (); m != mems.rend (); ++m)
	    as.add_mem_access (i, m->first, m->second);
         }

      as.find_reg_uses_and_values (bb);

      for (access_sequence::iterator it = as.first_access_to_optimize ();
           it != as.end (); it = as.next_access_to_optimize (it))
        it->update_alternatives (m_delegate);

      as.update_cost (m_delegate);
      int original_cost = as.cost ();

      log_msg ("Access sequence contents:\n\n");
      for (access_sequence::const_iterator it = as.begin ();
	   it != as.end (); ++it)
	{
	  log_access (*it, false);
	  log_msg ("\n-----\n");
	}
      log_msg ("\nTotal cost: %d\n", original_cost);

      log_msg ("\n\n");

      // Fill the sequence's REG_MOD_INSNS with the insns of the reg_mod accesses
      // that can be removed.
      for (access_sequence::iterator it = as.begin ();
	   it != as.end (); ++it)
        {
          if (it->removable ())
            access_sequence::reg_mod_insns ().push_back (it->insn ());
        }

      as.gen_address_mod (m_delegate);

      int new_cost = as.cost ();

      log_msg ("\nAccess sequence contents after address mod generation:\n\n");
      for (access_sequence::const_iterator it = as.begin ();
	   it != as.end (); ++it)
	{
	  log_access (*it, false);
	  log_msg ("\n-----\n");
	}
      log_msg ("\nTotal cost: %d\n", new_cost);

      if (new_cost < original_cost)
        as.update_insn_stream ();
      else
        log_msg ("Insn list not modified\n");

      log_msg ("\n\n");
    }

  log_return (0, "\n\n");
}
