
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
log_access (const sh_ams::access& a)
{
  if (dump_file == NULL)
    return;

  if (a.access_mode () == sh_ams::load)
    log_msg ("load ");
  else if (a.access_mode () == sh_ams::store)
    log_msg ("store");
  else if (a.access_mode () == sh_ams::reg_mod)
    {
      log_msg ("reg_mod:\n  ");
      log_rtx (a.modified_reg ());
      log_msg (" set\n");
    }
  else
    gcc_unreachable ();

  if (a.access_mode () == sh_ams::load || a.access_mode () == sh_ams::store)
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

  if (a.access_mode () == sh_ams::load || a.access_mode () == sh_ams::store)
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

} // anonymous namespace


sh_ams::access::access
(rtx_insn* insn, rtx* mem, access_mode_t access_mode,
 addr_expr original_addr_expr, addr_expr addr_expr, int cost)
{
  m_access_mode = access_mode;
  m_machine_mode = GET_MODE (*mem);
  m_addr_space = MEM_ADDR_SPACE (*mem);
  m_cost = cost;
  m_insn = insn;
  m_mem_ref = mem;
  m_original_addr_expr = original_addr_expr;
  m_addr_expr = addr_expr;
  m_addr_rtx = NULL_RTX;
  m_mod_reg = NULL_RTX;
  m_used = false;
  m_alternatives_count = 0;
}

// Constructor for reg_mod accesses.
sh_ams::access::access
(rtx_insn* insn, addr_expr original_addr_expr, addr_expr addr_expr,
 rtx addr_rtx, rtx mod_reg, int cost)
{
  m_access_mode = reg_mod;
  m_cost = cost;
  m_insn = insn;
  m_original_addr_expr = original_addr_expr;
  m_addr_expr =  addr_expr;
  m_addr_rtx =  addr_rtx;
  m_mod_reg = mod_reg;
  m_used = false;
  m_alternatives_count = 0;
}

// Add a normal access to the end of the access sequence.
sh_ams::access&
sh_ams::access_sequence::add_new_access
(rtx_insn* insn, rtx* mem,
 access_mode_t access_mode)
{
  machine_mode m_mode = GET_MODE (*mem);
  // Create an ADDR_EXPR struct from the address expression of MEM.
  addr_expr original_expr =
    extract_addr_expr ((XEXP (*mem, 0)), insn, insn, m_mode, *this, false, false);
  addr_expr expr =
    extract_addr_expr ((XEXP (*mem, 0)), insn, insn,
                       m_mode, *this, true, true);
  push_back (access (insn, mem, access_mode, original_expr, expr));
  return back ();
}

// Create a reg_mod access and add it to the access sequence.
// This function traverses the insn list backwards starting from INSN to
// find the correct place inside AS where the access needs to be inserted.
sh_ams::access&
sh_ams::access_sequence::add_reg_mod_access
(rtx_insn* insn, addr_expr original_addr_expr, addr_expr addr_expr,
 rtx addr_rtx, rtx_insn* mod_insn, rtx reg)
{
  if (empty ())
    {
      push_back (access (mod_insn, original_addr_expr, addr_expr,
                         addr_rtx, reg));
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
          if (as_it->access_mode () == reg_mod
              && as_it->modified_reg () == reg)
            return *as_it;
        }

      push_front (access (mod_insn, original_addr_expr, addr_expr,
                          addr_rtx, reg));
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
          if (as_it->access_mode () == reg_mod
              && as_it->insn () == mod_insn && as_it->modified_reg () == reg
              && as_it->address ().base_reg () == addr_expr.base_reg ())
            return *as_it;

        }
      if (INSN_UID (i) == INSN_UID (mod_insn))
        {
          // We found mod_insn inside the insn list, so we know where to
          // insert the access.
          insert (as_it.base (),
                  access (mod_insn, original_addr_expr, addr_expr,
                          addr_rtx, reg));
          return *as_it;
        }
    }
  gcc_unreachable ();
}

sh_ams::access&
sh_ams::access_sequence::add_reg_mod_access
(rtx_insn* insn, addr_expr original_addr_expr, addr_expr addr_expr,
 rtx_insn* mod_insn, rtx reg)
{
  return add_reg_mod_access (insn, original_addr_expr, addr_expr,
                             NULL_RTX, mod_insn, reg);
}
sh_ams::access&
sh_ams::access_sequence::add_reg_mod_access
(rtx_insn* insn, rtx addr_rtx,
 rtx_insn* mod_insn, rtx reg)
{
  return add_reg_mod_access (insn, make_invalid_addr (), make_invalid_addr (),
                             addr_rtx, mod_insn, reg);
}
// Create a reg_mod access and place it before INSERT_BEFORE
// in the access sequence.
sh_ams::access&
sh_ams::access_sequence::add_reg_mod_access
(access_sequence::iterator insert_before,
 addr_expr original_addr_expr, addr_expr addr_expr,
 rtx_insn* mod_insn, rtx reg)
{
  insert (insert_before,
          access (mod_insn, original_addr_expr, addr_expr,
                  NULL_RTX, reg));
  return *(--insert_before);
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
  std::vector<std::pair<rtx*, access_mode_t> > mems;

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
          for (std::vector<std::pair<rtx*, access_mode_t> >
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
// (used as the start insn when calling add_reg_mod_access).
sh_ams::addr_expr
sh_ams::extract_addr_expr (rtx x, rtx_insn* insn, rtx_insn *root_insn,
			   machine_mode mem_mach_mode,
			   access_sequence& as,
                           bool expand, bool collect_mod_insns)
{
  addr_expr op0 = make_invalid_addr ();
  addr_expr op1 = make_invalid_addr ();
  disp_t disp, scale;
  rtx base_reg, index_reg;

  if (x == NULL_RTX) return make_invalid_addr ();

  enum rtx_code code = GET_CODE (x);

  // If X is an arithmetic operation, first create ADDR_EXPR structs
  // from its operands. These will later be combined into a single ADDR_EXPR.
  if (code == PLUS || code == MINUS || code == MULT || code == ASHIFT)
    {
      op0 = extract_addr_expr
        (XEXP (x, 0), insn, root_insn, mem_mach_mode, as,
         expand, collect_mod_insns);
      op1 = extract_addr_expr
        (XEXP (x, 1), insn, root_insn, mem_mach_mode, as,
         expand, collect_mod_insns);
      if (op0.is_invalid () || op1.is_invalid ())
        return make_invalid_addr ();
    }
  else if (code == NEG)
    {
      op1 = extract_addr_expr
        (XEXP (x, 0), insn, root_insn, mem_mach_mode, as,
         expand, collect_mod_insns);
      if (op1.is_invalid ())
        return op1;
    }

  // Auto-mod accesses found in the original insn list are changed into
  // non-modifying accesses by offseting their constant displacement, or by
  // using the modified expression directly in the case of PRE/POST_MODIFY.
  else if (GET_RTX_CLASS (code) == RTX_AUTOINC)
    {
      bool expanding_reg = (INSN_UID (insn) != INSN_UID (root_insn));

      switch (code)
        {

        // For post-mod accesses, the displacement is offset only when
        // tracing back the value of a register.  Otherwise, we're interested
        // in the value that the address reg has during the memory access,
        // which isn't modified at that point.
        case POST_DEC:
          disp = expanding_reg ? -GET_MODE_SIZE (mem_mach_mode) : 0;
          break;
        case POST_INC:
          disp = expanding_reg ? GET_MODE_SIZE (mem_mach_mode) : 0;
          break;
        case PRE_DEC:
          disp = -GET_MODE_SIZE (mem_mach_mode);
          break;
        case PRE_INC:
          disp = GET_MODE_SIZE (mem_mach_mode);
          break;
        case POST_MODIFY:
          return extract_addr_expr
            (XEXP (x, expanding_reg ? 1 : 0), insn, root_insn,
             mem_mach_mode, as, expand, collect_mod_insns);
        case PRE_MODIFY:
          return extract_addr_expr
            (XEXP (x, 1), insn, root_insn,
             mem_mach_mode, as, expand, collect_mod_insns);
        default:
          return make_invalid_addr ();
        }

      op1 = extract_addr_expr
        (XEXP (x, 0), insn, root_insn, mem_mach_mode, as,
         expand, collect_mod_insns);
      disp += op1.disp ();
      return non_mod_addr
        (op1.base_reg (), op1.index_reg (), op1.scale (), disp);
    }

  switch (code)
    {

    // For CONST_INT and REG, the set the base register or the displacement
    // to the appropriate value.
    case CONST_INT:
      return make_const_addr (INTVAL (x));

    case REG:
      if (expand)
        {

          // Find the expression that the register was last set to
          // and convert it to an addr_expr.
          rtx reg_value;
          rtx_insn *reg_mod_insn = NULL;
          rtx_insn* inserted_mod_insn
            = as.reg_mod_insns ().empty () ? NULL : as.reg_mod_insns ().back ();
          find_reg_value (x, insn, &reg_value, &reg_mod_insn);
          if (reg_value != NULL_RTX)
            {
              // Stop expanding the reg if we reach a hardreg -> pseudo reg
              // copy, or if the reg can't be expanded any further.
              if (REG_P (reg_value)
                  && (REGNO (reg_value) == REGNO (x)
                      || HARD_REGISTER_P (reg_value)))
                {
                  // Add a reg_mod access that sets the reg to itself.
                  // This makes it easier for the address modification
                  // generator to find all possible starting addresses.
                  as.add_reg_mod_access
                    (root_insn, make_reg_addr (x), make_reg_addr (x),
                     reg_mod_insn, x);
                  return make_reg_addr (x);
                }

                // For constant -> reg copies, add the reg to the
                // sequence as a reg_mod access.
                if (CONST_INT_P (reg_value))
                  {
                    access& const_access
                      = as.add_reg_mod_access
                      (root_insn,
                       make_const_addr (INTVAL (reg_value)),
                       make_const_addr (INTVAL (reg_value)),
                       NULL, x);

                    // Mark the access as used so that cloning costs are
                    // always added during address modification generation.
                    // This encourages the generator to reuse the base regs
                    // of previous constant accesses.
                    const_access.set_used ();
                  }
            }

          // Collect all the insns that are used to arrive at the address
          // into reg_mod_insns.  The content of this list is later used
          // to remove the original register modifying insns when updating
          // the insn stream.  Auto-mod insns don't need to be removed
          // because the mem accesses get changed during the update.
          if (collect_mod_insns
              && !find_reg_note (reg_mod_insn, REG_INC, NULL_RTX))
            {
              as.reg_mod_insns ().push_back (reg_mod_insn);

              // Keep track of where we inserted the insn in case
              // we might have to backtrack later.
              inserted_mod_insn = reg_mod_insn;
            }

          addr_expr reg_addr_expr = extract_addr_expr
            (reg_value, reg_mod_insn, root_insn,
             mem_mach_mode, as, true, collect_mod_insns);

          // If the expression is something AMS can't handle, use the original
          // reg instead, and add a reg_mod access to the access sequence.
          if (reg_addr_expr.is_invalid ())
            {
              as.add_reg_mod_access
                (root_insn, reg_value, reg_mod_insn, x);

              // Add an (rx = rx) reg_mod access to help the
              // address modification generator.
              as.add_reg_mod_access
                (root_insn, make_reg_addr (x), make_reg_addr (x),
                 reg_mod_insn, x);

              // Remove any insn that might have been inserted while
              // expanding this register.
              if (collect_mod_insns)
                {
                  if (inserted_mod_insn)
                    {
                      while (as.reg_mod_insns ().back () != inserted_mod_insn)
                        as.reg_mod_insns ().pop_back ();
                      as.reg_mod_insns ().pop_back ();
                    }
                  else as.reg_mod_insns ().clear ();
                }

              return make_reg_addr (x);
            }
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
      if (op1.index_reg () != invalid_regno && op1.scale () != -1)
        break;
      op1 = non_mod_addr
        (op1.index_reg (), op1.base_reg (), -op1.scale (), -op1.disp ());
      if (code == NEG) return op1;
    case PLUS:
      disp = op0.disp () + op1.disp ();
      index_reg = invalid_regno;
      scale = 0;

      // If the same reg is used in both addresses, try to
      // merge them into one reg.
      if (op0.base_reg () == op1.base_reg ())
        {
          if (op0.index_reg () == invalid_regno)
            {
              op1 = non_mod_addr (invalid_regno, op1.index_reg (),
                                  op1.scale (), op1.disp ());
              op0 = non_mod_addr (invalid_regno, op0.base_reg (),
                                  2, op0.disp ());
            }
          else if (op1.index_reg () == invalid_regno)
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
      if (op0.base_reg () == invalid_regno)
        base_reg = op1.base_reg ();
      else if (op1.base_reg () == invalid_regno)
        base_reg = op0.base_reg ();

      // Otherwise, one of the base regs becomes the index reg
      // (with scale = 1).
      else if (op0.index_reg () == invalid_regno
               && op1.index_reg () == invalid_regno)
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
          if (op0.index_reg () == invalid_regno)
            {
              index_reg = op1.index_reg ();
              scale = op1.scale ();
            }
          else if (op1.index_reg () == invalid_regno)
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
      if (op1.base_reg () == invalid_regno && op1.index_reg () == invalid_regno
          && op1.disp () >= 0)
        {
          disp_t mul = 1
            << op1.disp ();
          op1 = non_mod_addr (invalid_regno, invalid_regno, 0, mul);
        }
      else break;
    case MULT:

      // One of the operands must be a constant term.
      // Bring it to the right side.
      if (op0.base_reg () == invalid_regno && op0.index_reg () == invalid_regno)
        std::swap (op0, op1);
      if (op1.base_reg () != invalid_regno || op1.index_reg () != invalid_regno)
        break;

      // Only one register can be scaled, so OP0 can have either a
      // BASE_REG or an INDEX_REG.
      if (op0.base_reg () == invalid_regno)
        {
          index_reg = op0.index_reg ();
          scale = op0.scale () * op1.disp ();
        }
      else if (op0.index_reg () == invalid_regno)
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

// Find the memory accesses in INSN and add them to MEM_LIST, together with their
// access mode. ACCESS_MODE indicates whether the next mem that we find is read
// or written to.
template <typename OutputIterator> void
sh_ams::find_mem_accesses (rtx& x, OutputIterator out,
			   access_mode_t access_mode)
{
  switch (GET_CODE (x))
    {
    case MEM:
      *out++ = std::make_pair (&x, access_mode);
      break;
    case PARALLEL:
      for (int i = 0; i < XVECLEN (x, 0); i++)
        find_mem_accesses (XVECEXP (x, 0, i), out, access_mode);
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
            find_mem_accesses (XEXP (x, i), out, access_mode);
        }
      break;
    }
}

// Generate the address modifications needed to arrive at the addresses in
// the access sequence.  They are inserted in the form of reg_mod accesses
// between the regular accesses.
//
// FIXME: The auto-mod alternatives are currently never selected because the
// insn generating algorithm only tries to optimize one access at a time, and
// SH's simple base reg access costs the same as the auto-mod accesses.
void sh_ams::access_sequence::
gen_address_mod (delegate& dlg)
{
  log_msg ("Generating address modifications\n");

  for (access_sequence::iterator accs = begin (); accs != end (); ++accs)
    {
      if (accs->access_mode () == reg_mod) continue;
      gen_min_mod (accs, dlg, true);
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

  access_sequence::iterator next_acc;
  if (record_in_sequence)
    {
      next_acc = acc;
      ++next_acc;
      for (; next_acc != end (); ++next_acc)
        {
          if (next_acc->access_mode () == load
              || next_acc->access_mode () == load)
            break;
        }
    } else next_acc = end ();

  acc->clear_alternatives ();
  dlg.mem_access_alternatives (*acc);

  // Go through the alternatives for this access and keep
  // track of the one with minimal costs.
  for (access::alternative* alt = acc->begin_alternatives ();
       alt != acc->end_alternatives (); ++alt)
    {
      const addr_expr& alt_ae = alt->address ();
      addr_expr end_base, end_index;

      // Handle only SH-specific access alternatives for now.
      if (alt_ae.base_reg () == invalid_regno
          || (alt_ae.type () != non_mod
              && alt_ae.index_reg () != invalid_regno)
          || (alt_ae.index_reg () != invalid_regno && alt_ae.scale () != 1))
        continue;

      if (alt_ae.index_reg () == invalid_regno)
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

      if (alt_ae.index_reg () != invalid_regno)
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
          if (alt_ae.index_reg () != invalid_regno)
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
  if (alternative.address ().index_reg () == invalid_regno)
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

  // Update the original_addr_expr of the access with the
  // alternative.
  acc->update_address (alternative.costs (), new_addr_expr);
}

// Write the sequence into the insn stream.
void sh_ams::access_sequence::update_insn_stream ()
{
  log_msg ("Updating insn list\n");

  // Remove all the insns that are originally used to arrive at
  // the required addresses.
  for (std::vector<rtx_insn*>::iterator it = reg_mod_insns ().begin ();
       it != reg_mod_insns ().end (); ++it)
    set_insn_deleted (*it);
  reg_mod_insns ().clear ();

  bool sequence_started = false;

  for (access_sequence::iterator accs = begin (); accs != end (); ++accs)
    {
      if (accs->access_mode () == reg_mod)
        {
          // Skip accesses with unknown values and the ones that
          // don't modify anything.
          if (accs->original_address ().is_invalid ())
            continue;
          if (accs->original_address ().base_reg () == accs->modified_reg ()
              && accs->original_address ().index_reg () == invalid_regno
              && accs->original_address ().disp () == 0)
            continue;

          if (!sequence_started)
            {
              start_sequence ();
              sequence_started = true;
            }

          // Insert an address modifying insn according to the reg-mod access.

          rtx new_val;

          if (accs->original_address ().base_reg () == invalid_regno
              && accs->original_address ().index_reg () == invalid_regno)
            new_val = GEN_INT (accs->original_address ().disp ());
          else if (accs->original_address ().index_reg () != invalid_regno)
            {
	      rtx index = expand_mult (accs->original_address ().index_reg (),
				       accs->original_address ().scale ());

              if (accs->original_address ().base_reg () == invalid_regno)
                new_val = index;
              else
		new_val = expand_plus (accs->original_address ().base_reg (),
				       index);
            }
          else
            new_val = accs->original_address ().base_reg ();

          accs->update_insn (emit_move_insn (accs->modified_reg (), new_val));
          reg_mod_insns ().push_back (accs->insn ());
        }
      else
        {
          // Update the access rtx to reflect ORIGINAL_ADDRESS.

          rtx new_addr = accs->original_address ().base_reg ();

          // Add (possibly scaled) index reg.
          if (accs->original_address ().index_reg () != invalid_regno)
            {
	      rtx index = expand_mult (accs->original_address ().index_reg (),
				       accs->original_address ().scale ());
	      new_addr = expand_plus (new_addr, index);
            }

          // Surround with POST/PRE_INC/DEC if ORIGINAL_ADDRESS is an
          // auto_mod type.
          if (accs->original_address ().type () == pre_mod)
            {
              if (accs->original_address ().disp () > 0)
                new_addr = gen_rtx_PRE_INC (Pmode, new_addr);
              else new_addr = gen_rtx_PRE_DEC (Pmode, new_addr);
            }
          else if (accs->original_address ().type () == post_mod)
            {
              if (accs->original_address ().disp () > 0)
                new_addr = gen_rtx_POST_INC (Pmode, new_addr);
              else new_addr = gen_rtx_POST_DEC (Pmode, new_addr);
            }

          // Add constant displacement.
	  new_addr = expand_plus (new_addr, accs->original_address ().disp ());

          if (sequence_started)
            {
              rtx_insn* new_insns = get_insns ();
              end_sequence ();
              emit_insn_before (new_insns, accs->insn ());
              sequence_started = false;
            }

          bool mem_update_ok = accs->update_mem (new_addr);
          gcc_assert (mem_update_ok);

          sh_check_add_incdec_notes (accs->insn ());
        }

    }
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
      if (it->access_mode () != reg_mod || it->address ().is_invalid ())
        continue;

      int cost = try_modify_addr (&(*it), end_addr,
                                  disp_min, disp_max, addr_type, dlg).cost;

      if (cost < min_cost)
        {
          min_cost = cost;
          min_start_addr = &(*it);
        }
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
  rtx new_reg = start_addr->modified_reg ();
  int cost = start_addr->is_used ()
            ? dlg.addr_reg_clone_cost (start_addr->modified_reg ()) : 0;
  rtx final_addr_regno = access_place
                        ? start_addr->modified_reg () : invalid_regno;

  // Canonicalize the start and end addresses by converting
  // addresses of the form base+disp into index*1+disp.
  addr_expr c_start_addr = start_addr->address ();
  addr_expr c_end_addr = end_addr;
  if (c_start_addr.index_reg () == invalid_regno)
    c_start_addr =
      non_mod_addr (invalid_regno, c_start_addr.base_reg (), 1,
                    c_start_addr.disp ());
  if (c_end_addr.index_reg () == invalid_regno)
    c_end_addr =
      non_mod_addr (invalid_regno, c_end_addr.base_reg (), 1,
                    c_end_addr.disp ());

  // If one of the addresses has the form base+index*1, it
  // might be better to switch its base and index reg.
  if (c_start_addr.index_reg () == c_end_addr.base_reg ())
    {
      if (c_end_addr.base_reg () != invalid_regno
          && c_end_addr.index_reg () != invalid_regno
          && c_end_addr.scale () == 1)
        {
          c_end_addr = non_mod_addr (c_end_addr.index_reg (),
                                     c_end_addr.base_reg (),
                                     1, c_end_addr.disp ());
        }
      else if (c_start_addr.base_reg () != invalid_regno
               && c_start_addr.index_reg () != invalid_regno
               && c_start_addr.scale () == 1)
        {
          c_start_addr = non_mod_addr (c_start_addr.index_reg (),
                                       c_start_addr.base_reg (),
                                       1, c_start_addr.disp ());
        }
    }

  // If the start and end address have different index
  // registers, give up.
  if (c_start_addr.index_reg () != c_end_addr.index_reg ())
    return mod_addr_result (infinite_costs, invalid_regno, 0);

  // Same for base regs, unless the start address doesn't have
  // a base reg, in which case we can add one.
  if (c_start_addr.base_reg () != invalid_regno
      && c_start_addr.base_reg () != c_end_addr.base_reg ())
    return mod_addr_result (infinite_costs, invalid_regno, 0);

  // Add scaling.
  if (c_start_addr.index_reg () != invalid_regno
      && c_start_addr.scale () != c_end_addr.scale ())
    {
      // We can't scale if the address has displacement or a base reg.
      if (c_start_addr.disp () != 0 || c_start_addr.base_reg () != invalid_regno)
        return mod_addr_result (infinite_costs, invalid_regno, 0);

      // We can only scale by integers.
      if (c_end_addr.scale () % c_start_addr.scale () != 0)
        return mod_addr_result (infinite_costs, invalid_regno, 0);

      scale_t scale = c_end_addr.scale () / c_start_addr.scale ();
      c_start_addr = non_mod_addr (invalid_regno, c_start_addr.index_reg (),
                                   c_end_addr.scale (), 0);
      cost += dlg.addr_reg_scale_cost (start_addr->modified_reg (), scale);
      if (access_place)
        {
          if (!start_addr->is_used ())
            {
              start_addr->set_used ();
              if (mod_tracker)
                mod_tracker->use_changed_accs ().push_back (start_addr);
            }

          new_reg = gen_reg_rtx (Pmode);
          start_addr
            = &add_reg_mod_access (*access_place,
                                   non_mod_addr (invalid_regno,
                                                 start_addr->modified_reg (),
                                                 scale, 0),
                                   c_start_addr,
                                   NULL, new_reg);
          final_addr_regno = new_reg;

          if (mod_tracker)
            {
              ins_place =  *access_place;
              --ins_place;
              mod_tracker->inserted_accs ().push_back (ins_place);
            }
        }
    }

  // Add missing base reg.
  if (c_start_addr.base_reg () == invalid_regno
      && c_end_addr.base_reg () != invalid_regno)
    {
      c_start_addr = non_mod_addr (c_end_addr.base_reg (),
                                   c_start_addr.index_reg (),
                                   c_start_addr.scale (),
                                   c_start_addr.disp ());
      cost += dlg.addr_reg_plus_reg_cost (start_addr->modified_reg (),
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
          start_addr
            = &add_reg_mod_access (*access_place,
                                   non_mod_addr (c_start_addr.base_reg (),
                                                 start_addr->modified_reg (),
                                                 1, 0),
                                   c_start_addr,
                                   NULL, new_reg);
          final_addr_regno = new_reg;

          if (mod_tracker)
            {
              ins_place =  *access_place;
              --ins_place;
              mod_tracker->inserted_accs ().push_back (ins_place);
            }
        }
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
      cost += dlg.addr_reg_disp_cost (start_addr->modified_reg (), disp);
      if (access_place)
        {
          if (!start_addr->is_used ())
            {
              start_addr->set_used ();
              if (mod_tracker)
                mod_tracker->use_changed_accs ().push_back (start_addr);
            }
          new_reg = gen_reg_rtx (Pmode);
          start_addr
            = &add_reg_mod_access (*access_place,
                                   non_mod_addr (start_addr->modified_reg (),
                                                 invalid_regno,
                                                 1, disp),
                                   c_start_addr,
                                   NULL, new_reg);
          final_addr_regno = new_reg;

          if (mod_tracker)
            {
              ins_place =  *access_place;
              --ins_place;
              mod_tracker->inserted_accs ().push_back (ins_place);
            }
        }
    }

  // For auto-mod accesses, copy the base reg into a new pseudo that will
  // be used by the auto-mod access.  This way, both the pre-access and
  // post-access version of the base reg can be reused by later accesses.
  // Do the same for constant displacement addresses so that there's no
  // cloning penalty for reusing the constant address in another access.
  if (addr_type != non_mod
      || (c_end_addr.base_reg () == invalid_regno
          && c_end_addr.index_reg () == invalid_regno))
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
          start_addr
            = &add_reg_mod_access (*access_place,
                                   make_reg_addr (pre_mod_reg),
                                   c_start_addr,
                                   NULL, new_reg);
          final_addr_regno = new_reg;

          if (mod_tracker)
            {
              ins_place =  *access_place;
              --ins_place;
              mod_tracker->inserted_accs ().push_back (ins_place);
            }
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

unsigned int sh_ams::execute (function* fun)
{
  log_msg ("sh-ams pass\n");

//  df_set_flags (DF_DEFER_INSN_RESCAN); // needed?

  df_note_add_problem ();
  df_analyze ();

  std::vector<std::pair<rtx*, access_mode_t> > mems;

  basic_block bb;
  FOR_EACH_BB_FN (bb, fun)
    {
      log_msg ("BB #%d:\n", bb->index);

      // Construct the access sequence from the access insns.
      access_sequence as;
      for (rtx_insn* next_i, *i = NEXT_INSN (BB_HEAD (bb));
           i != NULL_RTX; i = next_i)
        {
          next_i = NEXT_INSN (i);
          if (!INSN_P (i) || !NONDEBUG_INSN_P (i)
              || bb->index != BLOCK_FOR_INSN (i)->index)
            continue;

          // Search for memory accesses inside the current insn
          // and add them to the address sequence.
          mems.clear ();
          find_mem_accesses (PATTERN (i), std::back_inserter (mems));

          for (std::vector<std::pair<rtx*, access_mode_t> >
	       ::reverse_iterator m = mems.rbegin (); m != mems.rend (); ++m)
	    as.add_new_access (i, m->first, m->second);
         }

      for (access_sequence::iterator it = as.begin();
	   it != as.end(); ++it)
        {
          if (it->access_mode () != reg_mod)
            m_delegate.mem_access_alternatives (*it);
        }


      log_msg ("Access sequence contents:\n\n");
      for (access_sequence::const_iterator it = as.begin();
	   it != as.end(); ++it)
	{
	  log_access (*it);
	  log_msg("\n-----\n");
	}

      log_msg ("\n\n");

      as.gen_address_mod (m_delegate);

      log_msg ("\nAccess sequence contents after address mod generation:\n\n");
      for (access_sequence::const_iterator it = as.begin();
	   it != as.end(); ++it)
	{
	  log_access (*it);
	  log_msg("\n-----\n");
	}

      as.update_insn_stream ();

      log_msg ("\n\n");
    }

  log_return (0, "\n\n");
}
