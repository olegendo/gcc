
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

sh_ams::sh_ams (gcc::context* ctx, const char* name, delegate* dlg)
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
  return optimize > 0 && flag_auto_inc_dec && m_delegate != NULL;
}

namespace
{


} // anonymous namespace


sh_ams::access::access
(rtx_insn* insn, rtx* mem, access_mode_t access_mode,
 addr_expr original_addr_expr, addr_expr addr_expr)
{
  m_access_mode = access_mode;
  m_machine_mode = GET_MODE (*mem);
  m_addr_space = MEM_ADDR_SPACE (*mem);
  m_insn = insn;
  m_insn_ref = &XEXP (*mem, 0);
  m_original_addr_expr = original_addr_expr;
  m_addr_expr = addr_expr;
}

// This constructor creates an access that represents
// a register modification.
sh_ams::access::access
(rtx_insn* insn, rtx mod_expr, regno_t reg)
{
  m_access_mode = reg_mod;
  m_machine_mode = GET_MODE (mod_expr);
  m_insn = insn;
  m_reg_mod_expr = mod_expr;
  m_original_addr_expr = make_invalid_addr ();
  m_addr_expr = make_reg_addr (reg);
}

// Add a normal access to the end of the access sequence.
void sh_ams::add_new_access
(std::list<access>& as, rtx_insn* insn, rtx* mem, access_mode_t access_mode)
{
  machine_mode m_mode = GET_MODE (*mem);
  // Create an ADDR_EXPR struct from the address expression of MEM.
  addr_expr original_expr =
    extract_addr_expr ((XEXP (*mem, 0)), insn, insn, m_mode, as, false);
  addr_expr expr =
    extract_addr_expr ((XEXP (*mem, 0)), insn, insn, m_mode, as, true);
  as.push_back (access (insn, mem, access_mode, original_expr, expr));
}

// Create a reg_mod access and add it to the access sequence.
// This function traverses the insn list backwards starting from INSN to
// find the correct place inside AS where the access needs to be inserted.
void sh_ams::add_reg_mod_access
(std::list<access>& as, rtx_insn* insn, rtx mod_expr,
 rtx_insn* mod_insn, regno_t reg)
{
  if (as.empty ())
    {
      as.push_back (access (mod_insn, mod_expr, reg));
      return;
    }
  std::list<access>::reverse_iterator as_it = as.rbegin ();
  for (rtx_insn* i = insn; i != NULL_RTX; i = PREV_INSN (i))
    {
      if (!INSN_P (i) || !NONDEBUG_INSN_P (i))
        continue;

      // Keep track of the current insn in as.
      if (INSN_UID ((*as_it).insn ()) == INSN_UID (i))
        {
          ++as_it;

          // If the reg_mod access is already inside the access
          // sequence, don't add it a second time.
          if ((*as_it).access_mode () == reg_mod
              && (*as_it).reg_mod_expr () == mod_expr)
            break;
        }
      if (INSN_UID (i) == INSN_UID (mod_insn))
        {
          // We found mod_insn inside the insn list, so we know where to
          // insert the access.
          as.insert (as_it.base (), access (mod_insn, mod_expr, reg));
          break;
        }
    }
}

// Find the value that REG was last set to. Write the register value
// into mod_expr and the modifying insn into mod_insn.
// FIXME: make use of other info such as REG_EQUAL notes.
void sh_ams::find_reg_value
(rtx reg, rtx_insn* insn, rtx* mod_expr, rtx_insn** mod_insn)
{
  std::list<std::pair<rtx*, access_mode_t> > mems;
  // Go back through the insn list until we find the last instruction
  // that modified the register.
  for (rtx_insn* i = PREV_INSN (insn); i != NULL_RTX; i = PREV_INSN (i))
    {
      if (!INSN_P (i) || !NONDEBUG_INSN_P (i)
          || BLOCK_FOR_INSN (insn)->index != BLOCK_FOR_INSN (i)->index)
        continue;
      if (find_reg_value_1 (reg, PATTERN (i), mod_expr))
        {
          *mod_insn = i;
          return;
        }
      else
        {
          // Search for auto-mod memory accesses in the current
          // insn that modify REG.
          find_mem_accesses (&PATTERN (i), mems);
          while (!mems.empty ())
            {
              rtx mem_addr = XEXP (*(mems.back ().first), 0);
              enum rtx_code code = GET_CODE (mem_addr);
              if (GET_RTX_CLASS (code) == RTX_AUTOINC
                  && REG_P (XEXP (mem_addr, 0))
                  && REGNO (XEXP (mem_addr, 0)) == REGNO (reg))
                {
                  *mod_expr = mem_addr;
                  *mod_insn = i;
                  return;
                }
              mems.pop_back ();
            }
        }
    }
  *mod_expr = reg;
}

// The recursive part of find_reg_value. If REG is modified in INSN,
// set VALUE to REG's value and return true. Otherwise, return false.
bool sh_ams::find_reg_value_1 (rtx reg, rtx pattern, rtx* value)
{
  rtx dest;
  switch (GET_CODE (pattern))
    {
    case SET:
      {
        dest = SET_DEST (pattern);
        if (REG_P (dest) && REGNO (dest) == REGNO (reg))
          {
            // We're in the last insn that modified REG, so return
            // the expression in SET_SRC.
            *value = SET_SRC (pattern);
            return true;
          }
      }
      break;
    case CLOBBER:
      dest = XEXP (pattern, 0);
      if (REG_P (dest) && REGNO (dest) == REGNO (reg))
        {
          // The value of REG is unknown.
          *value = NULL_RTX;
          return true;
        }
      break;
    case PARALLEL:
      {
        for (int i = 0; i < XVECLEN (pattern, 0); i++)
          {
            if (find_reg_value_1 (reg, XVECEXP (pattern, 0, i), value))
              return true;
          }
      }
      break;
    default:
      break;
    }
  return false;
}

// Try to create an ADDR_EXPR struct of the form
// base_reg + index_reg * scale + disp from the access expression X.
// If EXPAND is true, trace the original value of the registers in X
// as far back as possible.
// INSN is the insn in which the access happens.  ROOT_INSN is the INSN
// argument that was passed to the function at the top level of recursion
// (used as the start insn when calling add_reg_mod_access).
sh_ams::addr_expr sh_ams::extract_addr_expr
(rtx x, rtx_insn* insn, rtx_insn *root_insn, machine_mode mem_mach_mode,
 std::list<access>& as, bool expand)
{
  addr_expr op0 = make_invalid_addr ();
  addr_expr op1 = make_invalid_addr ();
  disp_t disp, scale;
  regno_t base_reg, index_reg;

  if (x == NULL_RTX) return make_invalid_addr ();

  enum rtx_code code = GET_CODE (x);

  // If X is an arithmetic operation, first create ADDR_EXPR structs
  // from its operands. These will later be combined into a single ADDR_EXPR.
  if (code == PLUS || code == MINUS || code == MULT || code == ASHIFT)
    {
      op0 = extract_addr_expr
        (XEXP (x, 0), insn, root_insn, mem_mach_mode, as, expand);
      op1 = extract_addr_expr
        (XEXP (x, 1), insn, root_insn, mem_mach_mode, as, expand);
      if (op0.is_invalid () || op1.is_invalid ())
        return make_invalid_addr ();
    }
  else if (code == NEG)
    {
      op1 = extract_addr_expr
        (XEXP (x, 0), insn, root_insn, mem_mach_mode, as, expand);
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
             mem_mach_mode, as, expand);
        case PRE_MODIFY:
          return extract_addr_expr
            (XEXP (x, 1), insn, root_insn, mem_mach_mode, as, expand);
        default:
          return make_invalid_addr ();
        }

      op1 = extract_addr_expr
        (XEXP (x, 0), insn, root_insn, mem_mach_mode, as, expand);
      disp += op1.disp ();
      return non_mod_addr
        (op1.base_reg (), op1.index_reg (),
         op1.scale (), op1.scale (), op1.scale (),
         disp, disp, disp);
    }

  switch (code)
    {

    // For CONST_INT and REG, the set the base register or the displacement
    // to the appropriate value.
    case CONST_INT:
      disp = INTVAL (x);
      return non_mod_addr (invalid_regno, invalid_regno,
                           0, 0, 0, disp, disp, disp);
    case REG:
      if (expand)
        {

          // Find the expression that the register was last set to
          // and convert it to an addr_expr.
          rtx reg_value;
          rtx_insn *reg_mod_insn;
          find_reg_value (x, insn, &reg_value, &reg_mod_insn);
          if (reg_value != NULL_RTX && REG_P (reg_value))
            {
              if (REGNO (reg_value) == REGNO (x))
                return make_reg_addr (REGNO (x));

              // Don't expand hardreg -> pseudo reg copies.  Instead, add the
              // copy as a reg_mod access.
              if (HARD_REGISTER_P (reg_value))
                {
                  add_reg_mod_access
                    (as, root_insn, reg_value, reg_mod_insn, REGNO (x));

                  // The hard reg still needs to be traced back in case it
                  // is set to some unknown value, like the result of a CALL.
                  extract_addr_expr
                    (reg_value, reg_mod_insn, root_insn, mem_mach_mode, as, true);
                  return make_reg_addr (REGNO (x));
                }
            }

          addr_expr reg_addr_expr = extract_addr_expr
            (reg_value, reg_mod_insn, root_insn, mem_mach_mode, as, true);

          // If the expression is something AMS can't handle, use the original
          // reg instead, and add a reg_mod access to the access sequence.
          if (reg_addr_expr.is_invalid ())
            {
              add_reg_mod_access
                (as, root_insn, reg_value, reg_mod_insn, REGNO (x));
              return make_reg_addr (REGNO (x));
            }
          return reg_addr_expr;
        }
      else
        return make_reg_addr (REGNO (x));

    // Handle MINUS by inverting OP1 and proceeding to PLUS.
    // NEG is handled similarly, but returns with OP1 after inverting it.
    case NEG:
    case MINUS:

      // Only expressions of the form base + index * (-1) + disp
      // or base + disp are inverted.
      if (op1.index_reg () != invalid_regno && op1.scale () != -1)
        break;
      op1 = non_mod_addr
        (op1.index_reg (), op1.base_reg (),
         -op1.scale (), -op1.scale (), -op1.scale (),
         -op1.disp (), -op1.disp (), -op1.disp ());
      if (code == NEG) return op1;
    case PLUS:
      disp = op0.disp () + op1.disp ();
      index_reg = invalid_regno;
      scale = 0;

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
      // FIXME: it might be possible to combine them when the base
      // and/or index regs are the same.
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
      return non_mod_addr (base_reg, index_reg,
                           scale, scale, scale, disp, disp, disp);

    // Change shift into multiply.
    case ASHIFT:

      // OP1 must be a non-negative constant.
      if (op1.base_reg () == invalid_regno && op1.index_reg () == invalid_regno
          && op1.disp () >= 0)
        {
          disp_t mul = 1
            << op1.disp ();
          op1 = non_mod_addr
            (invalid_regno, invalid_regno, 0, 0, 0, mul, mul, mul);
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
                           scale, scale, scale,
                           op0.disp () * op1.disp (),
                           op0.disp () * op1.disp (),
                           op0.disp () * op1.disp ());
    default:
      break;
    }
  return make_invalid_addr ();
}

// Find the memory accesses in INSN and add them to MEM_LIST, together with their
// access mode. ACCESS_MODE indicates whether the next mem that we find is read
// or written to.
void sh_ams::find_mem_accesses
(rtx* x_ref, std::list<std::pair<rtx*, access_mode_t> >& mem_list,
 access_mode_t access_mode)
{
  int i;
  rtx x = *x_ref;
  enum rtx_code code = GET_CODE (x);
  switch (code)
    {
    case MEM:
      mem_list.push_back
        (std::pair<rtx*, access_mode_t> (x_ref, access_mode));
      break;
    case PARALLEL:
      for (i = 0; i < XVECLEN (x, 0); i++)
        find_mem_accesses (&XVECEXP (x, 0, i), mem_list, access_mode);
      break;
    case SET:
      find_mem_accesses (&SET_DEST (x), mem_list, store);
      find_mem_accesses (&SET_SRC (x), mem_list, load);
      break;
    case CALL:
      find_mem_accesses (&XEXP (x, 0), mem_list, load);
      break;
    default:
      if (ARITHMETIC_P (x))
        {
          for (i = 0; i < GET_RTX_LENGTH (code); i++)
            find_mem_accesses (&XEXP (x, i), mem_list, access_mode);
        }
      break;
    }
}

unsigned int sh_ams::execute (function* fun)
{
  log_msg ("sh-ams pass\n");

//  df_set_flags (DF_DEFER_INSN_RESCAN); // needed?
  df_set_flags (DF_NO_INSN_RESCAN);  // disable data flow updates.

  df_note_add_problem ();
  df_analyze ();

  basic_block bb;
  FOR_EACH_BB_FN (bb, fun)
    {
      log_msg ("BB #%d:\n", bb->index);

      // Construct the access sequence from the access insns.
      std::list<access> as;
      std::list<std::pair<rtx*, access_mode_t> > mems;
      for (rtx_insn* next_i, *i = NEXT_INSN (BB_HEAD (bb));
           i != NULL_RTX; i = next_i)
        {
          next_i = NEXT_INSN (i);
          if (!INSN_P (i) || !NONDEBUG_INSN_P (i)
              || bb->index != BLOCK_FOR_INSN (i)->index)
            continue;
          // Search for memory accesses inside the current insn
          // and add them to the address sequence.
          find_mem_accesses (&PATTERN (i), mems);
          while (!mems.empty ())
            {
              add_new_access
                (as, i, mems.back ().first, mems.back ().second);
              mems.pop_back ();
            }
         }
      log_msg ("Access sequence contents:\n\n");
      for (std::list<access>::const_iterator it = as.begin();
           it != as.end(); ++it)
        {
          if ((*it).access_mode () == reg_mod)
            {
              log_msg ("reg_mod: r%d set to\n", (*it).address ().base_reg ());
              log_rtx ((*it).reg_mod_expr ());
              log_msg("\n-----\n\n");
            }
          else
            {
              log_msg ("m_original_addr_expr:\n");
              log_msg ("base: %d, index: %d, scale: %d, disp: %d\n",
                       (*it).original_address ().base_reg (),
                       (*it).original_address ().index_reg (),
                       (*it).original_address ().scale (),
                       (*it).original_address ().disp ());
              log_msg ("\nm_addr_expr:\n");
              log_msg ("base: %d, index: %d, scale: %d, disp: %d\n-----\n\n",
                       (*it).address ().base_reg (),
                       (*it).address ().index_reg (),
                       (*it).address ().scale (),
                       (*it).address ().disp ());
            }
        }
      log_msg ("\n\n");
    }

  log_return (0, "\n\n");
}
