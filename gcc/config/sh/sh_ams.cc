
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


sh_ams::access::access (rtx_insn* insn, rtx* mem, access_mode_t access_mode)
{
  m_access_mode = access_mode;
  m_machine_mode = GET_MODE (*mem);
  m_addr_space = MEM_ADDR_SPACE (*mem);
  m_insn = insn;
  m_insn_ref = &XEXP (*mem, 0);

  // Create an ADDR_EXPR struct from the address expression of MEM.
  rtx expr = copy_rtx (XEXP (*mem, 0));
  log_msg ("Access rtx:\n");
  log_rtx (expr);
  m_original_addr_expr = extract_addr_expr (expr);
  log_msg ("\nm_original_addr_expr:\n");
  log_msg ("base: %d, index: %d, scale: %d, disp: %d\n",
           m_original_addr_expr.base_reg (), m_original_addr_expr.index_reg (),
           m_original_addr_expr.scale (), m_original_addr_expr.disp ());

  expand_expr (&expr, insn);
  log_msg ("Expanded access rtx:\n");
  log_rtx(expr);
  // FIXME: handle cases where the address expression doesn't
  // fit the base+index*scale+disp format.
  m_addr_expr = extract_addr_expr (expr);
  log_msg ("\nm_addr_expr:\n");
  log_msg ("base: %d, index: %d, scale: %d, disp: %d\n\n",
           m_addr_expr.base_reg (), m_addr_expr.index_reg (),
           m_addr_expr.scale (), m_addr_expr.disp ());
}

// Expand the MEM's address expression by substituting registers
// with the expression calculating their values.
// FIXME: make use of other info such as REG_EQUAL notes.
void sh_ams::expand_expr (rtx* expr, rtx_insn* insn)
{
  enum rtx_code code = GET_CODE (*expr);
  if (REG_P (*expr))
    {
      // Go back through the insn list until we find the last instruction
      // that modified the register.
      for (rtx_insn* i = PREV_INSN (insn); i != NULL_RTX; i = PREV_INSN (i))
        {
          if (!INSN_P (i) || !NONDEBUG_INSN_P (i))
            continue;
          if (replace_reg_value (expr, i, PATTERN (i)))
            break;
        }
    }
  else if ((ARITHMETIC_P (*expr)))
    {
      for (int i = 0; i < GET_RTX_LENGTH (code); i++)
        expand_expr (&XEXP (*expr, i), insn);
    }
}

// If REG is modified in PATTERN, replace it with the expression it is set to.
// Return false otherwise.
bool sh_ams::replace_reg_value (rtx* reg, rtx_insn* insn, rtx pattern)
{
  switch (GET_CODE (pattern))
    {
    case SET:
      {
        rtx dest = SET_DEST (pattern);
        if (REG_P (dest) && REGNO (dest) == REGNO (*reg))
          {
            // We're in the last insn that modified REG, so replace REG
            // with the expression in SET_SRC.
            *reg = copy_rtx (SET_SRC (pattern));
            expand_expr (reg, insn);
            return true;
          }
      }
      break;
    case PARALLEL:
      {
        for (int i = 0; i < XVECLEN (pattern, 0); i++)
          {
            if (replace_reg_value (reg, insn, XVECEXP (pattern, 0, i)))
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
// FIXME: handle auto-mod accesses.
sh_ams::addr_expr sh_ams::extract_addr_expr (rtx x)
{
  addr_expr op0 = make_invalid_addr ();
  addr_expr op1 = make_invalid_addr ();
  disp_t disp, scale;
  regno_t base_reg, index_reg;
  enum rtx_code code = GET_CODE (x);

  // If X is an arithmetic operation, first create ADDR_EXPR structs
  // from its operands. These will later be combined into a single ADDR_EXPR.
  if (code == PLUS || code == MINUS || code == MULT || code == ASHIFT)
    {
      op0 = extract_addr_expr (XEXP (x, 0));
      op1 = extract_addr_expr (XEXP (x, 1));
      if (op0.is_invalid () || op1.is_invalid ())
        return make_invalid_addr ();
    }
  else if (code == NEG)
    {
      op1 = extract_addr_expr (XEXP (x, 0));
      if (op1.is_invalid ())
        return op1;
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

// Find the memory accesses in INSN and add them to AS. ACCESS_MODE indicates
// whether the mem we're looking for is read or written to.
void sh_ams::find_mem_accesses
(rtx_insn* insn, rtx* x_ref, access_sequence& as, access_mode_t access_mode = load)
{
  int i;
  rtx x = *x_ref;
  enum rtx_code code = GET_CODE (x);
  switch (code)
    {
    case MEM:
      as.add_access (new access (insn, x_ref, access_mode));
      break;
    case PARALLEL:
      for (i = 0; i < XVECLEN (x, 0); i++)
        find_mem_accesses (insn, &XVECEXP (x, 0, i), as, access_mode);
      break;
    case SET:
      find_mem_accesses (insn, &SET_DEST (x), as, store);
      find_mem_accesses (insn, &SET_SRC (x), as, load);
      break;
    case CALL:
      find_mem_accesses (insn, &XEXP (x, 0), as, load);
      break;
    default:
      if (ARITHMETIC_P (x))
        {
          for (i = 0; i < GET_RTX_LENGTH (code); i++)
            find_mem_accesses (insn, &XEXP (x, i), as, access_mode);
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
      access_sequence as (bb);
      for (rtx_insn* next_i, *i = NEXT_INSN (BB_HEAD (bb));
           i != NULL_RTX; i = next_i)
        {
          next_i = NEXT_INSN (i);
          if (!INSN_P (i) || !NONDEBUG_INSN_P (i))
            continue;
          // Search for memory accesses inside the current insn
          // and add them to the address sequence.
          find_mem_accesses (i, &PATTERN (i), as);
         }
      log_msg ("\n\n");
    }

  log_return (0, "\n\n");
}
