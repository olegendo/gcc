
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
  m_alternatives_count = 0;
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
  m_alternatives_count = 0;
}

// Add a normal access to the end of the access sequence.
void sh_ams::add_new_access
(access_sequence& as, rtx_insn* insn, rtx* mem, access_mode_t access_mode,
 std::list<rtx_insn*>& reg_mod_insns)
{
  machine_mode m_mode = GET_MODE (*mem);
  // Create an ADDR_EXPR struct from the address expression of MEM.
  addr_expr original_expr =
    extract_addr_expr ((XEXP (*mem, 0)), insn, insn, m_mode, as, false, NULL);
  addr_expr expr =
    extract_addr_expr ((XEXP (*mem, 0)), insn, insn,
                       m_mode, as, true, &reg_mod_insns);
  as.push_back (access (insn, mem, access_mode, original_expr, expr));
}

// Create a reg_mod access and add it to the access sequence.
// This function traverses the insn list backwards starting from INSN to
// find the correct place inside AS where the access needs to be inserted.
void sh_ams::add_reg_mod_access
(access_sequence& as, rtx_insn* insn, rtx mod_expr,
 rtx_insn* mod_insn, regno_t reg)
{
  if (as.empty ())
    {
      as.push_back (access (mod_insn, mod_expr, reg));
      return;
    }
  access_sequence::reverse_iterator as_it = as.rbegin ();
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
 access_sequence& as, bool expand, std::list<rtx_insn*> *reg_mod_insns)
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
        (XEXP (x, 0), insn, root_insn, mem_mach_mode, as, expand, reg_mod_insns);
      op1 = extract_addr_expr
        (XEXP (x, 1), insn, root_insn, mem_mach_mode, as, expand, reg_mod_insns);
      if (op0.is_invalid () || op1.is_invalid ())
        return make_invalid_addr ();
    }
  else if (code == NEG)
    {
      op1 = extract_addr_expr
        (XEXP (x, 0), insn, root_insn, mem_mach_mode, as, expand, reg_mod_insns);
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
             mem_mach_mode, as, expand, reg_mod_insns);
        case PRE_MODIFY:
          return extract_addr_expr
            (XEXP (x, 1), insn, root_insn,
             mem_mach_mode, as, expand, reg_mod_insns);
        default:
          return make_invalid_addr ();
        }

      op1 = extract_addr_expr
        (XEXP (x, 0), insn, root_insn, mem_mach_mode, as, expand, reg_mod_insns);
      disp += op1.disp ();
      return non_mod_addr
        (op1.base_reg (), op1.index_reg (), op1.scale (), disp);
    }

  switch (code)
    {

    // For CONST_INT and REG, the set the base register or the displacement
    // to the appropriate value.
    case CONST_INT:
      disp = INTVAL (x);
      return non_mod_addr (invalid_regno, invalid_regno, 0, disp);
    case REG:
      if (expand)
        {

          // Find the expression that the register was last set to
          // and convert it to an addr_expr.
          rtx reg_value;
          rtx_insn *reg_mod_insn;
          std::list<rtx_insn*>::iterator inserted_mod_insn = reg_mod_insns->end ();
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
                    (reg_value, reg_mod_insn, root_insn,
                     mem_mach_mode, as, true, NULL);
                  return make_reg_addr (REGNO (x));
                }
            }

          // Collect all the insns that are used to arrive at the address
          // into reg_mod_insns.  The content of this list is later used
          // to remove the original register modifying insns when updating
          // the insn stream.  Auto-mod insns don't need to be removed
          // because the mem accesses get changed during the update.
          if (reg_mod_insns != NULL
              && !find_reg_note (reg_mod_insn, REG_INC, NULL_RTX))
            {
              reg_mod_insns->push_back (reg_mod_insn);

              // Keep track of where we inserted the insn in case
              // we might have to backtrack later.
              inserted_mod_insn = reg_mod_insns->end ();
              --inserted_mod_insn;
            }

          addr_expr reg_addr_expr = extract_addr_expr
            (reg_value, reg_mod_insn, root_insn,
             mem_mach_mode, as, true, reg_mod_insns);

          // If the expression is something AMS can't handle, use the original
          // reg instead, and add a reg_mod access to the access sequence.
          if (reg_addr_expr.is_invalid ())
            {
              add_reg_mod_access
                (as, root_insn, reg_value, reg_mod_insn, REGNO (x));

              // Remove any insn that might have been inserted while
              // expanding this register.
              if (reg_mod_insns != NULL)
                reg_mod_insns->erase (inserted_mod_insn, reg_mod_insns->end ());
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
        (op1.index_reg (), op1.base_reg (), -op1.scale (), -op1.disp ());
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

// FIXME: Add REG_DEAD notes and /f and /v flags.
void sh_ams::access_sequence::update_insn_stream
(std::list<rtx_insn*>& reg_mod_insns, delegate* dlg)
{
  log_msg ("Updating insn list\n");

  // Remove all the insns that are originally used to arrive at
  // the required addresses.
  for (std::list<rtx_insn*>::iterator it = reg_mod_insns.begin();
       it != reg_mod_insns.end(); ++it)
    {
      SET_INSN_DELETED (*it);
    }

  // Generate new address reg modifying insns.
  std::vector<reg_value> addr_reg_values;
  for (access_sequence::iterator as_it = begin (); as_it != end (); ++as_it)
    {
      if ((*as_it).access_mode () == reg_mod) continue;

      // Add the unmodified base and index reg values to ADDR_REG_VALUES.
      regno_t base_reg = (*as_it).address ().base_reg ();
      if (base_reg != invalid_regno
          && !reg_value::arr_contains_reg (addr_reg_values, base_reg))
          addr_reg_values.push_back (reg_value (base_reg));
      regno_t index_reg = (*as_it).address ().index_reg ();
      if (index_reg != invalid_regno
          && !reg_value::arr_contains_reg (addr_reg_values, index_reg))
        addr_reg_values.push_back (reg_value (index_reg));

      int min_cost = infinite_costs;
      access::alternative* min_alternative = NULL;
      reg_value *min_start_base = NULL, *min_start_index = NULL;
      addr_expr min_end_base, min_end_index;
      (*as_it).clear_alternatives ();
      dlg->mem_access_alternatives (*as_it);

      for (access::alternative* alt = (*as_it).begin_alternatives ();
           alt != (*as_it).end_alternatives (); ++alt)
        {
          const addr_expr ae = (*as_it).address ();
          const addr_expr alt_ae = alt->address ();
          addr_expr end_base, end_index;

          // Generate only base and base+index type accesses
          // for now (other alternatives are skipped).
          if (alt_ae.base_reg () == invalid_regno
              || alt_ae.disp_min () != 0 || alt_ae.disp_max () != 0
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

          // Get the minimal costs for using this alternative and update
          // the cheapest alternative so far.
          reg_value *start_base, *start_index;
          int alt_min_cost = alt->costs ();
          int address_mod_cost
            = find_min_mod_cost (addr_reg_values, &start_base, end_base, dlg);
          if (address_mod_cost == infinite_costs) continue;
          alt_min_cost += address_mod_cost;

          if (alt_ae.index_reg () != invalid_regno)
            {
              address_mod_cost = find_min_mod_cost (addr_reg_values, &start_index,
                                                    end_index, dlg);
              if (address_mod_cost == infinite_costs) continue;
              alt_min_cost += address_mod_cost;
            }

          if (alt_min_cost < min_cost)
            {
              min_cost = alt_min_cost;
              min_start_base = start_base;
              min_end_base = end_base;
              if (alt_ae.index_reg () != invalid_regno)
                {
                  min_end_index = end_index;
                  min_start_index = start_index;
                }
              min_alternative = alt;
            }
        }

      // Insert the address reg modifying insns before the access insn
      // and update the access.
      regno_t access_base =
        insert_reg_mod_insns (min_start_base, min_end_base,
                              (*as_it).insn (), addr_reg_values, dlg);

      if (min_alternative->address ().index_reg () == invalid_regno)
        *(*as_it).insn_ref () = gen_rtx_REG (word_mode, access_base);
      else
        {
          regno_t access_index =
            insert_reg_mod_insns (min_start_index, min_end_index,
                                  (*as_it).insn (), addr_reg_values, dlg);
          *(*as_it).insn_ref () =
            gen_rtx_PLUS (word_mode,
                          gen_rtx_REG (word_mode, access_base),
                          gen_rtx_REG (word_mode, access_index));
        }

      // FIXME: It might be faster to update the df manually.
      df_insn_rescan ((*as_it).insn ());
    }

  log_msg ("\naddr_reg_values after insn update:\n");
  for (std::vector<reg_value>::iterator it = addr_reg_values.begin ();
       it != addr_reg_values.end (); ++it)
    {
      log_msg ("r%d <- ", (*it).reg ());
      if ((*it).value ().base_reg () != invalid_regno)
        log_msg ("r%d + ", (*it).value ().base_reg ());
      if ((*it).value ().index_reg () != invalid_regno)
        log_msg ("r%d*%d + ", (*it).value ().index_reg (),
                 (*it).value ().scale ());
      log_msg ("%d\n", (*it).value ().disp ());
    }
  log_msg ("\n");
}

// Find the cheapest way END_ADDR can be arrived at from one of the values
// in ADDR_REG_VALUES.  Set MIN_START_ADDR to the reg_value that can be
// changed into END_ADDR with the least cost and return its cost.
int sh_ams::access_sequence::find_min_mod_cost
(std::vector<reg_value>& addr_reg_values,
 reg_value **min_start_addr, const addr_expr end_addr, delegate* dlg)
{
  int min_cost = infinite_costs;
  for (std::vector<reg_value>::iterator it = addr_reg_values.begin ();
       it != addr_reg_values.end (); ++it)
    {
      int cost = try_modify_addr (&(*it), end_addr, dlg);
      if (cost < min_cost)
        {
          min_cost = cost;
          *min_start_addr = &(*it);
        }
    }
  return min_cost;
}

// Insert insns behind INSN that modify START_ADDR to arrive at END_ADDR.
// Return the register in which the final address is stored.
sh_ams::regno_t sh_ams::access_sequence::insert_reg_mod_insns
(reg_value* start_value, const addr_expr end_addr,
 rtx_insn* insn, std::vector<reg_value>& addr_reg_values, delegate* dlg)
{
  regno_t final_addr_regno;
  try_modify_addr (start_value, end_addr, &addr_reg_values,
                   insn, &final_addr_regno, dlg);
  return final_addr_regno;
}

// Try to find address modifying insns that change the address in START_VALUE
// into END_ADDR.  If ADDR_REG_VALUES and INSN is not null, insert the insns
// before INSN, insert their corresponding reg_value structure into
// ADDR_REG_VALUES, and set FINAL_ADDR_REGNO to the register that stores the
// final address.
// Return the total cost of the modifying insns, or INFINITE_COSTS if no
// suitable insns have been found.
int sh_ams::access_sequence::try_modify_addr
(reg_value* start_value, const addr_expr end_addr,
 std::vector<reg_value>* addr_reg_values, rtx_insn* insn,
 regno_t* final_addr_regno, delegate* dlg)
{
  rtx new_reg = NULL_RTX;
  int cost = start_value->is_used ()
    ? dlg->addr_reg_clone_cost (start_value->reg ()) : 0;
  if (final_addr_regno != NULL) *final_addr_regno = start_value->reg ();
  rtx_insn *new_insns;
  if (insn != NULL_RTX) start_sequence ();

  // Canonicalize the start and end addresses by converting
  // addresses of the form base+disp into index*1+disp.
  addr_expr c_start_addr = start_value->value ();
  addr_expr c_end_addr = end_addr;
  if (c_start_addr.index_reg () == invalid_regno)
    c_start_addr =
      non_mod_addr (invalid_regno, c_start_addr.base_reg (), 1,
                    c_start_addr.disp ());
  if (c_end_addr.index_reg () == invalid_regno)
    c_end_addr =
      non_mod_addr (invalid_regno, c_end_addr.base_reg (), 1,
                    c_end_addr.disp ());

  // If the one of the addresses has the form base+index*1, it
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
    return infinite_costs;

  // Same for base regs, unless the start address doesn't have
  // a base reg, in which case we can add one.
  if (c_start_addr.base_reg () != invalid_regno
      && c_start_addr.base_reg () != c_end_addr.base_reg ())
    return infinite_costs;

  // FIXME: Handle cases when the end address consists only
  // of a constant displacement.

  // Add scaling insns.
  if (c_start_addr.index_reg () != invalid_regno
      && c_start_addr.scale () != c_end_addr.scale ())
    {
      // We can't scale if the address has displacement or a base reg.
      if (c_start_addr.disp () != 0 || c_start_addr.base_reg () != invalid_regno)
        return infinite_costs;

      // We can only scale by integers.
      if (c_end_addr.scale () % c_start_addr.scale () != 0)
        return infinite_costs;

      scale_t scale = c_end_addr.scale () / c_start_addr.scale ();
      c_start_addr = non_mod_addr (invalid_regno, c_start_addr.index_reg (),
                                   c_end_addr.scale (), 0);
      cost += dlg->addr_reg_scale_cost (start_value->reg (), scale);
      if (addr_reg_values != NULL)
        {
          start_value->set_used ();
          new_reg = gen_reg_rtx (word_mode);
          rtx mult_rtx;
          if ((scale & (scale - 1)) == 0)
            {
              scale_t shift = 0;
              while (scale >>= 1) ++shift;
              mult_rtx = gen_rtx_ASHIFT
                (word_mode,
                 gen_rtx_REG (word_mode, start_value->reg ()),
                 gen_rtx_CONST_INT (word_mode, shift));
            }
          else
            mult_rtx = gen_rtx_MULT (word_mode,
                                     gen_rtx_REG (word_mode, start_value->reg ()),
                                     gen_rtx_CONST_INT (word_mode, scale));

          emit_move_insn (new_reg, mult_rtx);
          addr_reg_values->push_back (reg_value (REGNO (new_reg), c_start_addr));
          start_value = &addr_reg_values->back ();
          *final_addr_regno = REGNO (new_reg);
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
      cost += dlg->addr_reg_plus_reg_cost (start_value->reg (),
                                           c_end_addr.base_reg ());
      if (addr_reg_values != NULL)
        {
          start_value->set_used ();
          new_reg = gen_reg_rtx (word_mode);
          rtx reg_plus_rtx =
            gen_rtx_PLUS (word_mode,
                          gen_rtx_REG (word_mode, start_value->reg ()),
                          gen_rtx_REG (word_mode, c_end_addr.base_reg ()));

          emit_move_insn (new_reg, reg_plus_rtx);
          addr_reg_values->push_back (reg_value (REGNO (new_reg), c_start_addr));
          start_value = &addr_reg_values->back ();
          *final_addr_regno = REGNO (new_reg);
        }
    }

  // Add displacement insns.
  if (c_start_addr.disp () != c_end_addr.disp ())
    {
      cost += dlg->addr_reg_disp_cost (start_value->reg (),
                                       c_end_addr.disp () - c_start_addr.disp ());
      if (addr_reg_values != NULL)
        {
          start_value->set_used ();
          new_reg = gen_reg_rtx (word_mode);
          rtx plus_rtx
            = gen_rtx_PLUS (word_mode,
                            gen_rtx_REG (word_mode, start_value->reg ()),
                            gen_rtx_CONST_INT
                            (word_mode,
                             c_end_addr.disp () - c_start_addr.disp ()));
          emit_move_insn (new_reg, plus_rtx);
          addr_reg_values->push_back (reg_value (REGNO (new_reg), c_end_addr));
          *final_addr_regno = REGNO (new_reg);
        }
    }

  if (insn != NULL_RTX)
    {
      new_insns = get_insns ();
      end_sequence ();
      emit_insn_before (new_insns, insn);
    }

  return cost;
}

int sh_ams::access_sequence::try_modify_addr
(reg_value* start_value, const addr_expr end_addr, delegate* dlg)
{
  return try_modify_addr (start_value, end_addr, NULL, NULL, NULL, dlg);
}

unsigned int sh_ams::execute (function* fun)
{
  log_msg ("sh-ams pass\n");

//  df_set_flags (DF_DEFER_INSN_RESCAN); // needed?

  df_note_add_problem ();
  df_analyze ();

  basic_block bb;
  FOR_EACH_BB_FN (bb, fun)
    {
      log_msg ("BB #%d:\n", bb->index);
      std::list<std::pair<rtx*, access_mode_t> > mems;
      std::list<rtx_insn*> reg_mod_insns;

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
          find_mem_accesses (&PATTERN (i), mems);
          while (!mems.empty ())
            {
              add_new_access
                (as, i, mems.back ().first, mems.back ().second, reg_mod_insns);
              mems.pop_back ();
            }
         }
      log_msg ("Access sequence contents:\n\n");
      for (access_sequence::const_iterator it = as.begin();
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

      as.update_insn_stream (reg_mod_insns, m_delegate);
    }

  log_return (0, "\n\n");
}
