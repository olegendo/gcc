
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

struct regno_equal
{
  const int val;

  regno_equal (int v) : val (v) { }
  
  bool operator () (const sh_ams::access_sequence::reg_value& a) const
  {
    return a.reg () == val;
  }
};

} // anonymous namespace


sh_ams::access::access
(rtx_insn* insn, rtx* mem, access_mode_t access_mode,
 addr_expr original_addr_expr, addr_expr addr_expr)
{
  m_access_mode = access_mode;
  m_machine_mode = GET_MODE (*mem);
  m_addr_space = MEM_ADDR_SPACE (*mem);
  m_insn = insn;
  m_mem_ref = mem;
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
      if (INSN_UID (as_it->insn ()) == INSN_UID (i))
        {
          ++as_it;

          // If the reg_mod access is already inside the access
          // sequence, don't add it a second time.
          if (as_it->access_mode () == reg_mod
              && as_it->reg_mod_expr () == mod_expr)
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

// The recursive part of find_reg_value. If REG is modified in INSN,
// set VALUE to REG's value and return true. Otherwise, return false.
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
  mems.reserve (32);

  // Go back through the insn list until we find the last instruction
  // that modified the register.
  for (rtx_insn* i = PREV_INSN (insn); i != NULL_RTX; i = PREV_INSN (i))
    {
      if (!INSN_P (i) || !NONDEBUG_INSN_P (i)
          || BLOCK_FOR_INSN (insn)->index != BLOCK_FOR_INSN (i)->index)
        continue;

      std::pair<rtx, bool> r = find_reg_value_1 (reg, PATTERN (i));
      if (r.second)
        {
          *mod_expr = r.first;
          *mod_insn = i;
          return;
        }
      else
        {
          // Search for auto-mod memory accesses in the current
          // insn that modify REG.
          mems.clear ();
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
      if (ARITHMETIC_P (x))
        {
          for (int i = 0; i < GET_RTX_LENGTH (GET_CODE (x)); i++)
            find_mem_accesses (XEXP (x, i), out, access_mode);
        }
      break;
    }
}

// FIXME: Add REG_DEAD notes and /f and /v flags.
void sh_ams::access_sequence::update_insn_stream
(std::list<rtx_insn*>& reg_mod_insns, delegate& dlg)
{
  log_msg ("Updating insn list\n");

  // Remove all the insns that are originally used to arrive at
  // the required addresses.
  for (std::list<rtx_insn*>::iterator it = reg_mod_insns.begin();
       it != reg_mod_insns.end(); ++it)
    {
      set_insn_deleted (*it);
    }

  // Generate new address reg modifying insns.
  std::vector<reg_value> addr_reg_values;
  for (access_sequence::iterator accs = begin (); accs != end (); ++accs)
    {
      if (accs->access_mode () == reg_mod) continue;
      const addr_expr& ae = accs->address ();

      // Add the unmodified base and index reg values to ADDR_REG_VALUES.
      regno_t base_reg = accs->address ().base_reg ();
      if (base_reg != invalid_regno
	  && std::find_if (addr_reg_values.begin (), addr_reg_values.end (),
			   regno_equal (base_reg)) == addr_reg_values.end ())
          addr_reg_values.push_back (reg_value (base_reg));

      regno_t index_reg = accs->address ().index_reg ();
      if (index_reg != invalid_regno
	  && std::find_if (addr_reg_values.begin (), addr_reg_values.end (),
			   regno_equal (index_reg)) == addr_reg_values.end ())
        addr_reg_values.push_back (reg_value (index_reg));

      int min_cost = infinite_costs;
      access::alternative* min_alternative = NULL;
      reg_value *min_start_base = NULL, *min_start_index = NULL;
      addr_expr min_end_base, min_end_index;
      accs->clear_alternatives ();
      dlg.mem_access_alternatives (*accs);

      for (access::alternative* alt = accs->begin_alternatives ();
           alt != accs->end_alternatives (); ++alt)
        {
          const addr_expr& alt_ae = alt->address ();
          addr_expr end_base, end_index;

          // Generate only base, base+disp and base+index type accesses
          // for now (auto-mod alternatives are skipped).
          if (alt_ae.base_reg () == invalid_regno
              || alt_ae.type () != non_mod
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
          int alt_min_cost = alt->costs ();
          
          min_mod_cost_result base_mod_cost =
		find_min_mod_cost (addr_reg_values, end_base,
				   alt_ae.disp_min (), alt_ae.disp_max (), dlg);
          
	  if (base_mod_cost.cost == infinite_costs)
	    continue;
	    
          alt_min_cost += base_mod_cost.cost;

	  min_mod_cost_result index_mod_cost;

          if (alt_ae.index_reg () != invalid_regno)
            {
	      index_mod_cost =
		  find_min_mod_cost (addr_reg_values, end_index, 0, 0, dlg);

              if (index_mod_cost.cost == infinite_costs)
		continue;
		
              alt_min_cost += index_mod_cost.cost;
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

      // Insert the address reg modifying insns before the access insn
      // and update the access.
      regno_t access_base =
        insert_reg_mod_insns (min_start_base, min_end_base,
                              accs->insn (), addr_reg_values,
                              min_alternative->address ().disp_min (),
                              min_alternative->address ().disp_max (),
                              dlg);
      rtx new_addr;
      if (min_alternative->address ().index_reg () == invalid_regno)
        {
          disp_t disp = ae.disp () - min_start_base->value ().disp ();
          if (disp == 0)
            new_addr = gen_rtx_REG (Pmode, access_base);
          else
            new_addr = gen_rtx_PLUS (Pmode,
                                     gen_rtx_REG (Pmode, access_base),
                                     GEN_INT (disp));
        }
      else
        {
          regno_t access_index =
            insert_reg_mod_insns (min_start_index, min_end_index,
                                  accs->insn (), addr_reg_values, 0, 0, dlg);
          new_addr = gen_rtx_PLUS (Pmode,
                                   gen_rtx_REG (Pmode, access_base),
                                   gen_rtx_REG (Pmode, access_index));
        }

      validate_change (accs->insn (), accs->mem_ref (),
		       replace_equiv_address (*(accs->mem_ref ()), new_addr),
		       false);
    }

  log_msg ("\naddr_reg_values after insn update:\n");
  for (std::vector<reg_value>::iterator it = addr_reg_values.begin ();
       it != addr_reg_values.end (); ++it)
    {
      log_msg ("r%d <- ", it->reg ());
      if (it->value ().base_reg () != invalid_regno)
        log_msg ("r%d + ", it->value ().base_reg ());
      if (it->value ().index_reg () != invalid_regno)
        log_msg ("r%d*%d + ", it->value ().index_reg (),
                 it->value ().scale ());
      log_msg ("%d\n", it->value ().disp ());
    }
  log_msg ("\n");
}

// Find the cheapest way END_ADDR can be arrived at from one of the values
// in ADDR_REG_VALUES.  Return the reg_value that can be changed into
// END_ADDR with the least cost and the actual cost.
sh_ams::access_sequence::min_mod_cost_result
sh_ams::access_sequence
::find_min_mod_cost (std::vector<reg_value>& addr_reg_values,
		     const addr_expr& end_addr,
		     disp_t disp_min, disp_t disp_max, delegate& dlg)
{
  int min_cost = infinite_costs;
  reg_value* min_start_addr = NULL;
  
  for (std::vector<reg_value>::iterator it = addr_reg_values.begin ();
       it != addr_reg_values.end (); ++it)
    {
      int cost = try_modify_addr (&(*it), end_addr, disp_min, disp_max, dlg);
      if (cost < min_cost)
        {
          min_cost = cost;
          min_start_addr = &(*it);
        }
    }
  return min_mod_cost_result (min_cost, min_start_addr);
}

// Insert insns behind INSN that modify START_ADDR to arrive at END_ADDR.
// Return the register in which the final address is stored.
sh_ams::regno_t sh_ams::access_sequence::insert_reg_mod_insns
(reg_value* start_value, const addr_expr& end_addr,
 rtx_insn* insn, std::vector<reg_value>& addr_reg_values,
 disp_t disp_min, disp_t disp_max, delegate& dlg)
{
  regno_t final_addr_regno;
  try_modify_addr (start_value, end_addr, disp_min, disp_max,
                   &addr_reg_values, insn, &final_addr_regno, dlg);
  return final_addr_regno;
}

// Try to find address modifying insns that change the address in START_VALUE
// into END_ADDR.  If ADDR_REG_VALUES and INSN is not null, insert the insns
// before INSN, insert their corresponding reg_value structure into
// ADDR_REG_VALUES, and set FINAL_ADDR_REGNO to the register that stores the
// final address.
// DISP_MIN and DISP_MAX shows the range of displacement that can be added to
// the address during the access.  If they are not zero, the final displacement
// of the generated address doesn't have to match the displacement of
// END_ADDR exactly.  Instead, it must be in the range
// [end_addr.disp ()+disp_min, end_addr.disp ()+disp_max].
// Return the total cost of the modifying insns, or INFINITE_COSTS if no
// suitable insns have been found.
int sh_ams::access_sequence::try_modify_addr
(reg_value* start_value, const addr_expr& end_addr,
 disp_t disp_min, disp_t disp_max,
 std::vector<reg_value>* addr_reg_values, rtx_insn* insn,
 regno_t* final_addr_regno, delegate& dlg)
{
  rtx new_reg = NULL_RTX;
  int cost = start_value->is_used ()
	     ? dlg.addr_reg_clone_cost (start_value->reg ()) : 0;
  if (final_addr_regno != NULL) *final_addr_regno = start_value->reg ();

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
    {
      if (insn != NULL)
        end_sequence ();
      return infinite_costs;
    }

  // Same for base regs, unless the start address doesn't have
  // a base reg, in which case we can add one.
  if (c_start_addr.base_reg () != invalid_regno
      && c_start_addr.base_reg () != c_end_addr.base_reg ())
    {
      if (insn != NULL)
        end_sequence ();
      return infinite_costs;
    }

  // FIXME: Handle cases when the end address consists only
  // of a constant displacement.

  // Add scaling insns.
  if (c_start_addr.index_reg () != invalid_regno
      && c_start_addr.scale () != c_end_addr.scale ())
    {
      // We can't scale if the address has displacement or a base reg.
      if (c_start_addr.disp () != 0 || c_start_addr.base_reg () != invalid_regno)
	{
	  if (insn != NULL)
	    end_sequence ();
	  return infinite_costs;
	}

      // We can only scale by integers.
      if (c_end_addr.scale () % c_start_addr.scale () != 0)
        {
	  if (insn != NULL)
	    end_sequence ();
	  return infinite_costs;
	}

      scale_t scale = c_end_addr.scale () / c_start_addr.scale ();
      c_start_addr = non_mod_addr (invalid_regno, c_start_addr.index_reg (),
                                   c_end_addr.scale (), 0);
      cost += dlg.addr_reg_scale_cost (start_value->reg (), scale);
      if (addr_reg_values != NULL)
        {
          start_value->set_used ();
          new_reg = gen_reg_rtx (Pmode);
          rtx mult_rtx;
          if ((scale & (scale - 1)) == 0)
            {
              scale_t shift = 0;
              while (scale >>= 1) ++shift;
              mult_rtx = gen_rtx_ASHIFT
                (Pmode,
                 gen_rtx_REG (Pmode, start_value->reg ()),
                 GEN_INT (shift));
            }
          else
            mult_rtx = gen_rtx_MULT (Pmode,
                                     gen_rtx_REG (Pmode, start_value->reg ()),
                                     GEN_INT (scale));

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
      cost += dlg.addr_reg_plus_reg_cost (start_value->reg (),
                                          c_end_addr.base_reg ());
      if (addr_reg_values != NULL)
        {
          start_value->set_used ();
          new_reg = gen_reg_rtx (Pmode);
          rtx reg_plus_rtx =
            gen_rtx_PLUS (Pmode,
                          gen_rtx_REG (Pmode, start_value->reg ()),
                          gen_rtx_REG (Pmode, c_end_addr.base_reg ()));

          emit_move_insn (new_reg, reg_plus_rtx);
          addr_reg_values->push_back (reg_value (REGNO (new_reg), c_start_addr));
          start_value = &addr_reg_values->back ();
          *final_addr_regno = REGNO (new_reg);
        }
    }

  // Add displacement insns.
  if (c_start_addr.disp () + disp_min > c_end_addr.disp ()
      || c_start_addr.disp () + disp_max < c_end_addr.disp ())
    {
      // Make the displacement as small as possible, since
      // adding smaller constants often costs less.
      disp_t disp = c_end_addr.disp () - c_start_addr.disp () - disp_min;
      disp_t alt_disp = c_end_addr.disp () - c_start_addr.disp () - disp_max;
      if (abs (alt_disp) < abs (disp)) disp = alt_disp;

      cost += dlg.addr_reg_disp_cost (start_value->reg (), disp);
      if (addr_reg_values != NULL)
        {
          start_value->set_used ();
          new_reg = gen_reg_rtx (Pmode);
          rtx plus_rtx
            = gen_rtx_PLUS (Pmode,
                            gen_rtx_REG (Pmode, start_value->reg ()),
                            GEN_INT (disp));
          emit_move_insn (new_reg, plus_rtx);
          addr_reg_values->push_back (reg_value (REGNO (new_reg), c_end_addr));
          *final_addr_regno = REGNO (new_reg);
        }
    }

  if (insn != NULL_RTX)
    {
      rtx_insn* new_insns = get_insns ();
      end_sequence ();
      emit_insn_before (new_insns, insn);
    }

  return cost;
}

int sh_ams::access_sequence::try_modify_addr
(reg_value* start_value, const addr_expr& end_addr,
 disp_t disp_min, disp_t disp_max, delegate& dlg)
{
  return try_modify_addr (start_value, end_addr, disp_min, disp_max,
                          NULL, NULL, NULL, dlg);
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
          mems.clear ();
          find_mem_accesses (PATTERN (i), std::back_inserter (mems));

          for (std::vector<std::pair<rtx*, access_mode_t> >
	       ::reverse_iterator m = mems.rbegin (); m != mems.rend (); ++m)
	    add_new_access (as, i, m->first, m->second, reg_mod_insns);
         }
      log_msg ("Access sequence contents:\n\n");
      for (access_sequence::const_iterator it = as.begin();
           it != as.end(); ++it)
        {
          if (it->access_mode () == reg_mod)
            {
              log_msg ("reg_mod: r%d set to\n", it->address ().base_reg ());
              log_rtx (it->reg_mod_expr ());
              log_msg("\n-----\n\n");
            }
          else
            {
              log_msg ("m_original_addr_expr:\n");
              log_msg ("base: %d, index: %d, scale: %d, disp: %d\n",
                       it->original_address ().base_reg (),
                       it->original_address ().index_reg (),
                       it->original_address ().scale (),
                       it->original_address ().disp ());
              log_msg ("\nm_addr_expr:\n");
              log_msg ("base: %d, index: %d, scale: %d, disp: %d\n-----\n\n",
                       it->address ().base_reg (),
                       it->address ().index_reg (),
                       it->address ().scale (),
                       it->address ().disp ());
            }
        }
      log_msg ("\n\n");

      as.update_insn_stream (reg_mod_insns, m_delegate);
    }

  log_return (0, "\n\n");
}
