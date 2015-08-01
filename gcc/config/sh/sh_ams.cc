
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
#include "rtl-iter.h"

#include <algorithm>
#include <list>
#include <vector>
#include <set>

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
log_access_location (const sh_ams::access& a)
{
  if (a.insn () != NULL)
    log_msg ("at insn %d [bb %d]", INSN_UID (a.insn ()),
				   BLOCK_FOR_INSN (a.insn ())->index);
  else
    log_msg ("at insn: ?");
}

void
log_access (const sh_ams::access& a, bool log_alternatives = true)
{
  if (dump_file == NULL)
    return;

  if (a.access_type () == sh_ams::load)
    log_msg ("load ");
  else if (a.access_type () == sh_ams::store)
    log_msg ("store ");
  else if (a.access_type () == sh_ams::reg_mod)
    log_msg ("reg_mod ");
  else if (a.access_type () == sh_ams::reg_use)
    log_msg ("reg_use ");
  else
    gcc_unreachable ();

  log_access_location (a);

  if (a.access_type () == sh_ams::load || a.access_type () == sh_ams::store)
    log_msg ("  %smode (%d):",
             GET_MODE_NAME (a.mach_mode ()), a.access_size ());
  else if (a.access_type () == sh_ams::reg_mod)
    {
      log_msg ("  set ");
      log_rtx (a.address_reg ());
    }

  log_msg ("\n  original addr:   ");

  if (a.original_address ().is_invalid ())
    {
      if (a.addr_rtx ())
        log_rtx (a.addr_rtx ());
      else
        log_msg ("unknown");
    }
  else
    log_addr_expr (a.original_address ());

  if (!a.address ().is_invalid ())
    {
      log_msg ("\n  effective addr:  ");
      log_addr_expr (a.address ());
    }

  if (a.cost () == sh_ams::infinite_costs)
    log_msg ("\n  cost: infinite");
  else
    log_msg ("\n  cost: %d", a.cost ());

  if (a.removable ())
    log_msg ("\n  (removable)");
  if (!a.should_optimize ())
    log_msg ("\n  (won't be optimized)");
  if (a.is_trailing ())
    log_msg ("\n  (trailing)");
  if (a.inc_chain_length () > 1)
    log_msg ("\n  (chain length:  %d [inc] )", a.inc_chain_length ());
  if (a.dec_chain_length () > 1)
    log_msg ("\n  (chain length:  %d [dec] )", a.dec_chain_length ());

  if (a.access_type () == sh_ams::reg_use)
    {
      if (a.is_trailing ())
        {
          log_msg ("\n  used in:\n");
          for (std::vector<rtx_insn*>::const_iterator i
                 = a.trailing_insns ().begin ();
               i != a.trailing_insns ().end (); ++i)
            {
              log_msg ("  [bb %d] ", BLOCK_FOR_INSN (*i)->index);
              log_insn (*i);
              log_msg ("\n");
            }
        }
      else
        {
          log_msg ("\n  used in ");
          log_insn (a.insn ());
        }
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

void
log_access_sequence (const sh_ams::access_sequence& as,
		     bool log_alternatives = true)
{
  if (dump_file == NULL)
    return;

  log_msg ("access sequence:\n\n");
  for (sh_ams::access_sequence::const_iterator it = as.accesses ().begin ();
       it != as.accesses ().end (); ++it)
    {
      log_access (*it, log_alternatives);
      log_msg ("\n-----\n");
    }

  int c = as.cost ();
  if (c == sh_ams::infinite_costs)
    log_msg ("total cost: infinite");
  else
    log_msg ("total cost: %d", as.cost ());
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


// Find the memory accesses in X and add them to OUT, together with their
// access mode. ACCESS_TYPE indicates whether the next mem that we find is read
// or written to.
template <typename OutputIterator> void
find_mem_accesses (rtx& x, OutputIterator out,
		   sh_ams::access_type_t access_type = sh_ams::load)
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
      find_mem_accesses (SET_DEST (x), out, sh_ams::store);
      find_mem_accesses (SET_SRC (x), out, sh_ams::load);
      break;
    case CALL:
      find_mem_accesses (XEXP (x, 0), out, sh_ams::load);
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
  return optimize > 0;
}

sh_ams::access::access (rtx_insn* insn, rtx* mem, access_type_t access_type,
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
  m_inc_chain_length = 1;
  m_dec_chain_length = 1;
  m_alternatives_count = 0;
}

// Constructor for reg_mod accesses.
sh_ams::access::access (rtx_insn* insn, addr_expr original_addr_expr,
                        addr_expr addr_expr, rtx addr_rtx, rtx mod_reg,
                        int cost, bool removable)
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
  m_used = false;
  m_inc_chain_length = 1;
  m_dec_chain_length = 1;
  m_alternatives_count = 0;
}

// Constructor for reg_use accesses.
sh_ams::access::access (rtx_insn* insn, std::vector<rtx_insn*> trailing_insns,
                        rtx* reg_ref,
                        addr_expr original_addr_expr, addr_expr addr_expr)
{
  m_access_type = reg_use;
  m_cost = 0;
  m_insn = insn;
  m_trailing_insns = trailing_insns;
  m_mem_ref = reg_ref;
  m_original_addr_expr = original_addr_expr;
  m_addr_expr = addr_expr;
  m_addr_rtx = NULL;
  m_removable = false;
  m_should_optimize = true;
  m_addr_reg = NULL;
  m_used = false;
  m_inc_chain_length = 1;
  m_dec_chain_length = 1;
  m_alternatives_count = 0;
}


bool sh_ams::access::
matches_alternative (const alternative* alt) const
{
  const addr_expr &ae = original_address (), &alt_ae = alt->address ();

  if (ae.type () != alt_ae.type ())
    return false;

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
    extract_addr_expr ((XEXP (*mem, 0)), m_mode);

  std::vector<access*> inserted_reg_mods;
  addr_expr expr =
    extract_addr_expr ((XEXP (*mem, 0)), insn, insn,
                       m_mode, this, inserted_reg_mods);

  // If the effective address doesn't fit into an addr_expr,
  // don't try to optimize it.
  bool should_optimize = true;
  if (expr.is_invalid ())
    {
      expr = original_expr;
      should_optimize = false;

      // The reg modifications that were used to arrive at the address
      // shouldn't be removed in this case.
      std::for_each (inserted_reg_mods.begin (), inserted_reg_mods.end (),
                     std::mem_fun (&access::mark_unremovable));
    }

  accesses ().push_back (access (insn, mem, access_type,
                                 original_expr, expr, should_optimize));
  return accesses ().back ();
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
  if (accesses ().empty ())
    {
      accesses ().push_back (access (mod_insn, original_addr_expr, addr_expr,
                                     addr_rtx, reg, cost, removable));
      start_addresses ().add (&accesses ().back ());
      return accesses ().back ();
    }

  // Place accesses that have no insn (i.e. the ones that represent the initial
  // values of the hard regs) into the start of the sequence if they haven't
  // been placed there already.
  if (!mod_insn)
    {
      for (access_sequence::iterator as_it = accesses ().begin ();
           as_it != accesses ().end () && !as_it->insn (); ++as_it)
        {
          if (as_it->access_type () == reg_mod
              && as_it->address_reg () == reg)
            return *as_it;
        }

      accesses ().push_front (access (mod_insn, original_addr_expr, addr_expr,
                                      addr_rtx, reg, cost, removable));
      start_addresses ().add (&accesses ().front ());
      return accesses ().front ();
    }

  access_sequence::reverse_iterator as_it = accesses ().rbegin ();
  for (rtx_insn* i = insn; i != NULL_RTX; i = PREV_INSN (i))
    {
      if (!INSN_P (i) || !NONDEBUG_INSN_P (i))
        continue;

      // Keep track of the current insn in the sequence.
      while (as_it->insn () && INSN_UID (as_it->insn ()) == INSN_UID (i))
        {
          ++as_it;

          if (as_it == accesses ().rend () || !as_it->insn ())
            break;

          // If the reg_mod access is already inside the access
          // sequence, don't add it a second time.
          if (as_it->access_type () == reg_mod
              && as_it->insn () == mod_insn && as_it->address_reg () == reg
              && as_it->original_address ().base_reg ()
                  == original_addr_expr.base_reg ())
            return *as_it;

        }
      if (as_it == accesses ().rend () || INSN_UID (i) == INSN_UID (mod_insn))
        {
          // We found mod_insn inside the insn list, so we know where to
          // insert the access.
          accesses ().insert (as_it.base (),
                              access (mod_insn, original_addr_expr, addr_expr,
                                      addr_rtx, reg, cost, removable));
          start_addresses ().add (&(*as_it));
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
                                      bool removable, bool use_as_start_addr)
{
  accesses ().insert (insert_before,
                      access (mod_insn, original_addr_expr, addr_expr,
                              NULL_RTX, reg, cost, removable));
  access_sequence::iterator inserted = (--insert_before);
  if (use_as_start_addr)
    start_addresses ().add (&(*inserted));
  return *inserted;
}

// Create a reg_use access and place it before INSERT_BEFORE
// in the access sequence.
sh_ams::access&
sh_ams::access_sequence::add_reg_use (access_sequence::iterator insert_before,
                                      const addr_expr& original_addr_expr,
                                      const addr_expr& addr_expr,
                                      rtx* reg_ref, rtx_insn* use_insn)
{
  access_sequence::iterator inserted =
    accesses ().insert (insert_before,
                        access (use_insn, std::vector<rtx_insn*> (), reg_ref,
                                original_addr_expr, addr_expr));
  return *inserted;
}

// Create a trailing reg_use access and place it before INSERT_BEFORE
// in the access sequence.
sh_ams::access&
sh_ams::access_sequence::add_reg_use (access_sequence::iterator insert_before,
                                      const addr_expr& original_addr_expr,
                                      const addr_expr& addr_expr,
                                      rtx* reg_ref,
                                      std::vector<rtx_insn*> use_insns)
{
  access_sequence::iterator inserted =
    accesses ().insert (insert_before,
                        access (NULL, use_insns, reg_ref,
                                original_addr_expr, addr_expr));
  return *inserted;
}

// Remove the access ACC from the sequence. Return an iterator
// pointing to the next access.
sh_ams::access_sequence::iterator
sh_ams::access_sequence::remove_access (access_sequence::iterator acc)
{
  if (acc->access_type () == reg_mod)
    start_addresses ().remove (&(*acc));
  return accesses ().erase (acc);
}

sh_ams::access_sequence::iterator
sh_ams::access_sequence::first_mem_access (void)
{
  for (iterator i = accesses ().begin (); i != accesses ().end (); ++i)
    if (i->access_type () == load || i->access_type () == store)
      return i;

  return accesses ().end ();
}

sh_ams::access_sequence::iterator
sh_ams::access_sequence::next_mem_access (iterator i)
{
  if (i == accesses ().end ())
    return i;

  for (++i; i != accesses ().end (); ++i)
    if (i->access_type () == load || i->access_type () == store)
      return i;

  return accesses ().end ();
}

sh_ams::access_sequence::iterator
sh_ams::access_sequence::first_access_to_optimize (void)
{
  for (iterator i = accesses ().begin (); i != accesses ().end (); ++i)
    if ((i->access_type () == load || i->access_type () == store
         || i->access_type () == reg_use
         || (i->access_type () == reg_mod
             && i->original_address ().is_invalid ()
             && !i->address ().is_invalid ()))
        && i->should_optimize ()
        && !i->is_trailing ())
      return i;

  return accesses ().end ();
}

sh_ams::access_sequence::iterator
sh_ams::access_sequence::next_access_to_optimize (iterator i)
{
  if (i == accesses ().end ())
    return i;

  for (++i; i != accesses ().end (); ++i)
    if ((i->access_type () == load || i->access_type () == store
         || i->access_type () == reg_use
         || (i->access_type () == reg_mod
             && i->original_address ().is_invalid ()
             && !i->address ().is_invalid ()))
        && i->should_optimize ()
        && !i->is_trailing ())
      return i;

  return accesses ().end ();
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
// If the register was modified because of an auto-inc/dec memory
// access, set the mode of the access into auto_mod_mode.
// FIXME: make use of other info such as REG_EQUAL notes.
void sh_ams::find_reg_value (rtx reg, rtx_insn* insn, rtx* mod_expr,
                             rtx_insn** mod_insn,
                             machine_mode* auto_mod_mode)
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
                  *auto_mod_mode = GET_MODE (*(m->first));
                  return;
                }
            }
        }
    }
  *mod_expr = reg;
}

// Try to create an ADDR_EXPR struct of the form
// base_reg + index_reg * scale + disp from the access expression X.
// If AS is not NULL, trace the original value of the registers in X
// as far back as possible, and add all the address reg modifying insns
// to AS as reg_mod accesses.
// INSN is the insn in which the access happens.  ROOT_INSN is the INSN
// argument that was passed to the function at the top level of recursion
// (used as the start insn when calling add_reg_mod).  These are not used
// if the registers in X aren't expanded.
sh_ams::addr_expr
sh_ams::extract_addr_expr (rtx x, rtx_insn* insn, rtx_insn *root_insn,
			   machine_mode mem_mach_mode,
			   access_sequence* as,
                           std::vector<access*>& inserted_reg_mods)
{
  addr_expr op0 = make_invalid_addr ();
  addr_expr op1 = make_invalid_addr ();
  disp_t disp;
  scale_t scale;
  rtx base_reg, index_reg;
  bool expand_regs = (as != NULL);

  if (x == NULL_RTX)
    return make_invalid_addr ();

  enum rtx_code code = GET_CODE (x);

  // If X is an arithmetic operation, first create ADDR_EXPR structs
  // from its operands. These will later be combined into a single ADDR_EXPR.
  if (code == PLUS || code == MINUS || code == MULT || code == ASHIFT)
    {
      op0 = extract_addr_expr
        (XEXP (x, 0), insn, root_insn, mem_mach_mode, as,
         inserted_reg_mods);
      op1 = extract_addr_expr
        (XEXP (x, 1), insn, root_insn, mem_mach_mode, as,
         inserted_reg_mods);
      if (op0.is_invalid () || op1.is_invalid ())
        return make_invalid_addr ();
    }
  else if (code == NEG)
    {
      op1 = extract_addr_expr
        (XEXP (x, 0), insn, root_insn, mem_mach_mode, as,
         inserted_reg_mods);
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
      bool use_post_disp = (!expand_regs || insn != root_insn);

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
                                   inserted_reg_mods);
          if (expand_regs)
            return op1;
          return post_mod_addr (op1.base_reg (), op1.disp ());
        case PRE_MODIFY:
          op1 = extract_addr_expr (XEXP (x, 1),
                                   insn, root_insn,
                                   mem_mach_mode, as,
                                   inserted_reg_mods);
          if (expand_regs)
            return op1;
          return pre_mod_addr (op1.base_reg (), op1.disp ());
        default:
          return make_invalid_addr ();
        }

      op1 = extract_addr_expr
        (XEXP (x, 0), insn, root_insn, mem_mach_mode, as,
         inserted_reg_mods);
      disp += op1.disp ();

      if (expand_regs)
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
      if (expand_regs)
        {
          // Find the expression that the register was last set to
          // and convert it to an addr_expr.
          rtx reg_value;
          rtx_insn *reg_mod_insn = NULL;
          machine_mode auto_mod_mode;

          find_reg_value (x, insn, &reg_value, &reg_mod_insn, &auto_mod_mode);
          // Stop expanding the reg if we reach a hardreg -> pseudo reg
          // copy, or if the reg can't be expanded any further.
          if (reg_value != NULL_RTX && REG_P (reg_value)
              && (REGNO (reg_value) == REGNO (x)
                  || HARD_REGISTER_P (reg_value)))
            {
              // Add a reg_mod access that sets the reg to itself.
              // This makes it easier for the address modification
              // generator to find all possible starting addresses.
              if (insn && root_insn)
                as->add_reg_mod (root_insn,
                                 make_reg_addr (x), make_reg_addr (x),
                                 reg_mod_insn, x);
              return make_reg_addr (x);
            }

          access* inserted_mods_start = inserted_reg_mods.empty ()
                                          ? NULL
                                          : inserted_reg_mods.back ();

          // Expand the register's value further.  If the register was
          // modified because of an auto-inc/dec memory access, pass
          // down the machine mode of that access.
          addr_expr reg_addr_expr = extract_addr_expr
            (reg_value, reg_mod_insn, root_insn,
             find_reg_note (reg_mod_insn, REG_INC, NULL_RTX)
               ? auto_mod_mode
               : mem_mach_mode,
             as, inserted_reg_mods);

          // Place all the insns that are used to arrive at the address
          // into AS in the form of reg_mod accesses that can be replaced
          // during address mod generation.
          // For auto-mod mem accesses, insert a reg_mod that sets X to itself.
          access* new_reg_mod = NULL;
          if (insn && root_insn)
            {
              addr_expr original_reg_addr_expr
                = find_reg_note (reg_mod_insn, REG_INC, NULL_RTX)
                  ? make_reg_addr (x)
                  : extract_addr_expr (reg_value, mem_mach_mode);
              new_reg_mod = &as->add_reg_mod (root_insn,
                                              original_reg_addr_expr,
                                              reg_addr_expr,
                                              reg_mod_insn, x,
                                              infinite_costs,
                                              true);
              inserted_reg_mods.push_back (new_reg_mod);
            }

          // If the expression is something AMS can't handle, use the original
          // reg instead, and update the INSERTED_MOD to store the reg's value
          // as an rtx instead of an addr_expr.
          if (reg_addr_expr.is_invalid ())
            {
              if (new_reg_mod)
                {
                  new_reg_mod->update_original_address (0, reg_value);

                  // Set all reg_mod accesses that were added while expanding this
                  // register to "unremovable".
                  while (!inserted_reg_mods.empty ())
                    {
                      access* a = inserted_reg_mods.back ();
                      if (a == inserted_mods_start)
                        break;
                      a->mark_unremovable ();
                      inserted_reg_mods.pop_back ();
                    }
                }

              // Add an (rx = rx) reg_mod access to help the
              // address modification generator.
              if (insn && root_insn)
                as->add_reg_mod (root_insn, make_reg_addr (x), make_reg_addr (x),
                                 reg_mod_insn, x);

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
      if (op1.has_index_reg () && op1.scale () != -1)
        break;

      if (op1.has_index_reg ())
        scale = op1.scale ();
      else
        scale = 1;

      op1 = non_mod_addr (op1.index_reg (), op1.base_reg (),
                          -scale, -op1.disp ());
      if (code == NEG)
        return op1;

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
      else
        break;

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
          else
            break;
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
      else
        break;
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
      else
        break;
      return non_mod_addr (invalid_regno, index_reg,
                           scale, op0.disp () * op1.disp ());
    default:
      break;
    }
  return make_invalid_addr ();
}

// Internal function of collect_addr_reg_uses.
template <typename OutputIterator> void
sh_ams::collect_addr_reg_uses_1 (access_sequence& as, rtx addr_reg,
                                 rtx_insn *start_insn, basic_block bb,
                                 std::vector<basic_block>& visited_bb,
                                 rtx abort_at_insn, OutputIterator out,
                                 bool skip_addr_reg_mods,
                                 bool stay_in_curr_bb, bool stop_after_first)
{
  if (bb == NULL)
    return;

  log_msg ("collect_addr_reg_uses_1 [bb %d]\n", bb->index);

  if (BB_END (bb) == NULL_RTX)
    log_return_void ("[bb %d] BB_END is null\n", bb->index);

  if (start_insn == NULL_RTX)
    log_return_void ("[bb %d] start_insn is null\n", bb->index);

  if (abort_at_insn == start_insn)
    return;

  rtx end_insn = NEXT_INSN (BB_END (bb));

  for (rtx_insn *i = NEXT_INSN (start_insn); i != end_insn; i = NEXT_INSN (i))
    {
      if (INSN_P (i) && NONDEBUG_INSN_P (i)
          && collect_addr_reg_uses_2 (as, addr_reg, i, PATTERN (i),
                                      out, skip_addr_reg_mods))
        {
          log_msg ("found addr reg use in [bb %d] at insn:\n", bb->index);
          log_insn (i);
          log_msg ("\n");
          if (stop_after_first)
            return;
        }

      if (abort_at_insn != NULL_RTX && abort_at_insn == i)
	return;
    }

  if (stay_in_curr_bb)
    return;

  for (edge_iterator ei = ei_start (bb->succs); !ei_end_p (ei); ei_next (&ei))
    {
      basic_block succ_bb = ei_edge (ei)->dest;

      if (std::find (visited_bb.begin (), visited_bb.end (), succ_bb)
          != visited_bb.end ())
        {
          log_msg ("[bb %d] already visited\n", succ_bb->index);
          continue;
        }

      visited_bb.push_back (succ_bb);
      collect_addr_reg_uses_1 (as, addr_reg, BB_HEAD (succ_bb),
                               succ_bb, visited_bb,
                               abort_at_insn, out,
                               skip_addr_reg_mods,
                               stay_in_curr_bb,
                               stop_after_first);
    }
}

// The recursive part of collect_addr_reg_uses.
template <typename OutputIterator> bool
sh_ams::collect_addr_reg_uses_2 (access_sequence& as, rtx addr_reg,
                                 rtx_insn *insn, rtx& x, OutputIterator out,
                                 bool skip_addr_reg_mods)
{

  bool found = false;
  switch (GET_CODE (x))
    {
    case REG:
      if (x == addr_reg || (!addr_reg && as.addr_regs ().find (x)
                            != as.addr_regs ().end ()))
        {
          *out++ = std::make_pair (&x, insn);
          return true;
        }
      break;
    case MEM:
      // Don't add regs used in memory accesses.
      break;
    case PARALLEL:
      for (int i = 0; i < XVECLEN (x, 0); i++)
        found |= collect_addr_reg_uses_2 (as, addr_reg, insn,
                                          XVECEXP (x, 0, i), out,
                                          skip_addr_reg_mods);
      break;
    case SET:

      if (skip_addr_reg_mods)
        {
          if (SET_DEST (x) == addr_reg)
            break;
          if (!addr_reg && as.addr_regs ().find (SET_DEST (x))
              != as.addr_regs ().end ())
            break;
        }

      found |= collect_addr_reg_uses_2 (as, addr_reg, insn, SET_SRC (x),
                                        out, skip_addr_reg_mods);
      break;
    default:
      if (UNARY_P (x) || ARITHMETIC_P (x))
        {
          // If the address reg is inside a (plus reg (const_int ...)) rtx,
          // add the whole rtx instead of just the addr reg.
          addr_expr use_expr = extract_addr_expr (x);
          if (!use_expr.is_invalid () && use_expr.has_no_index_reg ()
              && use_expr.has_base_reg () && use_expr.has_disp ()
              && (use_expr.base_reg () == addr_reg
                  || (!addr_reg && as.addr_regs ().find (use_expr.base_reg ())
                      != as.addr_regs ().end ())))
            {
              *out++ = std::make_pair (&x, insn);
              return true;
            }

          for (int i = 0; i < GET_RTX_LENGTH (GET_CODE (x)); i++)
            found |= collect_addr_reg_uses_2 (as, addr_reg, insn,
                                              XEXP (x, i),
                                              out, skip_addr_reg_mods);
        }
      break;
    }
  return found;
}

// Collect uses of the address registers in all basic blocks that are reachable
// from the specified insn. The reg(s) that we search for is ADDR_REG, or the
// address regs of the access sequence AS if ADDR_REG is null.
// If 'abort_at_insn' is not null, abort at that insn. If the insn
// 'abort_at_insn' has a reg-use, it is also collected.
// If SKIP_ADDR_REG_MODS is true, the reg uses that happen during an address reg
// modification don't get collected.  If STAY_IN_CURR_BB is true, only the basic
// block of the starting insn is searched through.  If STOP_AFTER_FIRST is true,
// we only collect the first addr reg use in a BB.
template <typename OutputIterator> void
sh_ams::collect_addr_reg_uses (access_sequence& as, rtx addr_reg,
                               rtx_insn *start_insn,
                               rtx abort_at_insn, OutputIterator out,
                               bool skip_addr_reg_mods,
                               bool stay_in_curr_bb, bool stop_after_first)
{
  log_msg ("\ncollecting address reg uses\nstart_insn = ");
  log_insn (start_insn);

  std::vector<basic_block> visited_bb;
  visited_bb.reserve (32);

  collect_addr_reg_uses_1 (as, addr_reg, start_insn, BLOCK_FOR_INSN (start_insn),
                           visited_bb, abort_at_insn, out,
                           skip_addr_reg_mods, stay_in_curr_bb, stop_after_first);
}

// Split the access sequence pointed to by AS_IT into multiple sequences,
// grouping the accesses according to their base register.
// The new sequences are placed into SEQUENCES in place of the old one.
// Return an iterator to the next sequence after the newly inserted sequences.
std::list<sh_ams::access_sequence>::iterator
sh_ams::split_access_sequence (std::list<access_sequence>::iterator as_it,
                               std::list<access_sequence>& sequences)
{
  typedef std::map<rtx, std::pair<access_sequence*, std::set<rtx> > > new_seq_map;

  new_seq_map new_seqs;
  access_sequence& as = *as_it;

  // Create a new access sequence for every unique base register of an
  // effective address.  Also create one for unknown/complicated addresses.
  for (sh_ams::access_sequence::iterator accs = as.accesses ().begin ();
       accs != as.accesses ().end (); ++accs)
    {
      if (accs->access_type () == reg_mod
          && !(accs->original_address ().is_invalid ()
               && !accs->address ().is_invalid ()))
        continue;

      rtx key = accs->address ().is_invalid () ? NULL
                                               : accs->address ().base_reg ();
      new_seq_map::iterator new_seq = new_seqs.find (key);
      if (new_seq == new_seqs.end ())
        {
          access_sequence& new_as =
            *sequences.insert (as_it, access_sequence (as.mod_insns ()));
          new_as.mod_insns ()->use ();
          new_seqs.insert (std::make_pair (key,
                                           std::make_pair (&new_as,
                                                           std::set<rtx> ())));
        }
    }

  // Add each memory and reg_use access from the original sequence to the
  // appropriate new sequence.  Also add the reg_mod accesses to all sequences
  // where they are used to calculate addresses.
  sh_ams::access_sequence::iterator last_mem_acc = as.accesses ().end ();
  for (sh_ams::access_sequence::reverse_iterator accs = as.accesses ().rbegin ();
       accs != as.accesses ().rend (); ++accs)
    {
      if (accs->access_type () == reg_mod
          // reg_mods with no original address are split
          // like the memory and reg_use accesses.
          && !(accs->original_address ().is_invalid ()
               && !accs->address ().is_invalid ()))
        split_access_sequence_1 (new_seqs, *accs, true);
      else
        {
          if (last_mem_acc == as.accesses ().end ())
            {
              last_mem_acc = accs.base ();
              --last_mem_acc;
            }
          rtx key = accs->address ().is_invalid () ? NULL
                                                   : accs->address ().base_reg ();
          std::pair<access_sequence*, std::set<rtx> >& new_seq = new_seqs[key];
          access_sequence& as = *new_seq.first;
          std::set<rtx>& addr_regs = new_seq.second;

          split_access_sequence_2 (addr_regs, *accs);
          as.accesses ().push_front (*accs);
        }
    }

  // Add remaining reg_mod accesses from the end of the original sequence.
  for (sh_ams::access_sequence::iterator accs = last_mem_acc;
       accs != as.accesses ().end (); ++accs)
    {
      if (accs->access_type () == reg_mod
          && !(accs->original_address ().is_invalid ()
               && !accs->address ().is_invalid ()))
        split_access_sequence_1 (new_seqs, *accs, false);
    }

  // Remove the old sequence and return the next element after the
  // newly inserted sequences.
  as_it->mod_insns ()->release ();
  return sequences.erase (as_it);
}

// Internal function of split_access_sequence.  Adds the reg_mod access ACC to
// those sequences in NEW_SEQS that use it in their address calculations.
void sh_ams::split_access_sequence_1 (
  std::map<rtx, std::pair<sh_ams::access_sequence*, std::set<rtx> > >& new_seqs,
  sh_ams::access& acc, bool add_to_front)
{
  typedef std::map<rtx, std::pair<access_sequence*, std::set<rtx> > > new_seq_map;

  for (new_seq_map::iterator it = new_seqs.begin ();
       it != new_seqs.end (); ++it)
    {
      access_sequence& as = *it->second.first;
      std::set<rtx>& addr_regs = it->second.second;

      // Add the reg_mod access only if it's used to calculate
      // one of the addresses in this new sequence.
      if (addr_regs.find (acc.address_reg ()) == addr_regs.end ())
        continue;

      split_access_sequence_2 (addr_regs, acc);
      if (add_to_front)
        as.accesses ().push_front (acc);
      else
        as.accesses ().push_back (acc);
      as.start_addresses ().add (&as.accesses ().front ());
    }
}

// Internal function of split_access_sequence.  Adds all the address registers
// referenced by ACC to ADDR_REGS.
void sh_ams::split_access_sequence_2 (std::set<rtx>& addr_regs,
                                      sh_ams::access& acc)
{
  if (acc.address_reg ())
    addr_regs.insert (acc.address_reg ());
  if (!acc.original_address ().is_invalid ())
    {
      if (acc.original_address ().has_base_reg ())
        addr_regs.insert (acc.original_address ().base_reg ());
      if (acc.original_address ().has_index_reg ())
        addr_regs.insert (acc.original_address ().index_reg ());
    }
  else if (acc.addr_rtx ())
    {
      // If the address is stored as an RTX, search it for regs.
      subrtx_var_iterator::array_type array;
      FOR_EACH_SUBRTX_VAR (it, array, acc.addr_rtx (), NONCONST)
        {
          rtx x = *it;
          if (REG_P (x))
            addr_regs.insert (x);
        }
    }
}

// Generate the address modifications needed to arrive at the addresses in
// the access sequence.  They are inserted in the form of reg_mod accesses
// between the regular accesses.
// FIXME: Handle trailing reg_mods/uses.
void sh_ams::access_sequence::
gen_address_mod (delegate& dlg)
{
  log_msg ("Generating address modifications\n");

  // Remove the original reg_mod accesses.
  for (access_sequence::iterator accs = accesses ().begin ();
       accs != accesses ().end ();)
    {
      if (accs->removable ())
        accs = remove_access (accs);
      else
        ++accs;
    }

  for (access_sequence::iterator accs = first_access_to_optimize ();
       accs != accesses ().end (); accs = next_access_to_optimize (accs))
    gen_min_mod (accs, dlg, dlg.lookahead_count (*this, accs), true);

  for (access_sequence::iterator accs = accesses ().begin ();
       accs != accesses ().end ();)
    {
      if (accs->access_type () == reg_mod)
        {
          // Mark the reg_mod accesses as "unused" again.
          accs->reset_used ();

          // Remove any unused reg <- constant copy that might have been
          // added while trying different accesses.
          if (accs->original_address ().has_no_base_reg ()
              && accs->original_address ().has_no_index_reg ())
            {
              access_sequence::iterator next_acc = accs;
              ++next_acc;
              if (!reg_used_in_sequence (accs->address_reg (), next_acc))
                {
                  accs = remove_access (accs);
                  continue;
                }
            }
        }
      ++accs;
    }
}

// Generate reg_mod accesses needed to arrive at the address in ACC and
// return the cost of the address modifications.
// If RECORD_IN_SEQUENCE is false, don't insert the actual modifications
// in the sequence, only calculate the cost.
int sh_ams::access_sequence::
gen_min_mod (access_sequence::iterator acc, delegate& dlg,
             int lookahead_num, bool record_in_sequence)
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
  mod_tracker tracker;

  access_sequence::iterator next_acc = lookahead_num
                                     ? next_access_to_optimize (acc)
                                     : accesses ().end ();

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
        find_min_mod_cost (end_base, acc,
                           alt_ae.disp_min (), alt_ae.disp_max (),
                           alt_ae.type (), dlg);

      if (base_mod_cost.cost == infinite_costs)
        continue;

      alt_min_cost += base_mod_cost.cost;

      min_mod_cost_result index_mod_cost;

      if (alt_ae.has_index_reg ())
        {
          index_mod_cost =
            find_min_mod_cost (end_index, acc, 0, 0, alt_ae.type (), dlg);
          if (index_mod_cost.cost == infinite_costs)
            continue;

          alt_min_cost += index_mod_cost.cost;
        }

      // Calculate the costs of the next access when this alternative is used.
      // This is done by inserting the address modifications of this alt into the
      // sequence, calling gen_min_mod on the next access and then removing the
      // inserted address mods.
      if (next_acc != accesses ().end ())
        {
          gen_mod_for_alt (*alt,
                           base_mod_cost.min_start_addr,
                           index_mod_cost.min_start_addr,
                           end_base, end_index,
                           acc, tracker, dlg);

          int next_cost = gen_min_mod (next_acc, dlg, lookahead_num-1, false);
          tracker.reset_changes (*this);

          if (next_cost == infinite_costs)
            continue;
          alt_min_cost += next_cost;
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
      log_msg ("  min alternative: %d  min costs = %d\n",
               (int)(min_alternative - acc->begin_alternatives ()),
               min_cost);
      gen_mod_for_alt (*min_alternative,
                       min_start_base, min_start_index,
                       min_end_base, min_end_index,
                       acc, tracker, dlg);
    }

  return min_cost;
}

// Generate the address modifications needed to arrive at END_BASE and
// END_INDEX from START_BASE/INDEX when using ALTERNATIVE as the access
// alternative.  Record any changes to the sequence in MOD_TRACKER.
void sh_ams::access_sequence::
gen_mod_for_alt (access::alternative& alternative,
                 access* start_base,
                 access* start_index,
                 const addr_expr& end_base,
                 const addr_expr& end_index,
                 access_sequence::iterator acc,
                 mod_tracker& mod_tracker,
                 delegate& dlg)
{
  // Insert the modifications needed to arrive at the address
  // in the base reg.
  mod_addr_result base_insert_result =
    try_modify_addr (start_base, end_base,
                     alternative.address ().disp_min (),
                     alternative.address ().disp_max (),
                     alternative.address ().type (),
                     acc, mod_tracker, dlg);

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
                         acc, mod_tracker, dlg);
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
  acc->update_original_address (alternative.costs (), new_addr_expr);
}

// Return all the start addresses that could be used to arrive at END_ADDR.
//
// FIXME: Avoid copying the list elements over and over.
std::list<sh_ams::access*> sh_ams::access_sequence::start_addr_list::
get_relevant_addresses (const addr_expr& end_addr)
{
  std::list<access*> start_addrs;

  // Constant displacements can always be used as start addresses.
  start_addrs.insert (start_addrs.end (),
                      m_const_addresses.begin (),
                      m_const_addresses.end ());

  // Addresses containing registers might be used if they have a
  // register in common with the end address.
  std::pair <std::multimap<rtx, access*>::iterator,
             std::multimap<rtx, access*>::iterator> matching_range;
  if (end_addr.has_base_reg ())
    {
      matching_range = m_reg_addresses.equal_range (end_addr.base_reg ());
      for (std::multimap<rtx, access*>::iterator it = matching_range.first;
           it != matching_range.second; ++it)
        start_addrs.push_back (it->second);
    }
  if (end_addr.has_index_reg ())
    {
      matching_range = m_reg_addresses.equal_range (end_addr.index_reg ());
      for (std::multimap<rtx, access*>::iterator it = matching_range.first;
           it != matching_range.second; ++it)
        start_addrs.push_back (it->second);
    }
  return start_addrs;
}

// Add START_ADDR to the list of available start addresses.
void sh_ams::access_sequence::
start_addr_list::add (access* start_addr)
{
  if (start_addr->address ().is_invalid ())
    return;

  // If the address has a base or index reg, add it to M_REG_ADDRESSES.
  if (start_addr->address ().has_base_reg ())
    m_reg_addresses.insert (std::make_pair (start_addr->address ().base_reg (),
                                            start_addr));
  if (start_addr->address ().has_index_reg ())
    m_reg_addresses.insert (std::make_pair (start_addr->address ().index_reg (),
                                            start_addr));

  // Otherwise, add it to the constant list.
  if (start_addr->address ().has_no_base_reg ()
      && start_addr->address ().has_no_index_reg ())
    m_const_addresses.push_back (start_addr);
}

// Remove START_ADDR from the list of available start addresses.
void sh_ams::access_sequence::
start_addr_list::remove (access* start_addr)
{
  std::pair <std::multimap<rtx, access*>::iterator,
             std::multimap<rtx, access*>::iterator> matching_range;
  if (start_addr->address ().has_base_reg ())
    {
      matching_range
        = m_reg_addresses.equal_range (start_addr->address ().base_reg ());
      for (std::multimap<rtx, access*>::iterator it = matching_range.first;
           it != matching_range.second; ++it)
        {
          if (it->second == start_addr)
            {
              m_reg_addresses.erase (it);
              break;
            }
        }
    }
  if (start_addr->address ().has_index_reg ())
    {
      matching_range
        = m_reg_addresses.equal_range (start_addr->address ().index_reg ());
      for (std::multimap<rtx, access*>::iterator it = matching_range.first;
           it != matching_range.second; ++it)
        {
          if (it->second == start_addr)
            {
              m_reg_addresses.erase (it);
              break;
            }
        }
    }

  if (start_addr->address ().has_no_base_reg ()
      && start_addr->address ().has_no_index_reg ())
    m_const_addresses.remove (start_addr);
}

// Write the sequence into the insn stream.
void sh_ams::access_sequence::
update_insn_stream (std::list<mod_insn_list>& sequence_mod_insns)
{
  log_msg ("Updating insn list\n");

  // The original insns are no longer used by this sequence.
  mod_insns ()->release ();

  // If the original address modifying insns were only used by this
  // sequence, remove them.
  if (!mod_insns ()->is_used ())
    {
      for (std::vector<rtx_insn*>::iterator
             it = mod_insns ()->insns ().begin ();
           it != mod_insns ()->insns ().end (); ++it)
        set_insn_deleted (*it);
      sequence_mod_insns.erase (mod_insns ());
    }

  // Create a new insn list for this sequence.
  sequence_mod_insns.push_back (mod_insn_list ());
  std::list<mod_insn_list>::iterator new_insns = sequence_mod_insns.end ();
  --new_insns;
  update_mod_insns (new_insns);

  bool sequence_started = false;
  rtx_insn* last_insn = NULL;

  for (access_sequence::iterator accs = accesses ().begin ();
       accs != accesses ().end (); ++accs)
    {
      if (accs->insn ())
        last_insn = accs->insn ();

      if (accs->access_type () == reg_mod)
        {
          // Skip accesses with unknown values, the ones that
          // don't modify anything, or those that already have
          // an insn.
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
          if (accs->insn ())
	    {
	      log_msg ("access already has an insn\n");
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
          else
            {
              if (accs->original_address ().has_index_reg ())
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
            }

          accs->update_insn (emit_move_insn (accs->address_reg (), new_val));
          mod_insns ()->insns ().push_back (accs->insn ());
        }
      else if (accs->access_type () == reg_use && !accs->is_trailing ())
        {
          gcc_assert (accs->original_address ().has_base_reg ());
          accs->update_use_expr (accs->original_address ().base_reg ());
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

      if (sequence_started && (accs->access_type () == load
                               || accs->access_type () == store
                               || accs->access_type () == reg_use))
        {
          rtx_insn* new_insns = get_insns ();
          end_sequence ();
          sequence_started = false;

          log_msg ("emitting new insns = \n");
          log_rtx (new_insns);
          log_msg ("\nbefore insn\n");
          log_insn (accs->insn ());
          log_msg ("\n");
          emit_insn_before (new_insns, accs->insn ());
        }
    }

  // Emit remaining address modifying insns after the last insn in the access.
  if (sequence_started && last_insn)
    {
      rtx_insn* new_insns = get_insns ();
      end_sequence ();

      log_msg ("emitting new insns = \n");
      log_rtx (new_insns);
      log_msg ("\nafter insn\n");
      log_insn (last_insn);
      log_msg ("\n");
      emit_insn_after (new_insns, last_insn);
    }
}

// Get the total cost of using this access sequence.
int sh_ams::access_sequence::cost (void) const
{
  int cost = 0;
  for (access_sequence::const_iterator accs = accesses ().begin ();
       accs != accesses ().end () && cost != infinite_costs; ++accs)
    cost += accs->cost ();
  return cost;
}

// Recalculate the cost of the accesses in the sequence.
void sh_ams::access_sequence::update_cost (delegate& dlg)
{
  for (access_sequence::iterator accs = accesses ().begin ();
       accs != accesses ().end (); ++accs)
    {
      if (accs->access_type () == load || accs->access_type () == store)
        {
          // Skip this access if it won't be optimized.
          if (!accs->should_optimize ())
            {
              accs->update_cost (0);
              continue;
            }

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
      else if (accs->access_type () == reg_mod)
        {
          // Skip this access if the original address doesn't fit into an
          // addr_expr or if it's a trailing access.
          if (accs->original_address ().is_invalid () || accs->is_trailing ())
            {
              accs->update_cost (0);
              continue;
            }

          int cost = 0;
          const addr_expr &ae = accs->original_address ();

          // Scaling costs
          if (ae.has_no_base_reg () && ae.has_index_reg ()
              && ae.scale () != 1)
            cost += dlg.addr_reg_scale_cost (ae.index_reg (), ae.scale (),
                                             *this, accs);

          // Costs for adding or subtracting another reg
          else if (ae.has_no_disp () && std::abs (ae.scale ()) == 1
                   && ae.has_base_reg () && ae.has_index_reg ())
            cost += dlg.addr_reg_plus_reg_cost (ae.index_reg (), ae.base_reg (),
                                                *this, accs);

          // Constant displacement costs
          else if (ae.has_base_reg () && ae.has_no_index_reg ()
                   && ae.has_disp ())
            cost += dlg.addr_reg_disp_cost (ae.base_reg (), ae.disp (),
                                            *this, accs);

          // Constant loading costs
          else if (ae.has_no_base_reg () && ae.has_no_index_reg ())
            cost += dlg.const_load_cost (accs->address_reg (), ae.disp (),
                                         *this, accs);

          // If none of the previous branches were taken, the reg_mod access
          // is a (reg <- reg) copy, and doesn't have any modification cost.
          else
            {
              gcc_assert (ae.has_base_reg () && ae.has_no_index_reg ()
                          && ae.has_no_disp ());
              cost = 0;
            }

          // Cloning costs
          cost += get_clone_cost (accs, dlg);

          accs->update_cost (cost);
        }
    }

  // Mark the reg_mod accesses as "unused" again.
  std::for_each (accesses ().begin (), accesses ().end (),
                 std::mem_fun_ref (&access::reset_used));
}

// Get the cloning costs associated with ACC, if any.
int sh_ams::access_sequence::get_clone_cost (access_sequence::iterator &acc,
                                             delegate& dlg)
{
  rtx reused_reg = NULL;
  if (acc->original_address ().has_base_reg ())
    reused_reg = acc->original_address ().base_reg ();
  else if (acc->original_address ().has_index_reg ())
    reused_reg = acc->original_address ().index_reg ();
  else
    return 0;

  // There's no cloning cost for accesses that set the reg to itself.
  if (reused_reg == acc->address_reg ())
    return 0;

  for (access_sequence::iterator prev_accs = accesses ().begin (); ; ++prev_accs)
    {
      if (prev_accs->access_type () == reg_mod
          && prev_accs->address_reg () == reused_reg)
        {
          // If the reused reg is already used by another access,
          // we'll have to clone it.
          if (prev_accs->is_used ())
            return  dlg.addr_reg_clone_cost (reused_reg, *this, acc);

          // Otherwise, we can use it without any cloning penalty.
          prev_accs->set_used ();
          return 0;
        }
    }
  gcc_unreachable ();
}

// Return true if the cost of this sequence is already minimal and
// can't be improved further (i.e. if all memory accesses use the
// cheapest alternative and there are no reg_mods with nonzero cost).
bool sh_ams::access_sequence::cost_already_minimal (void) const
{
  for (access_sequence::const_iterator accs = accesses ().begin ();
       accs != accesses ().end (); ++accs)
    {
      if (accs->access_type () == load || accs->access_type () == store)
        {
          for (const access::alternative* alt = accs->begin_alternatives ();
               alt != accs->end_alternatives (); ++alt)
            {
              if (alt->costs () < accs->cost ())
                return false;
            }
        }
      else if (accs->access_type () == reg_mod && accs->cost () > 0)
        return false;
    }
  return true;
}

// Find the cheapest way END_ADDR can be arrived at from one of the addresses
// in the sequence.
// Return the start address that can be changed into END_ADDR with the least
// cost and the actual cost.
sh_ams::access_sequence::min_mod_cost_result
sh_ams::access_sequence::
find_min_mod_cost (const addr_expr& end_addr,
                   access_sequence::iterator insert_before,
                   disp_t disp_min, disp_t disp_max,
                   addr_type_t addr_type, delegate& dlg)
{
  int min_cost = infinite_costs;
  access* min_start_addr = NULL;
  mod_tracker tracker;

  std::list<access*> start_addrs =
    start_addresses ().get_relevant_addresses (end_addr);
  for (std::list<access*>::iterator it = start_addrs.begin ();
       it != start_addrs.end (); ++it)
    {
      int cost = try_modify_addr (*it, end_addr, disp_min, disp_max,
                                  addr_type, insert_before, tracker, dlg).cost;
      tracker.reset_changes (*this);
      if (cost < min_cost)
        {
          min_cost = cost;
          min_start_addr = *it;
        }
    }

  // If the end addr only has a constant displacement, try loading it into
  // the reg directly.
  if (end_addr.has_no_base_reg () && end_addr.has_no_index_reg ()
      && end_addr.has_disp ())
    {
      rtx const_reg = gen_reg_rtx (Pmode);
      add_reg_mod (accesses ().begin (),
                   make_const_addr (end_addr.disp ()),
                   make_const_addr (end_addr.disp ()),
                   NULL, const_reg, 0);
      int cost = try_modify_addr (&(*accesses ().begin ()), end_addr,
                                  disp_min, disp_max,
                                  addr_type, insert_before, tracker, dlg).cost;
      cost += dlg.const_load_cost (const_reg, end_addr.disp (),
                                   *this, accesses ().begin ());

      tracker.reset_changes (*this);
      if (cost < min_cost)
        {
          min_cost = cost;
          min_start_addr = &(*accesses ().begin ());
        }
      // If this doesn't reduce the costs, remove the newly added
      // (reg <- const) copy.
      else
        remove_access (accesses ().begin ());
    }

  return min_mod_cost_result (min_cost, min_start_addr);
}

// Try to find address modifications that change the address in START_ADDR
// into END_ADDR, insert the generated reg_mod accesses into the sequence
// behind ACCESS_PLACE and record the sequence modifications in MOD_TRACKER.
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
try_modify_addr (access* start_addr, const addr_expr& end_addr,
                 disp_t disp_min, disp_t disp_max, addr_type_t addr_type,
                 access_sequence::iterator &access_place,
                 mod_tracker &mod_tracker,
                 delegate& dlg)
{
  access_sequence::iterator ins_place;
  rtx new_reg = start_addr->address_reg ();
  int cost = start_addr->is_used ()
             ? dlg.addr_reg_clone_cost (start_addr->address_reg (),
                                        *this, access_place)
             : 0;
  int prev_cost = 0;
  rtx final_addr_regno = start_addr->address_reg ();

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

      if (!start_addr->is_used ())
        {
          start_addr->set_used ();
          mod_tracker.use_changed_accs ().push_back (start_addr);
        }

      new_reg = gen_reg_rtx (Pmode);
      access* new_addr = &add_reg_mod (
                 access_place,
                 non_mod_addr (invalid_regno,
                               start_addr->address_reg (), scale, 0),
                 c_start_addr, NULL, new_reg, 0);
      final_addr_regno = new_reg;

      ins_place = access_place;
      --ins_place;
      mod_tracker.inserted_accs ().push_back (ins_place);

      cost += dlg.addr_reg_scale_cost (start_addr->address_reg (), scale,
                                       *this, ins_place);
      new_addr->update_cost (cost - prev_cost);
      prev_cost = cost;
      start_addr = new_addr;
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

      if (!start_addr->is_used ())
        {
          start_addr->set_used ();
          mod_tracker.use_changed_accs ().push_back (start_addr);
        }

      new_reg = gen_reg_rtx (Pmode);
      access* new_addr = &add_reg_mod (
                 access_place,
                 non_mod_addr (start_addr->address_reg (),
                               c_end_addr.index_reg (),
                               -1, 0),
                 c_start_addr, NULL, new_reg, 0);
      final_addr_regno = new_reg;

      ins_place = access_place;
      --ins_place;
      mod_tracker.inserted_accs ().push_back (ins_place);

      cost += dlg.addr_reg_plus_reg_cost (start_addr->address_reg (),
                                          c_end_addr.index_reg (),
                                          *this, ins_place);
      new_addr->update_cost (cost - prev_cost);
      prev_cost = cost;
      start_addr = new_addr;
    }

  // Add missing base reg.
  if (c_start_addr.has_no_base_reg () && c_end_addr.has_base_reg ())
    {
      c_start_addr = non_mod_addr (c_end_addr.base_reg (),
                                   c_start_addr.index_reg (),
                                   c_start_addr.scale (),
                                   c_start_addr.disp ());

      if (!start_addr->is_used ())
        {
          start_addr->set_used ();
          mod_tracker.use_changed_accs ().push_back (start_addr);
        }

      new_reg = gen_reg_rtx (Pmode);
      access* new_addr = &add_reg_mod (
                 access_place,
                 non_mod_addr (c_start_addr.base_reg (),
                               start_addr->address_reg (), 1, 0),
                 c_start_addr, NULL, new_reg, 0);
      final_addr_regno = new_reg;

      ins_place = access_place;
      --ins_place;
      mod_tracker.inserted_accs ().push_back (ins_place);

      cost += dlg.addr_reg_plus_reg_cost (start_addr->address_reg (),
                                          c_end_addr.base_reg (),
                                          *this, ins_place);
      new_addr->update_cost (cost - prev_cost);
      prev_cost = cost;
      start_addr = new_addr;
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
      if (std::abs (alt_disp) < std::abs (disp))
        disp = alt_disp;

      c_start_addr = non_mod_addr (c_end_addr.base_reg (),
                                   c_start_addr.index_reg (),
                                   c_start_addr.scale (),
                                   c_start_addr.disp () + disp);

      if (!start_addr->is_used ())
        {
          start_addr->set_used ();
          mod_tracker.use_changed_accs ().push_back (start_addr);
        }

      new_reg = gen_reg_rtx (Pmode);
      access* new_addr = &add_reg_mod (
                  access_place,
                  non_mod_addr (start_addr->address_reg (),
                                invalid_regno, 1, disp),
                  c_start_addr, NULL, new_reg, 0);
      final_addr_regno = new_reg;

      ins_place = access_place;
      --ins_place;
      mod_tracker.inserted_accs ().push_back (ins_place);

      cost += dlg.addr_reg_disp_cost (start_addr->address_reg (), disp,
                                      *this, ins_place);
      new_addr->update_cost (cost - prev_cost);
      prev_cost = cost;
      start_addr = new_addr;
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
      if (!start_addr->is_used ())
        {
          start_addr->set_used ();
          mod_tracker.use_changed_accs ().push_back (start_addr);
        }

      rtx pre_mod_reg = new_reg;
      new_reg = gen_reg_rtx (Pmode);
      access* new_addr = &add_reg_mod (access_place, make_reg_addr (pre_mod_reg),
                                       c_start_addr, NULL, new_reg, 0);
      final_addr_regno = new_reg;

      ins_place = access_place;
      --ins_place;
      mod_tracker.inserted_accs ().push_back (ins_place);

      new_addr->update_cost (cost - prev_cost);
      prev_cost = cost;
    }

  return mod_addr_result (cost, final_addr_regno, c_start_addr.disp ());
}

// Find all the address regs in the access sequence (i.e. the regs whose value
// was changed by a reg_mod access) and place them into M_ADDR_REGS. Pair them
// with the last reg_mod access that modified them, or NULL if they are dead
// at the end of the sequence.
void sh_ams::access_sequence::find_addr_regs (void)
{
  for (access_sequence::iterator accs = accesses ().begin ();
       accs != accesses ().end (); ++accs)
    {
      if (accs->is_trailing ())
        break;

      if (accs->access_type () == reg_mod)
        addr_regs ()[accs->address_reg ()] = &(*accs);

      // Search for REG_DEAD notes in the insns between this and the next access.
      access_sequence::iterator next = accs;
      ++next;
      if (accs->insn () && next != accesses ().end () && !next->is_trailing ())
        {
          for (rtx_insn *i = accs->insn (); ; i = NEXT_INSN (i))
            {
              if (!INSN_P (i) || !NONDEBUG_INSN_P (i))
                continue;

              for (rtx note = REG_NOTES (i); note; note = XEXP (note, 1))
                {
                  // Set the value of any address reg that's no longer
                  // alive to NULL.
                  if (REG_NOTE_KIND (note) == REG_DEAD
                      && addr_regs ().find (XEXP (note, 0)) != addr_regs ().end ())
                    addr_regs ()[XEXP (note, 0)] = NULL;
                }
              if (i == next->insn ())
                break;
            }
        }
    }
}

// Add to the sequence any address reg modifications in BB that weren't found
// during the mem address tracing (e.g. the address reg modifications
// that come after the last memory access in the sequence).
void sh_ams::access_sequence::add_missing_reg_mods (void)
{
  find_addr_regs ();

  std::vector<access*> inserted_reg_mods;
  for (std::map<rtx, access*>::iterator it = addr_regs ().begin ();
       it != addr_regs ().end (); ++it)
    {
      rtx reg = it->first;

      // Trace back the address reg's value, inserting any missing
      // modification of this reg to the sequence.
      inserted_reg_mods.clear ();
      addr_expr expr =
        extract_addr_expr (reg, BB_END (bb ()), BB_END (bb ()),
                           Pmode, this, inserted_reg_mods);

      // If the final expression created by these modifications
      // is too complicated for AMS to handle, the address mod
      // generator shouldn't try to replace them.
      if (expr.is_invalid ())
        {
           std::for_each (inserted_reg_mods.begin (), inserted_reg_mods.end (),
                   std::mem_fun (&access::mark_unremovable));
        }
    }
}

// Check whether REG is used in any access after SEARCH_START.
bool sh_ams::access_sequence::
reg_used_in_sequence (rtx reg, access_sequence::iterator search_start)
{
  for (access_sequence::iterator accs = search_start;
       accs != accesses ().end (); ++accs)
    {
      if (!accs->original_address ().is_invalid ()
          && (accs->original_address ().base_reg () == reg
              || accs->original_address ().index_reg () == reg))
        return true;
    }
  return false;
}

// Find all uses of the address registers that aren't mem loads/stores
// or address modifications, and add them to the sequence
// as reg_use accesses.
void sh_ams::access_sequence::find_reg_uses (void)
{
  std::vector<std::pair<rtx*, rtx_insn*> > used_regs;
  rtx_insn* last_insn = NULL;

  for (access_sequence::iterator accs = accesses ().begin ();
       accs != accesses ().end (); ++accs)
    {
      if (!accs->insn ())
        continue;
      last_insn = accs->insn ();

      if (accs->access_type () == reg_use)
        continue;

      access_sequence::iterator next_acc = accs;
      ++next_acc;
      used_regs.clear ();
      collect_addr_reg_uses (*this, accs->insn (),
                             next_acc == accesses ().end ()
                               ? NULL
                               : next_acc->insn (),
                             std::back_inserter (used_regs),
                             true, true, false);

      for (std::vector<std::pair<rtx*, rtx_insn*> >::iterator
             it = used_regs.begin (); it != used_regs.end (); ++it)
        {
          rtx* use_ref = it->first;
          rtx_insn* use_insn = it->second;
          addr_expr use_expr = extract_addr_expr (*use_ref);
          addr_expr effective_addr
            = extract_addr_expr (*use_ref, use_insn, NULL, Pmode, this);

          if (!effective_addr.is_invalid ())
            add_reg_use (next_acc, use_expr, effective_addr,
                         use_ref, use_insn);
        }
    }

  if (!last_insn)
    return;

  // Add trailing address reg uses to the end of the sequence.
  for (std::map<rtx, access*>::iterator it = addr_regs ().begin ();
       it != addr_regs ().end (); ++it)
    {
      used_regs.clear ();
      collect_addr_reg_uses (*this, it->first, last_insn, NULL,
                             std::back_inserter (used_regs),
                             false, false, true);

      std::vector<rtx_insn*> insns;
      rtx* trailing_use_ref = NULL;

      for (std::vector<std::pair<rtx*, rtx_insn*> >::iterator
             it = used_regs.begin (); it != used_regs.end (); ++it)
        {
          rtx* use_ref = it->first;
          rtx_insn* use_insn = it->second;
          if (!trailing_use_ref)
            trailing_use_ref = use_ref;
          else if (!rtx_equal_p (*use_ref, *trailing_use_ref))
            {
              // If the trailing uses aren't all the same,
              // don't add them for this reg.
              trailing_use_ref = NULL;
              break;
            }
          insns.push_back (use_insn);
        }

      if (trailing_use_ref)
        {
          addr_expr original_addr = extract_addr_expr (*trailing_use_ref);
          // FIXME: Compute the effective address of the reg_use.
          add_reg_use (accesses ().end (),
                       original_addr,
                       original_addr,
                       trailing_use_ref, insns);
        }
    }
}

// Find the values of all address registers that are still alive
// at the end of the access sequence, and set them to their values with
// reg_mod accesses. This will force the address modification generator
// to keep their original values at the end of the basic blocks.
void sh_ams::access_sequence::find_reg_end_values (void)
{
  // Update the address regs' final values.
  find_addr_regs ();

  for (std::map<rtx, access*>::iterator it = addr_regs ().begin ();
       it != addr_regs ().end (); ++it)
    {
      access* acc = it->second;

      // Address regs that have NULL as their value are dead,
      // so we can skip those.
      if (!acc)
        continue;

      // Don't add the addr reg if it wasn't modified during the sequence
      // (i.e. if its effective address is the address reg itself).
      if (acc->address ().is_invalid ()
          || (acc->address ().has_no_index_reg ()
              && acc->address ().has_no_disp ()
              && acc->address ().base_reg () == acc->address_reg ()))
        continue;

      add_reg_mod (accesses ().end (), make_invalid_addr (), acc->address (),
                   NULL, acc->address_reg (),
                   0, false, false);
    }
}

// Fill the m_inc/dec_chain_length field of the accesses in the sequence.
//
// FIXME: this is quadratic.
//
// for cases such as
//    (1) @(reg + 0)
//    (2) @(reg + 4)
//    (3) @(reg + 40)
//    (4) @(reg + 8)
//
// it will not see that (2) and (4) are adjacent, which is the hypothetical
// adjacency as opposed to the actual adjacency.  it might be interesting
// to also add a function that calculates the hypothetical adjacency.
// it should do something like this
//    (1) @(reg + 0)     hyp adj = 3 (chain 1,2,6)
//    (2) @(reg + 4)     hyp adj = 3 (chain 1,2,6)
//    (3) @(reg + 40)    hyp adj = 3 (chain 3,4,5)
//    (4) @(reg + 44)    hyp adj = 3 (chain 3,4,5)
//    (5) @(reg + 48)    hyp adj = 3 (chain 3,4,5)
//    (6) @(reg + 8)     hyp adj = 3 (chain 1,2,6)
//
void sh_ams::access_sequence::calculate_adjacency_info (void)
{
  for (sh_ams::access_sequence::iterator accs = first_mem_access ();
       accs != accesses ().end (); )
    {
      int dist = 0;
      sh_ams::access_sequence::iterator adj_end = accs;
      while (true)
        {
          sh_ams::access_sequence::iterator prev = adj_end;
          adj_end = next_mem_access (adj_end);
          dist++;
          if (adj_end == accesses ().end ()
              || !access::adjacent_inc (*prev, *adj_end))
            break;
        }

      for (; accs != adj_end; accs = next_mem_access (accs))
        accs->set_inc_chain_length (dist);
    }

  for (sh_ams::access_sequence::iterator accs = first_mem_access ();
       accs != accesses ().end (); )
    {
      int dist = 0;
      sh_ams::access_sequence::iterator adj_end = accs;
      while (true)
        {
          sh_ams::access_sequence::iterator prev = adj_end;
          adj_end = next_mem_access (adj_end);
          dist++;
          if (adj_end == accesses ().end ()
              || !access::adjacent_dec (*prev, *adj_end))
            break;
        }

      for (; accs != adj_end; accs = next_mem_access (accs))
        accs->set_dec_chain_length (dist);
    }
}

unsigned int sh_ams::execute (function* fun)
{
  log_msg ("sh-ams pass\n");

//  df_set_flags (DF_DEFER_INSN_RESCAN); // needed?

  df_note_add_problem ();
  df_analyze ();

  std::list<access_sequence> sequences;
  std::list<access_sequence::mod_insn_list > sequence_mod_insns;
  std::vector<std::pair<rtx*, access_type_t> > mems;

  log_msg ("extracting access sequences\n");
  basic_block bb;
  FOR_EACH_BB_FN (bb, fun)
    {
      rtx_insn* i;

      log_msg ("BB #%d:\n", bb->index);
      log_msg ("finding mem accesses\n");

      // Construct the access sequence from the access insns.
      sequence_mod_insns.push_back (access_sequence::mod_insn_list ());
      std::list<access_sequence::mod_insn_list>::iterator mod_insns
        = sequence_mod_insns.end ();
      --mod_insns;

      sequences.push_back (access_sequence (mod_insns));
      mod_insns->use ();
      access_sequence& as = sequences.back ();

      FOR_BB_INSNS (bb, i)
        {
          if (!INSN_P (i) || !NONDEBUG_INSN_P (i))
            continue;

          // Search for memory accesses inside the current insn
          // and add them to the address sequence.
          mems.clear ();
          find_mem_accesses (PATTERN (i), std::back_inserter (mems));

          for (std::vector<std::pair<rtx*, access_type_t> >
	       ::iterator m = mems.begin (); m != mems.end (); ++m)
	    as.add_mem_access (i, m->first, m->second);
         }
    }

  log_msg ("\nprocessing extracted sequences\n");
  for (std::list<access_sequence>::iterator as_it = sequences.begin ();
       as_it != sequences.end ();)
    {
      access_sequence& as = *as_it;
      if (as.accesses ().empty ())
        {
          log_msg ("access sequence empty\n\n");
          ++as_it;
          continue;
        }

      log_access_sequence (as, false);
      log_msg ("\n\n");

      log_msg ("add_missing_reg_mods\n");
      as.add_missing_reg_mods ();

      log_access_sequence (as, false);
      log_msg ("\n\n");

      log_msg ("find_reg_uses\n");
      as.find_reg_uses ();

      log_access_sequence (as, false);
      log_msg ("\n\n");

      log_msg ("find_reg_end_values\n");
      as.find_reg_end_values ();

      log_access_sequence (as, false);
      log_msg ("\n\n");

      // Fill the sequence's MOD_INSNS with the insns of the accesses
      // that can be removed.
      for (access_sequence::iterator it = as.accesses ().begin ();
           it != as.accesses ().end (); ++it)
        {
          if (it->removable ()
              // Auto-mod mem access insns shouldn't be removed.
              && !find_reg_note (it->insn (), REG_INC, NULL_RTX))
            as.mod_insns ()->insns ().push_back (it->insn ());
        }

      log_msg ("split_access_sequence\n");
      as_it = split_access_sequence (as_it, sequences);
    }

  log_msg ("\nprocessing split sequences\n");
  for (std::list<access_sequence>::iterator as_it = sequences.begin ();
       as_it != sequences.end (); ++as_it)
    {
      access_sequence& as = *as_it;
      if (as.accesses ().empty ())
        {
          log_msg ("access sequence empty\n\n");
          continue;
        }

      log_access_sequence (as, false);
      log_msg ("\n\n");

      log_msg ("updating access alternatives\n");
      for (access_sequence::iterator it = as.first_access_to_optimize ();
           it != as.accesses ().end (); it = as.next_access_to_optimize (it))
        as.update_access_alternatives (m_delegate, it);

      log_msg ("doing adjacency analysis\n");
      as.calculate_adjacency_info ();

      log_msg ("updating costs\n");

      for (access_sequence::iterator mem_acc = as.first_mem_access ();
           mem_acc != as.accesses ().end ();
           mem_acc = as.next_mem_access (mem_acc))
        for (access::alternative* alt = mem_acc->begin_alternatives ();
             alt != mem_acc->end_alternatives (); ++alt)
          m_delegate.adjust_alternative_costs (*alt, as, mem_acc);

      as.update_cost (m_delegate);
      int original_cost = as.cost ();

      log_access_sequence (as);
      log_msg ("\n\n");

      if (as.cost_already_minimal ())
        {
          log_msg ("costs are already minimal\n");
          continue;
        }

      log_msg ("gen_address_mod\n");
      as.gen_address_mod (m_delegate);

      as.update_cost (m_delegate);
      int new_cost = as.cost ();

      log_access_sequence (as, false);
      log_msg ("\n");

      if (new_cost < original_cost)
        as.update_insn_stream (sequence_mod_insns);
      else
        log_msg ("new_cost (%d) >= original_cost (%d)  not modifying\n",
		 new_cost, original_cost);

      log_msg ("\n\n");
    }

  log_return (0, "\n\n");
}
