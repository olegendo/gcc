#include "config.h"

#include <iterator>
#include <sstream>
#include <memory>

#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "predict.h"
#include "vec.h"
#include "hashtab.h"
#include "hash-set.h"
#include "hard-reg-set.h"
#include "input.h"
#include "dominance.h"
#include "cfgrtl.h"
#include "cfganal.h"
#include "lcm.h"
#include "cfgbuild.h"
#include "cfgcleanup.h"
#include "df.h"
#include "rtl.h"
#include "insn-config.h"
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
#include "diagnostic-core.h"
#include "opts.h"
#include "regs.h"

// For global variable flag_rerun_cse_after_global_opts.
#include "toplev.h"

#include <algorithm>
#include <list>
#include <vector>
#include <set>
#include <cstdlib>

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

template <typename T> struct parse_result
{
  bool valid;
  T value;

  parse_result (void) : valid (false) { }
  parse_result (const T& v) : valid (true), value (v) { }
  parse_result (const T& v, bool vv) : valid (vv), value (v) { }

  template <typename S> void
  copy_if_valid_to (S& out) const
  {
    if (valid)
      out = value;
  }
};

parse_result<int>
parse_int (const char* s)
{
  while (*s && ISSPACE (*s)) ++s;

  if (s[0] == '\0')
    return parse_result<int> ();

  bool neg = false;

  if (*s == '-')
    {
      neg = true;
      ++s;
    }
  else if (*s == '+')
    ++s;

  int val = integral_argument (s);
  return parse_result<int> (neg ? -val : val, val >= 0);
}

parse_result<int>
parse_int (const std::string& s)
{
  return parse_int (s.c_str ());
}

void
log_options (const sh_ams::options& opt)
{
  if (dump_file == NULL)
    return;

  log_msg ("option check_minimal_cost = %d\n", opt.check_minimal_cost);
  log_msg ("option check_original_cost = %d\n", opt.check_original_cost);
  log_msg ("option split_sequences = %d\n", opt.split_sequences);
  log_msg ("base_lookahead_count = %d", opt.base_lookahead_count);
}

void
log_reg (rtx x)
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
      log_msg ("@( += %"PRId64, ae.disp ());
      log_reg (ae.base_reg ());
      log_msg (" )");
      return;
    }

  if (ae.type () == sh_ams::post_mod)
    {
      log_msg ("@( ");
      log_reg (ae.base_reg ());
      log_msg (" += %"PRId64 " )", ae.disp ());
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
	log_msg (" + %"PRId64, ae.disp ());
      else if (ae.disp_min () != ae.disp_max ()
	       && (ae.disp_min () != 0 || ae.disp_max () != 0))
	log_msg (" + (%"PRId64 " ... %"PRId64 ")", ae.disp_min (), ae.disp_max ());

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

  if (a.emit_before_insn ())
    log_msg ("\n  emit before insn %d [bb %d]", INSN_UID (a.emit_before_insn ()),
             BLOCK_FOR_INSN (a.emit_before_insn ())->index);
  if (a.emit_after_insn ())
    log_msg ("\n  emit after insn %d [bb %d]", INSN_UID (a.emit_after_insn ()),
             BLOCK_FOR_INSN (a.emit_after_insn ())->index);

  if (!a.should_optimize ())
    log_msg ("\n  (won't be optimized)");
  if (a.is_trailing ())
    log_msg ("\n  (trailing)");
  if (a.inc_chain ().length () > 1)
    log_msg ("\n  (inc chain pos: %d  length: %d)", a.inc_chain ().pos (),
						    a.inc_chain ().length ());
  if (a.dec_chain ().length () > 1)
    log_msg ("\n  (dec chain pos: %d  length: %d)", a.dec_chain ().pos (),
						    a.dec_chain ().length ());

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
      log_msg ("\n  %d alternatives:\n", a.alternatives ().size ());
      int alt_count = 0;
      for (sh_ams::access::alternative_set::const_iterator
		alt = a.alternatives ().begin ();
           alt != a.alternatives ().end (); ++alt)
        {
          if (alt_count > 0)
            log_msg ("\n");

          log_msg ("    alt %d, cost %d, valid %d: ",
		   alt_count, alt->cost (), alt->valid ());
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

  log_msg ("=====\naccess sequence %p: %s\n\n", (const void*)&as,
	   as.accesses ().empty () ? "is empty" : "");

  if (as.accesses ().empty ())
    return;

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

// Find all registers that are used in the address calculation of X
// and insert them into OUT.
template <typename OutputIterator> void
find_regs_used_in_rtx (rtx x, OutputIterator out)
{
  if (REG_P (x))
    *out++ = x;
  else if (UNARY_P (x) || ARITHMETIC_P (x))
    {
      for (int i = 0; i < GET_RTX_LENGTH (GET_CODE (x)); i++)
        find_regs_used_in_rtx (XEXP (x, i), out);
    }
}

// check if register a and b match, where both could be any_regno or
// invalid_regno.
//          a         |      b        |  match
//     invalid_regno  | invalid_regno |  false
//     invalid_regno  |   any_regno   |  false
//     invalid_regno  |      reg      |  false
//       any_regno    | invalid_regno |  false
//       any_regno    |   any_regno   |  true
//       any_regno    |      reg      |  true
//          reg       | invalid_regno |  false
//          reg       |   any_regno   |  true
//          reg       |      reg      |  REGNO (reg) == REGNO (reg)
bool
registers_match (rtx a, rtx b)
{
  if (a == sh_ams::invalid_regno || b == sh_ams::invalid_regno)
    return false;

  if (a == sh_ams::any_regno || b == sh_ams::any_regno)
    return true;

  return REGNO (a) == REGNO (b);
}

bool
remove_incdec_notes (rtx_insn* i)
{
  bool found = false;
  for (bool retry = true; retry; )
    {
      retry = false;
      for (rtx note = REG_NOTES (i); note; note = XEXP (note, 1))
	if (REG_NOTE_KIND (note) == REG_INC)
	  {
	    remove_note (i, note);
            found = true;
	    retry = true;
	    break;
	  }
    }
  return found;
}

void
remove_incdec_note (rtx_insn* i, rtx reg)
{
  if (rtx n = find_regno_note (i, REG_INC, REGNO (reg)))
    remove_note (i, n);
}

} // anonymous namespace

// borrowed from C++11
// could also put this into namespace std.  but std libs like libc++ (clang)
// provide std::next/prev also if used in C++98 mode.  so we'd need something
// like
//    #if __cplusplus < 201103L && !defined (_LIBCPP_ITERATOR)
// but that's a bit fragile, so let's not do it.

namespace stdx
{

template<class ForwardIt> ForwardIt
next (ForwardIt it,
      typename std::iterator_traits<ForwardIt>::difference_type n = 1)
{
  std::advance (it, n);
  return it;
}

template<class BidirIt> BidirIt
prev (BidirIt it,
      typename std::iterator_traits<BidirIt>::difference_type n = 1)
{
  std::advance (it, -n);
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

sh_ams::sh_ams (gcc::context* ctx, const char* name, delegate& dlg,
		const options& opt)
: rtl_opt_pass (default_pass_data, ctx),
  m_delegate (dlg),
  m_options (opt)
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

void sh_ams::set_options (const options& opt)
{
  m_options = opt;
}

sh_ams::options::options (void)
{
  // maybe we can use different sets of options based on the global
  // optimization level.
  check_minimal_cost = true;
  check_original_cost = true;
  split_sequences = true;
  force_alt_validation = false;
  disable_alt_validation = false;
  cse = false;
  cse2 = false;
  gcse = false;
  allow_mem_addr_change_new_insns = true;
  base_lookahead_count = 1;
}

sh_ams::options::options (const char* str)
{
  *this = options (std::string (str == NULL ? "" : str));
}

sh_ams::options::options (const std::string& str)
{
  *this = options ();

  std::vector<std::string> tokens;
  for (std::stringstream ss (str); ss.good (); )
    {
      tokens.push_back (std::string ());
      std::getline (ss, tokens.back (), ',');
    }

  std::map<std::string, std::string> kv;

  for (std::vector<std::string>::const_iterator i = tokens.begin ();
       i != tokens.end (); ++i)
    {
      std::string::size_type eq_pos = i->find ('=');
      kv[i->substr (0, eq_pos)] = eq_pos == std::string::npos
				  ? std::string ()
				  : i->substr (eq_pos + 1);
    }

  typedef std::map<std::string, std::string>::iterator kvi;

#define get_int_opt(name) \
  for (kvi i = kv.find (#name); i != kv.end (); i = kv.end ()) \
    parse_int (i->second).copy_if_valid_to (name)

  get_int_opt (check_minimal_cost);
  get_int_opt (check_original_cost);
  get_int_opt (split_sequences);
  get_int_opt (base_lookahead_count);
  get_int_opt (force_alt_validation);
  get_int_opt (disable_alt_validation);
  get_int_opt (cse);
  get_int_opt (cse2);
  get_int_opt (gcse);
  get_int_opt (allow_mem_addr_change_new_insns);

#undef get_int_opt

//  error ("unknown AMS option");
}

rtx
sh_ams::addr_expr::to_rtx (void) const
{
  if (m_cached_to_rtx != NULL)
    return m_cached_to_rtx;

  rtx r = has_base_reg () ? base_reg () : NULL;

  // Add (possibly scaled) index reg.
  if (has_index_reg ())
    {
      rtx i = index_reg ();
      int s = scale ();

      if (s != 1)
	{
	  int shiftval = exact_log2 (s);
	  i = shiftval != -1 ? gen_rtx_ASHIFT (Pmode, i, GEN_INT (shiftval))
			     : gen_rtx_MULT (Pmode, i, GEN_INT (s));
	}

      r = r ? gen_rtx_PLUS (Pmode, r, i) : i;
   }

  // Surround with POST/PRE_INC/DEC if it is an auto_mod type.
  // FIXME: Also handle PRE_MODIFY and POST_MODIFY.  For that we might need
  // to have the mod being an addr_expr instead of the constant displacement.
  // Moreover, we can't really distinguish a post/pre mod with a
  // displacement != access size from a post/pre inc/dec.
  if (type () == pre_mod)
    r = disp () > 0 ? gen_rtx_PRE_INC (Pmode, r) : gen_rtx_PRE_DEC (Pmode, r);

  else if (type () == post_mod)
    r = disp () > 0 ? gen_rtx_POST_INC (Pmode, r) : gen_rtx_POST_DEC (Pmode, r);

  else if (has_disp ())
    r = r ? gen_rtx_PLUS (Pmode, r, GEN_INT (disp ())) : GEN_INT (disp ());

  return m_cached_to_rtx = r;
}

void
sh_ams::addr_expr::set_base_reg (rtx val)
{
  if (val == m_base_reg)
    return;

  m_base_reg = val;
  m_cached_to_rtx = NULL;
}

void
sh_ams::addr_expr::set_index_reg (rtx val)
{
  if (val == m_index_reg)
    return;

  m_index_reg = val;
  m_cached_to_rtx = NULL;
}

void
sh_ams::addr_expr::set_disp (disp_t val)
{
  if (val == m_disp)
    return;

  m_disp = m_disp_min = m_disp_max = val;
  m_cached_to_rtx = NULL;
}

void
sh_ams::addr_expr::set_scale (scale_t val)
{
  if (val == m_scale)
    return;

  m_scale = m_scale_min = m_scale_max = val;
  m_cached_to_rtx = NULL;
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
  m_emit_before_insn = NULL;
  m_emit_after_insn = NULL;
  m_mem_ref = mem;
  m_original_addr_expr = original_addr_expr;
  m_addr_expr = addr_expr;
  m_addr_rtx = NULL;
  m_valid_addr_expr = make_invalid_addr ();
  m_should_optimize = should_optimize;
  m_addr_reg = NULL;
  m_used = false;
  m_visited = false;
  m_valid_at_end = false;
  m_validate_alternatives = true;
}

// Constructor for reg_mod accesses.
sh_ams::access::access (rtx_insn* insn, addr_expr original_addr_expr,
                        addr_expr addr_expr, rtx addr_rtx, rtx mod_reg,
                        int cost)
{
  m_access_type = reg_mod;
  m_cost = cost;
  m_insn = insn;
  m_emit_before_insn = NULL;
  m_emit_after_insn = NULL;
  m_mem_ref = NULL;
  m_original_addr_expr = original_addr_expr;
  m_addr_expr = addr_expr;
  m_addr_rtx = addr_rtx;
  m_valid_addr_expr = make_invalid_addr ();
  m_should_optimize = true;
  m_addr_reg = mod_reg;
  m_used = false;
  m_visited = false;
  m_valid_at_end = false;
  m_validate_alternatives = true;
}

// Constructor for reg_use accesses.
sh_ams::access::access (rtx_insn* insn, std::vector<rtx_insn*> trailing_insns,
                        rtx* reg_ref,
                        addr_expr original_addr_expr, addr_expr addr_expr,
                        int cost)
{
  m_access_type = reg_use;
  m_cost = cost;
  m_insn = insn;
  m_emit_before_insn = NULL;
  m_emit_after_insn = NULL;
  m_trailing_insns = trailing_insns;
  m_mem_ref = reg_ref;
  m_original_addr_expr = original_addr_expr;
  m_addr_expr = addr_expr;
  m_addr_rtx = NULL;
  m_valid_addr_expr = make_invalid_addr ();
  m_should_optimize = true;
  m_addr_reg = NULL;
  m_used = false;
  m_visited = false;
  m_valid_at_end = false;
  m_validate_alternatives = true;
}

bool
sh_ams::access::matches_alternative (const alternative& alt) const
{
  const addr_expr& ae = original_address ();
  const addr_expr& alt_ae = alt.address ();

  if (ae.type () != alt_ae.type ())
    return false;

  if (ae.has_base_reg () != alt_ae.has_base_reg ())
    return false;
  if (ae.has_index_reg () != alt_ae.has_index_reg ())
    return false;

  if (ae.has_base_reg () && alt_ae.has_base_reg ()
      && !registers_match (ae.base_reg (), alt_ae.base_reg ()))
    return false;

  if (ae.disp () < alt_ae.disp_min () || ae.disp () > alt_ae.disp_max ())
    return false;

  if (ae.has_index_reg ()
      && (ae.scale () < alt_ae.scale_min ()
          || ae.scale () > alt_ae.scale_max ()
          || !registers_match (ae.index_reg (), alt_ae.index_reg ())))
    return false;

  return true;
}

// Add a normal access to the end of the access sequence.
sh_ams::access&
sh_ams::access_sequence::add_mem_access (rtx_insn* insn, rtx* mem,
					 access_type_t access_type)
{
  machine_mode m_mode = GET_MODE (*mem);

  addr_expr original_expr = extract_addr_expr ((XEXP (*mem, 0)), m_mode);

  std::vector<access*> inserted_reg_mods;
  addr_expr expr = extract_addr_expr ((XEXP (*mem, 0)),
                                      prev_nonnote_insn_bb (insn), insn,
				      m_mode, this, inserted_reg_mods);
  bool should_optimize = true;

  // If the effective address doesn't fit into an addr_expr,
  // don't try to optimize it.
  if (expr.is_invalid ())
    {
      expr = original_expr;
      should_optimize = false;
    }

  accesses ().push_back (access (insn, mem, access_type,
                                 original_expr, expr, should_optimize));
  return accesses ().back ();
}

// Return a valid address even when the real effective address
// is unknown/complicated.
const sh_ams::addr_expr&
sh_ams::access::valid_address (void)
{
  if (m_addr_expr.is_invalid () && m_addr_reg)
    {
      if (m_valid_addr_expr.is_invalid ())
        m_valid_addr_expr = make_reg_addr (m_addr_reg);
      return m_valid_addr_expr;
    }
  return m_addr_expr;
}

void
sh_ams::access::set_original_address (int new_cost,
				      const addr_expr& new_addr_expr)
{
  m_cost = new_cost;
  m_original_addr_expr = new_addr_expr;
  m_addr_rtx = NULL;
}

void
sh_ams::access::set_original_address (int new_cost, rtx new_addr_rtx)
{
  m_cost = new_cost;
  m_original_addr_expr = make_invalid_addr ();
  m_addr_rtx = new_addr_rtx;
}

void
sh_ams::access::set_effective_address (const addr_expr& new_addr_expr)
{
  m_addr_expr = new_addr_expr;
  m_addr_rtx = NULL;
}

bool
sh_ams::access::set_insn_mem_rtx (rtx new_addr, bool allow_new_insns)
{
  // In some cases we might actually end up with 'new_addr' being not
  // really a valid address.  validate_change will then use the
  // target's 'legitimize_address' function to make a valid address out of
  // it.  While doing so the target might emit new insns which we must
  // capture and re-emit before the actual insn.
  // If this happens it means that something with the alternatives or
  // mem insn matching is not working as intended.

  start_sequence ();
  bool r = validate_change (m_insn, m_mem_ref,
			    replace_equiv_address (*m_mem_ref, new_addr),
			    false);

  rtx_insn* new_insns = get_insns ();
  end_sequence ();

  if (r && !allow_new_insns && new_insns != NULL)
    {
      log_msg ("validate_change produced new insns: \n");
      log_rtx (new_insns);
      abort ();
    }

  if (r && new_insns != NULL)
    emit_insn_before (new_insns, m_insn);

  return r;
}

bool
sh_ams::access::try_set_insn_mem_rtx (rtx new_addr)
{
  rtx prev_rtx = XEXP (*m_mem_ref, 0);

  XEXP (*m_mem_ref, 0) = new_addr;

  int new_insn_code = recog (PATTERN (m_insn), m_insn, NULL);
/*
  log_msg ("\nrecog\n");
  log_rtx (PATTERN (m_insn));
  log_msg (" = %d\n", new_insn_code);
*/
  XEXP (*m_mem_ref, 0) = prev_rtx;
  return new_insn_code >= 0;
}

bool
sh_ams::access::set_insn_use_rtx (rtx new_expr)
{
  return validate_change (m_insn, m_mem_ref, new_expr, false);
}

void
sh_ams::access::set_insn (rtx_insn* new_insn)
{
  // FIXME: maybe add some consistency checks here?
  m_insn = new_insn;
}

struct sh_ams::access::alternative_valid
{
  bool operator () (const alternative& a) const { return a.valid (); }
};

struct sh_ams::access::alternative_invalid
{
  bool operator () (const alternative& a) const { return !a.valid (); }
};

// Create a reg_mod access and add it to the access sequence.
// This function traverses the insn list backwards starting from INSN to
// find the correct place inside AS where the access needs to be inserted.
sh_ams::access&
sh_ams::access_sequence::add_reg_mod (rtx_insn* insn,
				      const addr_expr& original_addr_expr,
				      const addr_expr& addr_expr, rtx addr_rtx,
				      rtx_insn* mod_insn, rtx reg, int cost)
{
  if (accesses ().empty ())
    {
      accesses ().push_back (access (mod_insn, original_addr_expr, addr_expr,
                                     addr_rtx, reg, cost));
      start_addresses ().add (stdx::prev (accesses ().end ()));
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
              && regs_equal (as_it->address_reg (), reg))
            return *as_it;
        }

      accesses ().push_front (access (mod_insn, original_addr_expr, addr_expr,
                                      addr_rtx, reg, cost));
      start_addresses ().add (accesses ().begin ());
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
              && as_it->insn () == mod_insn
              && regs_equal (as_it->address_reg (), reg))
            {
              if (as_it->original_address ().is_invalid ())
                {
                  if (as_it->addr_rtx () == addr_rtx)
                    return *as_it;
                }
              else if (as_it->original_address ().base_reg ()
                        == original_addr_expr.base_reg ())
                return *as_it;
            }

        }
      if (as_it == accesses ().rend () || INSN_UID (i) == INSN_UID (mod_insn))
        {
          // We found mod_insn inside the insn list, so we know where to
          // insert the access.
          accesses ().insert (as_it.base (),
                              access (mod_insn, original_addr_expr, addr_expr,
                                      addr_rtx, reg, cost));
          start_addresses ().add (stdx::next (as_it).base ());
          return *as_it;
        }
    }
  gcc_unreachable ();
}

sh_ams::access&
sh_ams::access_sequence::add_reg_mod (rtx_insn* insn,
                                      const addr_expr& original_addr_expr,
                                      const addr_expr& addr_expr,
                                      rtx_insn* mod_insn, rtx reg, int cost)
{
  return add_reg_mod (insn, original_addr_expr, addr_expr, NULL, mod_insn,
                      reg, cost);
}

sh_ams::access&
sh_ams::access_sequence::add_reg_mod (rtx_insn* insn, rtx addr_rtx,
                                      rtx_insn* mod_insn, rtx reg, int cost)
{
  return add_reg_mod (insn, make_invalid_addr (), make_invalid_addr (),
                      addr_rtx, mod_insn, reg, cost);
}
// Create a reg_mod access and place it before INSERT_BEFORE
// in the access sequence.
sh_ams::access&
sh_ams::access_sequence::add_reg_mod (access_sequence::iterator insert_before,
                                      const addr_expr& original_addr_expr,
                                      const addr_expr& addr_expr,
                                      rtx_insn* mod_insn, rtx reg, int cost,
                                      bool use_as_start_addr)
{
  accesses ().insert (insert_before,
                      access (mod_insn, original_addr_expr, addr_expr,
                              NULL_RTX, reg, cost));
  access_sequence::iterator inserted = (--insert_before);
  if (use_as_start_addr)
    start_addresses ().add (inserted);
  return *inserted;
}

// Create a reg_use access and place it before INSERT_BEFORE
// in the access sequence.
sh_ams::access&
sh_ams::access_sequence::add_reg_use (access_sequence::iterator insert_before,
                                      const addr_expr& original_addr_expr,
                                      const addr_expr& addr_expr,
                                      rtx* reg_ref, rtx_insn* use_insn, int cost)
{
  access_sequence::iterator inserted =
    accesses ().insert (insert_before,
                        access (use_insn, std::vector<rtx_insn*> (), reg_ref,
                                original_addr_expr, addr_expr, cost));
  if (!inserted->try_set_insn_mem_rtx (gen_reg_rtx (Pmode)))
    {
      log_msg ("failed to substitute reg_use rtx, not optimizing");
      inserted->set_should_optimize (false);
    }
  return *inserted;
}

// Create a trailing reg_use access and place it before INSERT_BEFORE
// in the access sequence.
sh_ams::access&
sh_ams::access_sequence::add_reg_use (access_sequence::iterator insert_before,
                                      const addr_expr& original_addr_expr,
                                      const addr_expr& addr_expr,
                                      rtx* reg_ref,
                                      std::vector<rtx_insn*> use_insns, int cost)
{
  access_sequence::iterator inserted =
    accesses ().insert (insert_before,
                        access (NULL, use_insns, reg_ref,
                                original_addr_expr, addr_expr, cost));
  return *inserted;
}

// Remove the access ACC from the sequence. Return an iterator
// pointing to the next access.
sh_ams::access_sequence::iterator
sh_ams::access_sequence::remove_access (access_sequence::iterator acc)
{
  // Remove the access from the start_addresses and
  // addr_regs list first.

  if (acc->access_type () == reg_mod)
    {
      start_addresses ().remove (acc);

      std::pair <addr_reg_map::iterator, addr_reg_map::iterator> reg_mods =
        addr_regs ().equal_range (acc->address_reg ());
      for (addr_reg_map::iterator it = reg_mods.first; it!= reg_mods.second; ++it)
        {
          if (it->second == acc)
            {
              addr_regs ().erase (it);
              break;
            }
        }
    }

  return accesses ().erase (acc);
}

struct sh_ams::access_to_optimize
{
  bool operator () (const access& a) const
  {
    return (a.access_type () == load || a.access_type () == store
	    || a.access_type () == reg_use
	    || (a.access_type () == reg_mod
		&& a.original_address ().is_invalid ()
		&& !a.address ().is_invalid ()))
	   && a.should_optimize ()
           && !a.is_trailing ();
  }
};

// The basic block of the first insn in the access sequence.
basic_block
sh_ams::access_sequence::start_bb (void) const
{
  for (const_iterator a = accesses ().begin (); a != accesses ().end (); ++a)
    {
      if (a->insn () && BLOCK_FOR_INSN (a->insn ()))
        return BLOCK_FOR_INSN (a->insn ());
    }
  gcc_unreachable ();
}

// The first insn in the access sequence.
rtx_insn*
sh_ams::access_sequence::start_insn (void) const
{
  for (const_iterator a = accesses ().begin (); a != accesses ().end (); ++a)
    {
      if (a->insn ())
        return a->insn ();
    }
  gcc_unreachable ();
}

// The recursive part of find_reg_value. If REG is modified in INSN,
// return true and the SET pattern that modifies it. Otherwise, return
// false.
//
// FIXME: see if we can re-use find_set_of_reg_bb from sh_treg_combine.cc
// This is very similar to rtlanal.c (reg_set_p), except that we return
// the known set rtx to avoid looking for it again.
std::pair<rtx, bool> sh_ams::find_reg_value_1 (rtx reg, rtx pat)
{
  switch (GET_CODE (pat))
    {
    case SET:
      {
        rtx dest = SET_DEST (pat);
        if (REG_P (dest) && regs_equal (dest, reg))
          {
            // We're in the last insn that modified REG, so return
            // the modifying SET rtx.
            return std::make_pair (pat, true);
          }
      }
      break;

    case CLOBBER:
      {
        rtx dest = XEXP (pat, 0);
        if (REG_P (dest) && regs_equal (dest, reg))
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

// Find the value that REG was last set to, starting the search from INSN.
// Return that value along with the modifying insn and the register in the
// modifying pattern's SET_SRC (which is always the same register as REG,
// but might have a different machine mode).  If the reg's previous value
// can't be determined, return the insn where the search ended.
// If the register was modified because of an auto-inc/dec memory
// access, also return the mode of that access.
// FIXME: make use of other info such as REG_EQUAL notes.
sh_ams::find_reg_value_result sh_ams::find_reg_value (rtx reg, rtx_insn* insn)
{
  std::vector<std::pair<rtx*, access_type_t> > mems;

  // Go back through the insn list until we find the last instruction
  // that modified the register.
  rtx_insn* i;
  for (i = insn; i != NULL_RTX; i = prev_nonnote_insn_bb (i))
    {
      if (BARRIER_P (i))
	return find_reg_value_result (reg, NULL, i);
      if (!INSN_P (i) || DEBUG_INSN_P (i))
	continue;

      if (reg_set_p (reg, i) && CALL_P (i))
	return find_reg_value_result (reg, NULL, i);

      std::pair<rtx, bool> r = find_reg_value_1 (reg, PATTERN (i));
      if (r.second)
        {
          rtx modified_reg = r.first ? SET_DEST (r.first) : reg;
          rtx value = r.first ? SET_SRC (r.first) : NULL;
          return find_reg_value_result (modified_reg, value, i);
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
                  && regs_equal (XEXP (mem_addr, 0), reg))
                return find_reg_value_result (reg, mem_addr, i,
                                              GET_MODE (*(m->first)));
            }
        }
    }
  return find_reg_value_result (reg, reg, i);
}

// Return a non_mod_addr if it can be created with the given scale and
// displacement.  Otherwise, return an invalid address.
sh_ams::addr_expr
sh_ams::check_make_non_mod_addr (rtx base_reg, rtx index_reg,
                                 HOST_WIDE_INT scale, HOST_WIDE_INT disp)
{
  if (((base_reg || index_reg)
       && sext_hwi (disp, GET_MODE_PRECISION (Pmode)) != disp)
      || sext_hwi (scale, GET_MODE_PRECISION (Pmode)) != scale)
    return make_invalid_addr ();

  return non_mod_addr (base_reg, index_reg, scale, disp);
}

// Try to create an ADDR_EXPR struct of the form
// base_reg + index_reg * scale + disp from the access rtx X.
// If AS is not NULL, trace the original value of the registers in X
// as far back as possible, and add all the address reg modifying insns
// to AS as reg_mod accesses.  In this case, SEARCH_START_I is the insn
// from which the value-tracing starts and LAST_ACCESS_I should be the
// insn where the sequence's last access occurs.
sh_ams::addr_expr
sh_ams::extract_addr_expr (rtx x, rtx_insn* search_start_i,
                           rtx_insn *last_access_i,
			   machine_mode mem_mach_mode,
			   access_sequence* as,
                           std::vector<access*>& inserted_reg_mods)
{
  const bool expand_regs = as != NULL;

  addr_expr op0 = make_invalid_addr ();
  addr_expr op1 = make_invalid_addr ();
  HOST_WIDE_INT disp;
  HOST_WIDE_INT scale;
  rtx base_reg, index_reg;

  if (x == NULL_RTX)
    return make_invalid_addr ();

  enum rtx_code code = GET_CODE (x);

  // If X is an arithmetic operation, first create ADDR_EXPR structs
  // from its operands. These will later be combined into a single ADDR_EXPR.
  if (code == PLUS || code == MINUS || code == MULT || code == ASHIFT)
    {
      op0 = extract_addr_expr (XEXP (x, 0), search_start_i, last_access_i,
                               mem_mach_mode, as, inserted_reg_mods);
      op1 = extract_addr_expr (XEXP (x, 1), search_start_i, last_access_i,
                               mem_mach_mode, as, inserted_reg_mods);
      if (op0.is_invalid () || op1.is_invalid ())
        return make_invalid_addr ();
    }
  else if (code == NEG)
    {
      op1 = extract_addr_expr (XEXP (x, 0), search_start_i, last_access_i,
                               mem_mach_mode, as, inserted_reg_mods);
      if (op1.is_invalid ())
        return op1;
    }

  // Auto-mod accesses' effective address is found by offseting their constant
  // displacement, or by using the modified expression directly in the case
  // of PRE/POST_MODIFY.
  else if (GET_RTX_CLASS (code) == RTX_AUTOINC)
    {
      addr_type_t mod_type;

      // If we're expanding the effective address of a reg inside a post-mod
      // access, the post-mod displacement should not be applied if we're
      // looking for the address at the time the memory access happens.
      const bool use_post_disp =
        !expand_regs || !last_access_i
        || search_start_i != prev_nonnote_insn_bb (last_access_i);

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
          {
	    addr_expr a = extract_addr_expr (XEXP (x, use_post_disp ? 1 : 0),
					     search_start_i, last_access_i,
                                             mem_mach_mode,
					     as, inserted_reg_mods);
            if (a.is_invalid ())
              return make_invalid_addr ();
	    return expand_regs ? a : post_mod_addr (a.base_reg (), a.disp ());
	  }
        case PRE_MODIFY:
	  {
            addr_expr a = extract_addr_expr (XEXP (x, 1),
                                             search_start_i, last_access_i,
					     mem_mach_mode, as,
					     inserted_reg_mods);
            if (a.is_invalid ())
              return make_invalid_addr ();
	    return expand_regs ? a : pre_mod_addr (a.base_reg (), a.disp ());
	  }

        default:
          return make_invalid_addr ();
        }

      op1 = extract_addr_expr (XEXP (x, 0), search_start_i, last_access_i,
                               mem_mach_mode, as, inserted_reg_mods);
      if (op1.is_invalid ())
        return op1;

      disp += op1.disp ();

      if (expand_regs)
        return check_make_non_mod_addr (op1.base_reg (), op1.index_reg (),
                                        op1.scale (), disp);

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
          find_reg_value_result r = find_reg_value (x, search_start_i);

          // Stop expanding the reg if the reg can't be expanded any further.
          if (r.value != NULL_RTX && REG_P (r.value) && regs_equal (r.value, x))
            {
              // Add to the sequence's start a reg_mod access that sets
              // the reg to itself. This will be used by the address
              // modification generator as a starting address.
              if (last_access_i)
                {
                  access* new_reg_mod
                    = &as->add_reg_mod (last_access_i,
                                        make_reg_addr (x), make_reg_addr (x),
                                        NULL, x);
                  inserted_reg_mods.push_back (new_reg_mod);
                }

              return make_reg_addr (x);
            }

          // Expand the register's value further.  If the register was
          // modified because of an auto-inc/dec memory access, pass
          // down the machine mode of that access.
          addr_expr reg_addr_expr = extract_addr_expr
            (r.value, prev_nonnote_insn_bb (r.mod_insn), last_access_i,
             find_reg_note (r.mod_insn, REG_INC, NULL_RTX)
               ? r.auto_mod_mode
               : mem_mach_mode,
             as, inserted_reg_mods);

          addr_expr original_reg_addr_expr
            = find_reg_note (r.mod_insn, REG_INC, NULL_RTX)
            ? make_reg_addr (x)
            : extract_addr_expr (r.value, mem_mach_mode);

          // Place all the insns that are used to arrive at the address
          // into AS in the form of reg_mod accesses that can be replaced
          // during address mod generation.
          // For auto-mod mem accesses, insert a reg_mod that sets X to itself.
          if (last_access_i)
            {
              access* new_reg_mod = NULL;

              // If the original or effective address is something AMS can't
              // handle, store the reg's original address as an rtx instead of
              // an addr_expr.
              if (reg_addr_expr.is_invalid ()
                  || original_reg_addr_expr.is_invalid ())
                new_reg_mod = &as->add_reg_mod (last_access_i, r.value,
                                                r.mod_insn, r.reg, 0);

              // Otherwise, store it as a normal addr_expr.
              else
                {
                  new_reg_mod = &as->add_reg_mod (last_access_i,
                                                  original_reg_addr_expr,
                                                  reg_addr_expr,
                                                  r.mod_insn, r.reg,
                                                  infinite_costs);
                }
              inserted_reg_mods.push_back (new_reg_mod);
            }

          // If the expression is something AMS can't handle, use the original
          // reg instead.
          if (reg_addr_expr.is_invalid ()
              || original_reg_addr_expr.is_invalid ())
            return make_reg_addr (x);

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

      op1 = check_make_non_mod_addr (op1.index_reg (), op1.base_reg (),
                                     -scale, -op1.disp ());

      if (code == NEG || op1.is_invalid ())
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
              op1 = check_make_non_mod_addr (invalid_regno, op1.index_reg (),
                                             op1.scale (), op1.disp ());
              op0 = check_make_non_mod_addr (invalid_regno, op0.base_reg (),
                                             2, op0.disp ());
            }
          else if (op1.has_no_index_reg ())
            {
              op0 = check_make_non_mod_addr (invalid_regno, op0.index_reg (),
                                             op0.scale (), op0.disp ());
              op1 = check_make_non_mod_addr (invalid_regno, op1.base_reg (),
                                             2, op1.disp ());
              if (op1.is_invalid ())
                break;
            }
        }
      if (op0.base_reg () == op1.index_reg ())
        {
          op0 = check_make_non_mod_addr (invalid_regno, op0.index_reg (),
                                         op0.scale (), op0.disp ());

          op1 = check_make_non_mod_addr (op1.base_reg (), op1.index_reg (),
                                         op1.scale () + 1, op1.disp ());
          if (op1.is_invalid ())
            break;
        }
      if (op1.base_reg () == op0.index_reg ())
        {
          op1 = check_make_non_mod_addr (invalid_regno, op1.index_reg (),
                                         op1.scale (), op1.disp ());
          op0 = check_make_non_mod_addr (op0.base_reg (), op0.index_reg (),
                                         op0.scale () + 1, op0.disp ());
          if (op0.is_invalid ())
            break;

        }
      if (op0.index_reg () == op1.index_reg ())
        {
          op0 = check_make_non_mod_addr (op0.base_reg (), op0.index_reg (),
                                         op0.scale () + op1.scale (), op0.disp ());
          op1 = check_make_non_mod_addr (op1.base_reg (), invalid_regno,
                                         0, op1.disp ());
          if (op0.is_invalid ())
            break;
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
      return check_make_non_mod_addr (base_reg, index_reg, scale, disp);

    // Change shift into multiply.
    case ASHIFT:

      // OP1 must be a non-negative constant.
      if (op1.has_no_base_reg () && op1.has_no_index_reg ()
          && op1.disp () >= 0)
        {
          disp_t mul = disp_t (1) << op1.disp ();
          op1 = check_make_non_mod_addr (invalid_regno, invalid_regno, 0, mul);
          if (op1.is_invalid ())
            break;
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
      return check_make_non_mod_addr (invalid_regno, index_reg,
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
      if (visited_addr_reg (x, addr_reg, as))
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
	found |= collect_addr_reg_uses_2 (as, addr_reg, insn, XVECEXP (x, 0, i),
					  out, skip_addr_reg_mods);
      break;

    case SET:
      if (skip_addr_reg_mods)
        {
          if (SET_DEST (x) == addr_reg)
            break;
          if (visited_addr_reg (SET_DEST (x), addr_reg, as))
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
              && visited_addr_reg (use_expr.base_reg (), addr_reg, as))
            {
              *out++ = std::make_pair (&x, insn);
              return true;
            }

	  for (int i = 0; i < GET_RTX_LENGTH (GET_CODE (x)); i++)
	    found |= collect_addr_reg_uses_2 (as, addr_reg, insn, XEXP (x, i),
					      out, skip_addr_reg_mods);
        }
      break;
    }
  return found;
}

// Returns true if X is the same register as ADDR_REG or if X is an
// address reg of the sequence AS that was already visited.  Used by
// collect_addr_reg_uses_2.
bool sh_ams::visited_addr_reg (rtx x, rtx addr_reg, access_sequence& as)
{
  if (addr_reg)
    return x == addr_reg;

  std::pair <access_sequence::addr_reg_map::iterator,
             access_sequence::addr_reg_map::iterator> found_addr_reg =
    as.addr_regs ().equal_range (x);
  if (found_addr_reg.first == found_addr_reg.second)
    return false;

  for (access_sequence::addr_reg_map::iterator it = found_addr_reg.first;
       it != found_addr_reg.second; ++it)
    {
      if (it->second->visited ())
        return true;
    }
  return false;
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

  collect_addr_reg_uses_1 (as, addr_reg, start_insn,
			   BLOCK_FOR_INSN (start_insn), visited_bb,
			   abort_at_insn, out, skip_addr_reg_mods,
			   stay_in_curr_bb, stop_after_first);
}

// Split the access sequence pointed to by AS_IT into multiple sequences,
// grouping the accesses according to their base register.
// The new sequences are placed into SEQUENCES in place of the old one.
// Return an iterator to the next sequence after the newly inserted sequences.
std::list<sh_ams::access_sequence>::iterator
sh_ams::split_access_sequence (std::list<access_sequence>::iterator as_it,
                               std::list<access_sequence>& sequences)
{
  typedef std::map<rtx, split_sequence_info> new_seq_map;

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
            *sequences.insert (as_it, access_sequence ());
          new_seqs.insert (std::make_pair (key, split_sequence_info (&new_as)));
        }
    }

  // Add each memory and reg_use access from the original sequence to the
  // appropriate new sequence.  Also add the reg_mod accesses to all
  // sequences where they are used to calculate addresses.
  //
  // To determine which reg_mods should be added to a sequence, we go over
  // the accesses twice: In the first pass, we record the address regs that
  // the sequence uses.  In the second, we add the relevant accesses to the
  // sequence.
  sh_ams::access_sequence::iterator last_mem_acc = as.accesses ().end ();
  for (unsigned pass = 0; pass < 2; ++pass)
    {
      bool add_to_sequence = (pass==1);
      for (sh_ams::access_sequence::reverse_iterator accs =
             as.accesses ().rbegin (); accs != as.accesses ().rend (); ++accs)
        {
          // reg_mods with no original address are split
          // like the memory and reg_use accesses.
          if (accs->access_type () == reg_mod
              && !(accs->original_address ().is_invalid ()
                   && !accs->address ().is_invalid ()))
            split_access_sequence_1 (new_seqs, *accs, add_to_sequence, false);
          else
            {
              if (add_to_sequence && last_mem_acc == as.accesses ().end ())
                last_mem_acc = stdx::prev (accs.base ());

              rtx key = accs->address ().is_invalid ()
                ? NULL : accs->address ().base_reg ();
              split_sequence_info& new_seq = new_seqs.find(key)->second;

              split_access_sequence_2 (new_seq, *accs);
              if (add_to_sequence)
                new_seq.as ()->accesses ().push_front (*accs);
            }
        }
    }

  // Add remaining reg_mod accesses from the end of the original sequence.
  for (sh_ams::access_sequence::iterator accs = last_mem_acc;
       accs != as.accesses ().end (); ++accs)
    {
      if (accs->access_type () == reg_mod
          && !(accs->original_address ().is_invalid ()
               && !accs->address ().is_invalid ()))
        split_access_sequence_1 (new_seqs, *accs, false, true);
    }

  // Remove the old sequence and return the next element after the
  // newly inserted sequences.
  return sequences.erase (as_it);
}

// Internal function of split_access_sequence.  Adds the reg_mod access ACC to
// those sequences in NEW_SEQS that use it in their address calculations.
void
sh_ams::split_access_sequence_1 (std::map<rtx, split_sequence_info >& new_seqs,
                                 sh_ams::access& acc,
                                 bool add_to_front, bool add_to_back)
{
  typedef std::map<rtx, split_sequence_info> new_seq_map;
  for (new_seq_map::iterator seqs = new_seqs.begin ();
       seqs != new_seqs.end (); ++seqs)
    {
      split_sequence_info& seq_info = seqs->second;
      access_sequence& as = *seq_info.as ();

      // Add the reg_mod access only if it's used to calculate
      // one of the addresses in this new sequence.
      if (!seq_info.uses_addr_reg (acc.address_reg ()))
        continue;

      split_access_sequence_2 (seq_info, acc);
      if (add_to_front)
        {
          as.accesses ().push_front (acc);
          as.start_addresses ().add (as.accesses ().begin ());
        }
      else if (add_to_back)
        {
          as.accesses ().push_back (acc);
          as.start_addresses ().add (stdx::prev (as.accesses ().end ()));
        }
    }
}

// Internal function of split_access_sequence.  Adds all the address registers
// referenced by ACC to ADDR_REGS.
void
sh_ams::split_access_sequence_2 (split_sequence_info& seq_info,
                                 sh_ams::access& acc)
{
  if (acc.address_reg ())
    seq_info.add_reg (acc.address_reg ());
  if (!acc.original_address ().is_invalid ())
    {
      if (acc.original_address ().has_base_reg ())
        seq_info.add_reg (acc.original_address ().base_reg ());
      if (acc.original_address ().has_index_reg ())
        seq_info.add_reg (acc.original_address ().index_reg ());
    }
  else if (acc.addr_rtx ())
    {
      // If the address is stored as an RTX, search it for regs.
      subrtx_var_iterator::array_type array;
      FOR_EACH_SUBRTX_VAR (it, array, acc.addr_rtx (), NONCONST)
        {
          rtx x = *it;
          if (REG_P (x))
            seq_info.add_reg (x);
        }
    }
}

// Generate the address modifications needed to arrive at the addresses in
// the access sequence.  They are inserted in the form of reg_mod accesses
// between the regular accesses.
// FIXME: Handle trailing reg_mods/uses.
void
sh_ams::access_sequence::gen_address_mod (delegate& dlg, int base_lookahead)
{
  log_msg ("Generating address modifications\n");

  find_addr_regs ();

  typedef access_type_matches<reg_mod> reg_mod_match;
  typedef filter_iterator<iterator, reg_mod_match> reg_mod_iter;

  // Remove the original reg_mod accesses.
  for (reg_mod_iter accs = begin<reg_mod_match> (),
       accs_end = end<reg_mod_match> (); accs != accs_end; )
    {
      const addr_expr& ae = accs->address ();

      // Keep the reg_mods with no original address as they're going
      // to be optimized.
      if (accs->original_address ().is_invalid () && !ae.is_invalid ())
        ++accs;
      else
        {
          // Clone the starting addresses into new registers.  These will be
          // used as the starting points of the address calculations.
          if (!ae.is_invalid () && ae.has_base_reg ()
              && ae.has_no_index_reg () && ae.has_no_disp ()
              && regs_equal (ae.base_reg (), accs->address_reg ()))
            {
              access& reg_clone_acc
                = add_reg_mod (accs, ae, ae, NULL,
                               gen_reg_rtx (GET_MODE (accs->address_reg ())), 0);

              // The cloning should happen before any other
              // address reg modification.
              reg_clone_acc.set_emit_before_insn (start_insn ());
            }
          // Also clone the addr regs that get set to an unknown value.
          else if (ae.is_invalid () || accs->original_address ().is_invalid ())
            {
              access& reg_clone_acc
                = add_reg_mod (accs, make_reg_addr (accs->address_reg ()),
                               make_reg_addr (accs->address_reg ()), NULL,
                               gen_reg_rtx (GET_MODE (accs->address_reg ())), 0);

              // In this case, the cloning should happen after the reg is set.
              if (!accs->emit_after_insn ())
                reg_clone_acc.set_emit_after_insn (accs->insn ());
            }

          accs = remove_access (accs);
        }
    }

  typedef filter_iterator<iterator, access_to_optimize> acc_opt_iter;

  for (acc_opt_iter accs = begin<access_to_optimize> (),
       accs_end = end<access_to_optimize> (); accs != accs_end;)
    {
      gen_min_mod (accs, dlg,
                   base_lookahead + dlg.adjust_lookahead_count (*this, (iterator)accs),
                   true);
      acc_opt_iter next_acc = accs;
      ++next_acc;
      accs = next_acc;
    }

  for (reg_mod_iter accs = begin<reg_mod_match> (),
       accs_end = end<reg_mod_match> (); accs != accs_end; )
    {
      // Mark the reg_mod accesses as "unused" again.
      accs->set_unused ();

      // Remove any unused reg <- constant copy that might have been
      // added while trying different accesses.
      if (!accs->original_address ().is_invalid ()
	  && accs->original_address ().has_no_base_reg ()
	  && accs->original_address ().has_no_index_reg ())
	{
	  if (!reg_used_in_sequence (accs->address_reg (),
				     stdx::next ((iterator)accs)))
	    {
	      accs = remove_access (accs);
	      continue;
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
gen_min_mod (filter_iterator<iterator, access_to_optimize> acc, delegate& dlg,
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
  access_sequence::iterator min_start_base, min_start_index;
  addr_expr min_end_base, min_end_index;
  mod_tracker tracker;

  filter_iterator<iterator, access_to_optimize> next_acc =
	lookahead_num ? stdx::next (acc) : end<access_to_optimize> ();

  // Go through the alternatives for this access and keep
  // track of the one with minimal costs.
  for (access::alternative_set::iterator alt = acc->alternatives ().begin ();
       alt != acc->alternatives ().end (); ++alt)
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
          end_index = non_mod_addr (invalid_regno, ae.index_reg (),
				    ae.scale (), ae.disp ());
        }

      // Get the costs for using this alternative.
      int alt_min_cost = alt->cost ();

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
          index_mod_cost = find_min_mod_cost (end_index, acc, 0, 0,
					      alt_ae.type (), dlg);
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
          gen_mod_for_alt (*alt, base_mod_cost.min_start_addr,
			   index_mod_cost.min_start_addr,
			   end_base, end_index, acc, tracker, dlg);

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
               (int)(min_alternative - acc->alternatives ().begin ()),
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
void
sh_ams::access_sequence::gen_mod_for_alt (access::alternative& alternative,
					  access_sequence::iterator start_base,
					  access_sequence::iterator start_index,
					  const addr_expr& end_base,
					  const addr_expr& end_index,
					  access_sequence::iterator acc,
					  mod_tracker& mod_tracker,
					  delegate& dlg)
{
  machine_mode acc_mode = Pmode;
  if (acc->access_type () == reg_mod)
    acc_mode = GET_MODE (acc->address_reg ());
  else if (acc->access_type () == reg_use)
    acc_mode = GET_MODE (acc->original_address ().base_reg ());

  // Insert the modifications needed to arrive at the address
  // in the base reg.
  mod_addr_result base_insert_result =
    try_modify_addr (start_base, end_base,
                     alternative.address ().disp_min (),
                     alternative.address ().disp_max (),
                     alternative.address ().type (),
                     acc_mode, acc, mod_tracker, dlg);

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
                         acc_mode, acc, mod_tracker, dlg);
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
  mod_tracker.addr_changed_accs ()
    .push_back (std::make_pair (acc, acc->original_address ()));
  acc->set_original_address (alternative.cost (), new_addr_expr);
}

// Return all the start addresses that could be used to arrive at END_ADDR.
//
// FIXME: Avoid copying the list elements over and over.
std::list<sh_ams::access_sequence::iterator>
sh_ams::access_sequence::start_addr_list
::get_relevant_addresses (const addr_expr& end_addr)
{
  std::list<access_sequence::iterator> start_addrs;

  // Constant displacements can always be used as start addresses.
  start_addrs.insert (start_addrs.end (),
                      m_const_addresses.begin (),
                      m_const_addresses.end ());

  // Addresses containing registers might be used if they have a
  // register in common with the end address.
  typedef std::pair <addr_reg_map::iterator,
                     addr_reg_map::iterator> matching_range_t;
  if (end_addr.has_base_reg ())
    {
      matching_range_t r = m_reg_addresses.equal_range (end_addr.base_reg ());
      for (matching_range_t::first_type it = r.first; it != r.second; ++it)
        start_addrs.push_back (it->second);
    }
  if (end_addr.has_index_reg ())
    {
      matching_range_t r = m_reg_addresses.equal_range (end_addr.index_reg ());
      for (matching_range_t::first_type it = r.first; it != r.second; ++it)
        start_addrs.push_back (it->second);
    }

  return start_addrs;
}

// Add START_ADDR to the list of available start addresses.
void
sh_ams::access_sequence::start_addr_list::add (access_sequence::iterator start_addr)
{
  if (start_addr->valid_address ().is_invalid ())
    return;

  // If the address has a base or index reg, add it to M_REG_ADDRESSES.
  if (start_addr->valid_address ().has_base_reg ())
    m_reg_addresses.insert (std::make_pair (start_addr->valid_address ().base_reg (),
                                            start_addr));
  if (start_addr->valid_address ().has_index_reg ())
    m_reg_addresses.insert (std::make_pair (start_addr->valid_address ().index_reg (),
                                            start_addr));

  // Otherwise, add it to the constant list.
  if (start_addr->valid_address ().has_no_base_reg ()
      && start_addr->valid_address ().has_no_index_reg ())
    m_const_addresses.push_back (start_addr);
}

// Remove START_ADDR from the list of available start addresses.
void sh_ams::access_sequence::
start_addr_list::remove (access_sequence::iterator start_addr)
{
  std::pair <addr_reg_map::iterator, addr_reg_map::iterator> matching_range;
  if (start_addr->valid_address ().has_base_reg ())
    {
      matching_range
        = m_reg_addresses.equal_range (start_addr->valid_address ().base_reg ());
      for (addr_reg_map::iterator it = matching_range.first;
           it != matching_range.second; ++it)
        {
          if (it->second == start_addr)
            {
              m_reg_addresses.erase (it);
              break;
            }
        }
    }
  if (start_addr->valid_address ().has_index_reg ())
    {
      matching_range
        = m_reg_addresses.equal_range (start_addr->valid_address ().index_reg ());
      for (addr_reg_map::iterator it = matching_range.first;
           it != matching_range.second; ++it)
        {
          if (it->second == start_addr)
            {
              m_reg_addresses.erase (it);
              break;
            }
        }
    }

  if (start_addr->valid_address ().has_no_base_reg ()
      && start_addr->valid_address ().has_no_index_reg ())
    m_const_addresses.remove (start_addr);
}

// Write the sequence into the insn stream.
void
sh_ams::access_sequence
::update_insn_stream (bool allow_mem_addr_change_new_insns)
{
  log_msg ("update_insn_stream\n");

  bool sequence_started = false;
  rtx_insn* last_insn = NULL;

  for (access_sequence::iterator accs = accesses ().begin ();
       accs != accesses ().end (); ++accs)
    {
      if (accs->insn ())
        last_insn = accs->insn ();
    }

  if (!last_insn)
    {
      log_msg ("Skipping insn gen as the sequence doesn't have any insns\n");
      return;
    }

  // First, add the insns of the accesses that must go strictly
  // before/after another insn.
  for (access_sequence::iterator accs = accesses ().begin ();
       accs != accesses ().end (); ++accs)
    {
      if (accs->access_type () == reg_mod && !accs->is_trailing ()
          && (accs->emit_before_insn () || accs->emit_after_insn ()))
        {
          start_sequence ();
          gen_reg_mod_insns (*accs);
          rtx_insn* new_insns = get_insns ();
          end_sequence ();

          if (accs->emit_before_insn ())
            {
              log_msg ("emitting new insns = \n");
              log_rtx (new_insns);
              log_msg ("\before insn\n");
              log_insn (accs->emit_before_insn ());
              log_msg ("\n");
              emit_insn_before (new_insns, accs->emit_before_insn ());
            }
          else
            {
              log_msg ("emitting new insns = \n");
              log_rtx (new_insns);
              log_msg ("\nafter insn\n");
              log_insn (accs->emit_after_insn ());
              log_msg ("\n");
              emit_insn_after (new_insns, accs->emit_after_insn ());
            }
        }
    }

  // Add the insns of the remaining accesses.
  for (access_sequence::iterator accs = accesses ().begin ();
       accs != accesses ().end (); ++accs)
    {
      if (accs->is_trailing ())
        {
          log_msg ("skipping trailing access\n");
          continue;
        }

      if (sequence_started && accs->insn ()
          && (accs->access_type () == load
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

      if (!accs->should_optimize ())
        {
          log_msg ("access didn't get optimized, skipping\n");
          continue;
        }

      if (accs->original_address ().is_invalid ())
        {
          log_msg ("original address not valid\n");
          continue;
        }

      if (accs->access_type () == reg_mod)
        {
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

          gen_reg_mod_insns (*accs);
        }
      else if (accs->access_type () == reg_use)
        {
          gcc_assert (accs->original_address ().has_base_reg ());
          bool r = accs->set_insn_use_rtx (
			accs->original_address ().to_rtx ());
	  gcc_assert (r);
        }
      else if (accs->access_type () == load || accs->access_type () == store)
        {
          // Update the access rtx to reflect ORIGINAL_ADDRESS.

          rtx new_addr = accs->original_address ().to_rtx ();
	  log_msg ("new addr = ");
	  log_rtx (new_addr);
	  log_msg ("\n");

	  // If the original access used an auto-mod addressing mode,
	  // remove the original REG_INC note.
          // Also add a reg_mod after the mem access that replicates the
          // address reg modification in case it's used somewhere else later.
	  // FIXME: Maybe remove only the notes for the particular regs
	  // instead of removing them all?  Might be interesting for multi-mem
	  // insns (which we don't handle right now at all).
          if (remove_incdec_notes (accs->insn ()))
            {
              rtx mem = accs->addr_rtx_in_insn ();
              addr_expr auto_mod_expr = extract_addr_expr ((XEXP (mem, 0)),
                                                           GET_MODE (mem));
              auto_mod_expr = non_mod_addr (auto_mod_expr.base_reg (),
                                            invalid_regno,
                                            1, auto_mod_expr.disp ());
              add_reg_mod (stdx::next (accs),
                           auto_mod_expr, auto_mod_expr, NULL,
                           auto_mod_expr.base_reg (), 0);
            }

	  if (!accs->set_insn_mem_rtx (new_addr, allow_mem_addr_change_new_insns))
	    {
	      log_msg ("failed to replace mem rtx\n");
	      log_rtx (accs->addr_rtx_in_insn ());
	      log_msg ("\nwith new rtx\n");
	      log_rtx (new_addr);
	      log_msg ("\nin insn\n");
	      log_insn (accs->insn ());
	      log_msg ("\n");
	      abort ();
	    }

          sh_check_add_incdec_notes (accs->insn ());
        }
    }

  // Emit remaining address modifying insns after the last insn in the access.
  if (sequence_started)
    {
      bool emit_after = (GET_CODE (last_insn) == INSN);

      rtx_insn* new_insns = get_insns ();
      end_sequence ();

      log_msg ("emitting new insns = \n");
      log_rtx (new_insns);
      if (emit_after)
        log_msg ("\nafter insn\n");
      else
        log_msg ("\nbefore insn\n");
      log_insn (last_insn);
      log_msg ("\n");
      if (emit_after)
        emit_insn_after (new_insns, last_insn);
      else
        emit_insn_before (new_insns, last_insn);
    }
}

// Generate the address modifying insns of a reg_mod access.
// Used by update_insn_stream.
void
sh_ams::access_sequence
::gen_reg_mod_insns (access& acc)
{
  rtx new_val;

  if (acc.original_address ().has_no_base_reg ()
      && acc.original_address ().has_no_index_reg ())
    {
      new_val = GEN_INT (acc.original_address ().disp ());
      log_msg ("reg mod new val (1) = ");
      log_rtx (new_val);
      log_msg ("\n");
    }
  else
    {
      if (acc.original_address ().has_index_reg ())
        {
          bool subtract = acc.original_address ().has_base_reg ()
            && acc.original_address ().scale () == -1;
          rtx index = subtract ? acc.original_address ().index_reg ()
            : expand_mult (acc.original_address ().index_reg (),
                           acc.original_address ().scale ());

          if (acc.original_address ().has_no_base_reg ())
            new_val = index;
          else if (subtract)
            new_val = expand_minus (acc.original_address ().base_reg (),
                                    index);
          else
            new_val = expand_plus (acc.original_address ().base_reg (),
                                   index);
          log_msg ("reg mod new val (2) = ");
          log_rtx (new_val);
          log_msg ("\n");
        }
      else
        {
          new_val = acc.original_address ().base_reg ();
          log_msg ("reg mod new val (3) = ");
          log_rtx (new_val);
          log_msg ("\n");
        }

      new_val = expand_plus (new_val, acc.original_address ().disp ());
    }

  acc.set_insn (emit_move_insn (acc.address_reg (), new_val));
}

// Get the total cost of using this access sequence.
int
sh_ams::access_sequence::cost (void) const
{
  int cost = 0;
  for (access_sequence::const_iterator accs = accesses ().begin ();
       accs != accesses ().end () && cost != infinite_costs; ++accs)
    cost += accs->cost ();
  return cost;
}

// Recalculate the cost of the accesses in the sequence.
void
sh_ams::access_sequence::update_cost (delegate& dlg)
{
  for (access_sequence::iterator accs = accesses ().begin ();
       accs != accesses ().end (); ++accs)
    {
      if (accs->access_type () == load || accs->access_type () == store)
        {
          // Skip this access if it won't be optimized.
          if (!accs->should_optimize ())
            {
              accs->set_cost (0);
              continue;
            }

          // Find the alternative that the access uses and update
          // its cost accordingly.
          // FIXME: when selecting an alternative, remember the alternative
          // iterator as the "currently selected alternative".  then we don't
          // need to find it over and over again.
          for (access::alternative_set::const_iterator alt
                 = accs->alternatives ().begin (); ; ++alt)
            {
              if (accs->matches_alternative (*alt))
                {
                  accs->set_cost (alt->cost ());
                  break;
                }
              if (alt == accs->alternatives ().end ())
                gcc_unreachable ();
            }
        }
      else if (accs->access_type () == reg_mod)
        {
          // Skip this access if the original address doesn't fit into an
          // addr_expr or if it's a trailing access.
          if (accs->original_address ().is_invalid () || accs->is_trailing ())
            {
              accs->set_cost (0);
              continue;
            }

          int cost = 0;
          const addr_expr &ae = accs->original_address ();

          // Scaling costs
          if (ae.has_no_base_reg () && ae.has_index_reg () && ae.scale () != 1)
            cost += get_reg_mod_cost (dlg, accs->address_reg (),
                                      gen_rtx_MULT (Pmode,
                                                    ae.index_reg (),
                                                    GEN_INT (ae.scale ())),
                                      *this, accs);

          // Costs for adding or subtracting another reg
          else if (ae.has_no_disp () && std::abs (ae.scale ()) == 1
                   && ae.has_base_reg () && ae.has_index_reg ())
            cost += get_reg_mod_cost (dlg, accs->address_reg (),
                                      gen_rtx_PLUS (Pmode,
                                                    ae.index_reg (),
                                                    ae.base_reg ()),
                                      *this, accs);

          // Constant displacement costs
          else if (ae.has_base_reg () && ae.has_no_index_reg ()
                   && ae.has_disp ())
            cost += get_reg_mod_cost (dlg, accs->address_reg (),
                                      gen_rtx_PLUS (Pmode,
                                                    ae.base_reg (),
                                                    GEN_INT (ae.disp ())),
                                      *this, accs);

          // Constant loading costs
          else if (ae.has_no_base_reg () && ae.has_no_index_reg ())
            cost += get_reg_mod_cost (dlg, accs->address_reg (),
                                      GEN_INT (ae.disp ()),
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

          accs->set_cost (cost);
        }
    }

  // Mark the reg_mod accesses as "unused" again.
  std::for_each (accesses ().begin (), accesses ().end (),
                 std::mem_fun_ref (&access::set_unused));
}

// Get the cloning costs associated with ACC, if any.
int
sh_ams::access_sequence::get_clone_cost (access_sequence::iterator& acc,
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
  if (regs_equal (reused_reg, acc->address_reg ()))
    return 0;

  for (access_sequence::iterator prev_accs = accesses ().begin ();
       prev_accs != acc; ++prev_accs)
    {
      if (prev_accs->access_type () == reg_mod
          && regs_equal (prev_accs->address_reg (), reused_reg))
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
  return 0;
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
          for (access::alternative_set::const_iterator
		  alt = accs->alternatives ().begin ();
               alt != accs->alternatives ().end (); ++alt)
            {
              if (alt->cost () < accs->cost ())
                return false;
            }
        }
      else if (accs->cost () > 0)
        return false;
    }
  return true;
}

// Find the cheapest way END_ADDR can be arrived at from one of the addresses
// in the sequence.
// Return the start address that can be changed into END_ADDR with the least
// cost and the actual cost.
sh_ams::access_sequence::min_mod_cost_result
sh_ams::access_sequence
::find_min_mod_cost (const addr_expr& end_addr,
		     access_sequence::iterator acc,
		     disp_t disp_min, disp_t disp_max,
		     addr_type_t addr_type, delegate& dlg)
{
  int min_cost = infinite_costs;
  access_sequence::iterator min_start_addr;
  mod_tracker tracker;
  machine_mode acc_mode = Pmode;
  if (acc->access_type () == reg_mod)
    acc_mode = GET_MODE (acc->address_reg ());
  else if (acc->access_type () == reg_use)
    acc_mode = GET_MODE (acc->original_address ().base_reg ());

  std::list<access_sequence::iterator> start_addrs =
    start_addresses ().get_relevant_addresses (end_addr);
  for (start_addr_list::iterator it = start_addrs.begin ();
       it != start_addrs.end (); ++it)
    {
      int cost = try_modify_addr (*it, end_addr, disp_min, disp_max,
                                  addr_type, acc_mode, acc, tracker, dlg).cost;
      tracker.reset_changes (*this);
      if (cost < min_cost)
        {
          min_cost = cost;
          min_start_addr = *it;
        }
    }

  // If the end addr only has a constant displacement, try loading it into
  // the reg directly.
  if (end_addr.has_no_base_reg () && end_addr.has_no_index_reg ())
    {
      rtx const_reg = gen_reg_rtx (acc_mode);
      add_reg_mod (accesses ().begin (), make_const_addr (end_addr.disp ()),
					 make_const_addr (end_addr.disp ()),
					 NULL, const_reg, 0);
      int cost = try_modify_addr (accesses ().begin (), end_addr,
                                  disp_min, disp_max,
                                  addr_type, acc_mode, acc, tracker, dlg).cost;
      cost += get_reg_mod_cost (dlg, const_reg, GEN_INT (end_addr.disp ()),
                                *this, accesses ().begin ());

      tracker.reset_changes (*this);
      if (cost < min_cost)
        {
          min_cost = cost;
          min_start_addr = accesses ().begin ();
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
// behind ACC and record the sequence modifications in MOD_TRACKER.
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
sh_ams::access_sequence
::try_modify_addr (access_sequence::iterator start_addr, const addr_expr& end_addr,
		   disp_t disp_min, disp_t disp_max, addr_type_t addr_type,
		   machine_mode mode,
		   access_sequence::iterator acc,
		   mod_tracker &mod_tracker,
		   delegate& dlg)
{
  access_sequence::iterator ins_place;
  rtx new_reg = start_addr->address_reg ();
  int cost = start_addr->is_used ()
             ? dlg.addr_reg_clone_cost (start_addr->address_reg (),
                                        *this, acc)
             : 0;
  int prev_cost = 0;
  rtx final_addr_regno = start_addr->address_reg ();

  // Canonicalize the start and end addresses by converting
  // addresses of the form base+disp into index*1+disp.
  addr_expr c_start_addr = start_addr->valid_address ();
  addr_expr c_end_addr = end_addr;
  if (c_start_addr.has_no_index_reg ())
    c_start_addr = non_mod_addr (invalid_regno, c_start_addr.base_reg (), 1,
				 c_start_addr.disp ());
  if (c_end_addr.has_no_index_reg ())
    c_end_addr = non_mod_addr (invalid_regno, c_end_addr.base_reg (), 1,
			       c_end_addr.disp ());

  // If one of the addresses has the form base+index*1, it
  // might be better to switch its base and index reg.
  if (regs_equal (c_start_addr.index_reg (), c_end_addr.base_reg ()))
    {
      if (c_end_addr.has_base_reg ()
          && c_end_addr.has_index_reg () && c_end_addr.scale () == 1)
	c_end_addr = non_mod_addr (c_end_addr.index_reg (),
				   c_end_addr.base_reg (),
				   1, c_end_addr.disp ());
      else if (c_start_addr.has_base_reg ()
               && c_start_addr.has_index_reg () && c_start_addr.scale () == 1)
	c_start_addr = non_mod_addr (c_start_addr.index_reg (),
				     c_start_addr.base_reg (),
				     1, c_start_addr.disp ());
    }

  // If the start address has a base reg, and it's different
  // from that of the end address, give up.
  if (c_start_addr.has_base_reg ()
      && !regs_equal (c_start_addr.base_reg (), c_end_addr.base_reg ()))
    return mod_addr_result (infinite_costs, invalid_regno, 0);

  // Same for index regs, unless we can get to the end address
  // by subtracting.
  if (!regs_equal (c_start_addr.index_reg (), c_end_addr.index_reg ()))
    {
      if (!(c_start_addr.has_no_base_reg ()
            && c_end_addr.has_index_reg ()
            && regs_equal (c_start_addr.index_reg (), c_end_addr.base_reg ())
            && c_start_addr.scale () == 1
            && c_end_addr.scale () == -1))
        return mod_addr_result (infinite_costs, invalid_regno, 0);
    }

  // The start address' regs need to have the
  // same machine mode as the access.
  if (c_start_addr.has_base_reg ()
      && GET_MODE (c_start_addr.base_reg ()) != mode)
    return mod_addr_result (infinite_costs, invalid_regno, 0);
  if (c_start_addr.has_index_reg ()
      && GET_MODE (c_start_addr.index_reg ()) != mode)
    return mod_addr_result (infinite_costs, invalid_regno, 0);

  // Add scaling.
  if (c_start_addr.has_index_reg ()
      && regs_equal (c_start_addr.index_reg (), c_end_addr.index_reg ())
      && c_start_addr.scale () != c_end_addr.scale ())
    {
      // We can't scale if the address has displacement or a base reg.
      if (c_start_addr.has_disp () || c_start_addr.has_base_reg ())
        return mod_addr_result (infinite_costs, invalid_regno, 0);

      // We can only scale by integers.
      gcc_assert (c_start_addr.scale () != 0);
      std::div_t sr = std::div (c_end_addr.scale (), c_start_addr.scale ());

      if (sr.rem != 0)
        return mod_addr_result (infinite_costs, invalid_regno, 0);

      scale_t scale = sr.quot;
      c_start_addr = non_mod_addr (invalid_regno, c_start_addr.index_reg (),
                                   c_end_addr.scale (), 0);

      if (!start_addr->is_used ())
        {
          start_addr->set_used ();
          mod_tracker.use_changed_accs ().push_back (start_addr);
        }

      new_reg = gen_reg_rtx (mode);
      access& new_addr = add_reg_mod (
                 acc,
                 non_mod_addr (invalid_regno,
                               start_addr->address_reg (), scale, 0),
                 c_start_addr, NULL, new_reg, 0);
      final_addr_regno = new_reg;

      ins_place = stdx::prev (acc);
      mod_tracker.inserted_accs ().push_back (ins_place);

      cost += get_reg_mod_cost (dlg, new_reg,
                                gen_rtx_MULT (mode,
                                              start_addr->address_reg (),
                                              GEN_INT (scale)),
                                *this, acc);
      new_addr.set_cost (cost - prev_cost);
      prev_cost = cost;
      start_addr = stdx::prev (acc);
    }

  // Try subtracting regs.
  if (c_start_addr.has_no_base_reg ()
      && c_end_addr.has_index_reg ()
      && regs_equal (c_start_addr.index_reg (), c_end_addr.base_reg ())
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

      new_reg = gen_reg_rtx (mode);
      access& new_addr = add_reg_mod (
                 acc,
                 non_mod_addr (start_addr->address_reg (),
                               c_end_addr.index_reg (),
                               -1, 0),
                 c_start_addr, NULL, new_reg, 0);
      final_addr_regno = new_reg;

      ins_place = stdx::prev (acc);
      mod_tracker.inserted_accs ().push_back (ins_place);

      cost += get_reg_mod_cost (dlg, new_reg,
                                gen_rtx_PLUS (mode,
                                              start_addr->address_reg (),
                                              c_end_addr.index_reg ()),
                                *this, acc);
      new_addr.set_cost (cost - prev_cost);
      prev_cost = cost;
      start_addr = stdx::prev (acc);
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

      new_reg = gen_reg_rtx (mode);
      access& new_addr = add_reg_mod (
                 acc,
                 non_mod_addr (c_start_addr.base_reg (),
                               start_addr->address_reg (), 1, 0),
                 c_start_addr, NULL, new_reg, 0);
      final_addr_regno = new_reg;

      ins_place = stdx::prev (acc);
      mod_tracker.inserted_accs ().push_back (ins_place);

      cost += get_reg_mod_cost (dlg, new_reg,
                                gen_rtx_PLUS (mode,
                                              start_addr->address_reg (),
                                              c_end_addr.base_reg ()),
                                *this, acc);
      new_addr.set_cost (cost - prev_cost);
      prev_cost = cost;
      start_addr = stdx::prev (acc);
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

      new_reg = gen_reg_rtx (mode);
      access& new_addr = add_reg_mod (
                 acc,
                 non_mod_addr (start_addr->address_reg (),
                               invalid_regno, 1, disp),
                 c_start_addr, NULL, new_reg, 0);
      final_addr_regno = new_reg;

      ins_place = stdx::prev (acc);
      mod_tracker.inserted_accs ().push_back (ins_place);

      cost += get_reg_mod_cost (dlg, new_reg,
                                gen_rtx_PLUS (mode,
                                              start_addr->address_reg (),
                                              GEN_INT (disp)),
                                *this, acc);
      new_addr.set_cost (cost - prev_cost);
      prev_cost = cost;
      start_addr = stdx::prev (acc);
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
      new_reg = gen_reg_rtx (mode);
      access& new_addr = add_reg_mod (acc, make_reg_addr (pre_mod_reg),
                                       c_start_addr, NULL, new_reg, 0);
      final_addr_regno = new_reg;

      ins_place = stdx::prev (acc);
      mod_tracker.inserted_accs ().push_back (ins_place);

      new_addr.set_cost (cost - prev_cost);
      prev_cost = cost;
    }

  return mod_addr_result (cost, final_addr_regno, c_start_addr.disp ());
}



// Find all the address regs in the access sequence (i.e. the regs whose value
// was changed by a reg_mod access) and place them into M_ADDR_REGS. Pair them
// with the reg_mod accesses that modified them and set those accesses'
// M_VALID_AT_END field as needed.
// If HANDLE_CALL_USED_REGS is true, add reg_mod accesses before any call insn
// to ensure that the regs used by the call take on their correct values by then.
void
sh_ams::access_sequence::find_addr_regs (bool handle_call_used_regs)
{
  addr_regs ().clear ();

  addr_reg_map hard_addr_regs;

  for (access_sequence::iterator accs = accesses ().begin ();
       accs != accesses ().end (); ++accs)
    {
      if (accs->is_trailing ())
        break;

      // If this is a reg_mod access, add its address register to addr_regs.
      if (accs->access_type () == reg_mod)
        {
          std::pair <addr_reg_map::iterator, addr_reg_map::iterator>
            prev_values = addr_regs ().equal_range (accs->address_reg ());

          // Don't add it if there's already an entry and this reg_mod
          // only sets the reg to itself.
          if (prev_values.first == prev_values.second
              || accs->original_address ().is_invalid ()
              || accs->original_address ().has_index_reg ()
              || accs->original_address ().has_disp ()
              || accs->original_address ().base_reg () != accs->address_reg ()
              || (!accs->address ().is_invalid ()
                  && (accs->address ().has_index_reg ()
                      || accs->address ().has_disp ()
                      || accs->address ().base_reg () != accs->address_reg ())))
            {
              // Since we found a new version of this addr reg, the previous
              // ones won't be valid at the sequence's end.
              for (addr_reg_map::iterator it = prev_values.first;
                   it!= prev_values.second; ++it)
                it->second->set_invalid_at_end ();
              accs->set_valid_at_end ();

              addr_regs ().insert (std::make_pair (accs->address_reg (),
                                                   accs));
              if (HARD_REGISTER_P (accs->address_reg ()))
                hard_addr_regs.insert (std::make_pair (accs->address_reg (),
                                                       accs));;
            }
        }

      if (!handle_call_used_regs)
        continue;

      // Search for call insns and REG_DEAD notes in the insns between
      // this and the next access.
      access_sequence::iterator next = stdx::next (accs);
      if (accs->insn () && next != accesses ().end () && !next->is_trailing ())
        {
          for (rtx_insn *i = accs->insn (); ; i = NEXT_INSN (i))
            {
              if (!INSN_P (i) || !NONDEBUG_INSN_P (i))
                continue;

              if (handle_call_used_regs && i != accs->insn ()
                  && GET_CODE (i) == CALL_INSN)
                {
                  std::map<rtx, access*>::iterator addr_reg;
                  rtx prev_reg = NULL;
                  for (addr_reg_map::iterator it =
                         hard_addr_regs.begin ();
                       it != hard_addr_regs.end (); ++it)
                    {
                      rtx reg = it->first;
                      access_sequence::iterator acc = it->second;

                      if (!regs_equal (reg, prev_reg) && reg_set_p (reg, i))
                        acc->set_invalid_at_end ();

                      prev_reg = reg;

                      if (!acc->valid_at_end () || acc->address ().is_invalid ())
                        continue;

                      // Don't add any reg_mod if it'd just set the hardreg
                      // to itself.
                      const addr_expr& ae = acc->address ();
                      if (ae.has_no_index_reg () && ae.has_no_disp ()
                          && ae.base_reg () == acc->address_reg ())
                        continue;
                    }
                }
              for (rtx note = REG_NOTES (i); note; note = XEXP (note, 1))
                {
                  if (REG_NOTE_KIND (note) != REG_DEAD)
                    continue;

                  // If an addr reg is no longer alive, set all its
                  // accesses' M_VALID_AT_END to false.
                  std::pair <addr_reg_map::iterator, addr_reg_map::iterator>
                    found_accs = addr_regs ().equal_range (XEXP (note, 0));
                  for (addr_reg_map::iterator it = found_accs.first;
                       it!= found_accs.second; ++it)
                    it->second->set_invalid_at_end ();
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
void
sh_ams::access_sequence::add_missing_reg_mods (void)
{
  find_addr_regs ();

  std::vector<access*> inserted_reg_mods;
  rtx prev_reg = NULL;
  for (addr_reg_map::iterator it = addr_regs ().begin ();
       it != addr_regs ().end (); ++it)
    {
      rtx reg = it->first;
      if (regs_equal (reg, prev_reg))
        continue;
      prev_reg = reg;

      // Trace back the address reg's value, inserting any missing
      // modification of this reg to the sequence.
      basic_block bb = start_bb ();

      inserted_reg_mods.clear ();
      extract_addr_expr (reg, BB_END (bb), BB_END (bb),
                         Pmode, this, inserted_reg_mods);
    }
}

// Check whether REG is used in any access after SEARCH_START.
bool
sh_ams::access_sequence
::reg_used_in_sequence (rtx reg, access_sequence::iterator search_start)
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

bool
sh_ams::access_sequence
::reg_used_in_sequence (rtx reg)
{
  return reg_used_in_sequence (reg, accesses ().begin ());
}

// Find all uses of the address registers that aren't mem loads/stores
// or address modifications, and add them to the sequence
// as reg_use accesses.
void
sh_ams::access_sequence::find_reg_uses (delegate& dlg)
{
  std::vector<std::pair<rtx*, rtx_insn*> > used_regs;
  rtx_insn* last_insn = NULL;

  find_addr_regs ();

  accesses ().begin ()->set_visited ();

  for (access_sequence::iterator accs = accesses ().begin ();
       accs != accesses ().end (); ++accs)
    {
      access_sequence::iterator next_acc = stdx::next (accs);
      if (next_acc != accesses ().end ())
        next_acc->set_visited ();

      if (!accs->insn ())
        continue;
      last_insn = accs->insn ();

      if (accs->access_type () == reg_use)
        continue;

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
            = extract_addr_expr (*use_ref, prev_nonnote_insn_bb (use_insn),
                                 NULL, Pmode, this);

          if (!effective_addr.is_invalid ())
            {
              add_reg_use (next_acc, use_expr, effective_addr,
                           use_ref, use_insn, 0);
              access_sequence::iterator acc = stdx::prev (next_acc);
              acc->set_cost (dlg.addr_reg_mod_cost (NULL, *use_ref, *this, acc));
            }
        }
    }

  if (!last_insn)
    return;

  // Add trailing address reg uses to the end of the sequence.
  rtx prev_reg = NULL;
  for (addr_reg_map::iterator it = addr_regs ().begin ();
       it != addr_regs ().end (); ++it)
    {
      rtx reg = it->first;
      if (regs_equal (reg, prev_reg))
        continue;
      prev_reg = reg;

      used_regs.clear ();
      collect_addr_reg_uses (*this, reg, last_insn, NULL,
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
                       trailing_use_ref, insns, 0);
          access_sequence::iterator acc = stdx::prev (accesses ().end ());
          acc->set_cost (dlg.addr_reg_mod_cost (NULL, *trailing_use_ref,
                                                *this, acc));
        }
    }

  // Reset the "visited" flags.
  std::for_each (accesses ().begin (), accesses ().end (),
                 std::mem_fun_ref (&access::reset_visited));
}

// Find the values of all address registers that are still alive
// at the end of the access sequence, and set them to their values with
// reg_mod accesses. This will force the address modification generator
// to keep their original values at the end of the basic blocks.
void
sh_ams::access_sequence::find_reg_end_values (void)
{
  // Update the address regs' final values.
  find_addr_regs (true);

  for (addr_reg_map::iterator it = addr_regs ().begin ();
       it != addr_regs ().end (); ++it)
    {
      access_sequence::iterator acc = it->second;

      // Skip the reg_mod access if it isn't alive or has a different value
      // at the sequence's end.
      if (!acc->valid_at_end ())
        continue;

      // Don't add the addr reg if it wasn't modified during the sequence
      // (i.e. if its effective address is the address reg itself).
      if (acc->address ().is_invalid ()
          || (acc->address ().has_no_index_reg ()
              && acc->address ().has_no_disp ()
              && acc->address ().base_reg () == acc->address_reg ()))
        continue;

      access& new_reg_mod
        = add_reg_mod (accesses ().end (), make_invalid_addr (), acc->address (),
                       NULL, acc->address_reg (), 0, false);
      new_reg_mod.set_emit_after_insn (acc->insn ());
    }
}

// Fill the m_inc/dec_chain fields of the accesses in the sequence.
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
void
sh_ams::access_sequence::calculate_adjacency_info (void)
{
  typedef access_type_matches<load, store, reg_use> match;
  typedef filter_iterator<iterator, match> iter;

  for (iter m = begin<match> (), mend = end<match> (); m != mend; )
    {
      iter inc_end = std::adjacent_find (m, mend, not_adjacent_inc);
      if (inc_end != mend)
        ++inc_end;

      const int inc_len = std::distance (m, inc_end);

      for (int i = 0; i < inc_len; ++i)
	{
	  m->set_inc_chain (access::adjacent_chain (i, inc_len));
	  ++m;
	}
    }

  for (iter m = begin<match> (), mend = end<match> (); m != mend; )
    {
      iter dec_end = std::adjacent_find (m, mend, not_adjacent_dec);
      if (dec_end != mend)
        ++dec_end;

      const int dec_len = std::distance (m, dec_end);

      for (int i = 0; i < dec_len; ++i)
	{
	  m->set_dec_chain (access::adjacent_chain (i, dec_len));
	  ++m;
	}
    }
}

void
sh_ams::access_sequence
::update_access_alternatives (delegate& d, access_sequence::iterator a,
			      bool force_validation, bool disable_validation)
{
  bool val_alts = a->validate_alternatives ();

  if (a->access_type () != load && a->access_type () != store)
    {
      // If the access isn't a true memory access, the
      // address has to be loaded into a single register.
      a->alternatives ().push_back (access::alternative (0, make_reg_addr ()));
      a->set_validate_alternatives (false);
      return;
    }

  d.mem_access_alternatives (a->alternatives (), *this, a, val_alts);
  a->set_validate_alternatives (val_alts);

  typedef access::alternative_valid match;
  typedef filter_iterator<access::alternative_set::iterator, match> iter;

  // By default alternative validation is enabled for all accesses.
  // The target's delegate implementation might disable validation for insns
  // to speed up processing, if it knows that all the alternatives are valid.
  if ((a->validate_alternatives () || force_validation)
      && (a->access_type () == load || a->access_type () == store)
      && !disable_validation)
    {
      log_msg ("\nvalidating alternatives for insn\n");
      log_insn (a->insn ());

      #define log_invalidate_cont(msg) do { if (dump_file != NULL) { \
	log_msg ("alternative  "); \
	log_addr_expr (alt->address ()); \
	log_msg ("  invalid: %s\n", msg); } \
	alt->set_invalid (); \
	goto Lcontinue; } while (0)

      // Alternatives might have reg placeholders such as any_regno.
      // When validating the change in the insn we need to have real pseudos.
      // To avoid creating a lot of pseudos, use this one.
      rtx tmp_reg = gen_rtx_REG (Pmode, LAST_VIRTUAL_REGISTER + 1);

      addr_expr tmp_addr;

      for (iter alt = iter (a->alternatives ().begin (),
			    a->alternatives ().end ()),
	   alt_end = iter (a->alternatives ().end (),
			   a->alternatives ().end ()); alt != alt_end; ++alt)
	{
	  if (alt->address ().has_no_base_reg ())
	    log_invalidate_cont ("has no base reg");

	  tmp_addr = alt->address ();
	  if (tmp_addr.base_reg () == any_regno)
	    tmp_addr.set_base_reg (tmp_reg);
	  if (tmp_addr.index_reg () == any_regno)
	    tmp_addr.set_index_reg (tmp_reg);

	  if (!a->try_set_insn_mem_rtx (tmp_addr.to_rtx ()))
	    log_invalidate_cont ("failed to substitute regs");

	  if (alt->address ().disp_min () > alt->address ().disp_max ())
	    log_invalidate_cont ("min disp > max disp");

	  if (alt->address ().disp_min () != alt->address ().disp_max ())
	    {
	      // Probe some displacement values and hope that we cover enough.
	      tmp_addr.set_disp (alt->address ().disp_min ());
	      if (!a->try_set_insn_mem_rtx (tmp_addr.to_rtx ()))
		log_invalidate_cont ("bad min disp");

	      tmp_addr.set_disp (alt->address ().disp_max ());
	      if (!a->try_set_insn_mem_rtx (tmp_addr.to_rtx ()))
		log_invalidate_cont ("bad max disp");
	    }

	  if (alt->address ().has_index_reg ())
	    {
	      if (alt->address ().scale_min () > alt->address ().scale_max ())
		log_invalidate_cont ("min scale > max scale");

	      if (alt->address ().scale_min () != alt->address ().scale_max ())
		{
		  // Probe some displacement and index scale combinations and
		  // hope that we cover enough.
		  tmp_addr.set_disp (alt->address ().disp_min ());
		  tmp_addr.set_scale (alt->address ().scale_min ());
		  if (!a->try_set_insn_mem_rtx (tmp_addr.to_rtx ()))
		    log_invalidate_cont ("bad min disp min scale");

		  tmp_addr.set_disp (alt->address ().disp_min ());
		  tmp_addr.set_scale (alt->address ().scale_max ());
		  if (!a->try_set_insn_mem_rtx (tmp_addr.to_rtx ()))
		    log_invalidate_cont ("bad min disp max scale");

		  tmp_addr.set_disp (alt->address ().disp_max ());
		  tmp_addr.set_scale (alt->address ().scale_min ());
		  if (!a->try_set_insn_mem_rtx (tmp_addr.to_rtx ()))
		    log_invalidate_cont ("bad max disp min scale");

		  tmp_addr.set_disp (alt->address ().disp_max ());
		  tmp_addr.set_scale (alt->address ().scale_max ());
		  if (!a->try_set_insn_mem_rtx (tmp_addr.to_rtx ()))
		    log_invalidate_cont ("bad max disp max scale");
		}
	    }

        Lcontinue:;
	}

      #undef log_set_invalid_continue
    }

  // Remove invalid alternatives from the set.
  // Instead we could also use a filter_iterator each time the
  // alternatives are accessed.  This would allow for more flexible
  // alternative valid/invalid scenarios.  Currently we allow invalid
  // alternatives only right here.
  access::alternative_set::iterator first_invalid =
	std::stable_partition (a->alternatives ().begin (),
			       a->alternatives ().end (),
			       access::alternative_valid ());

  // FIXME: Implement erase (iter, iter) for alternative_set.
  if (first_invalid != a->alternatives ().end ())
    {
      unsigned int c = std::distance (first_invalid, a->alternatives ().end ());
      log_msg ("removing %u invalid alternatives\n", c);

      for (; c > 0; --c)
	a->alternatives ().pop_back ();
    }

  if (a->alternatives ().empty ())
    {
      log_msg ("no valid alternatives, not optimizing this access\n");
      a->set_should_optimize (false);
    }

  // At least on clang/libc++ there is a problem with bind1st, mem_fun and
  // &access::matches_alternative.
  access::alternative_set::iterator alt_match;
  for (alt_match = a->alternatives ().begin ();
       alt_match != a->alternatives ().end (); ++alt_match)
    if (a->matches_alternative (*alt_match))
      break;

  if (alt_match == a->alternatives ().end ())
    {
      log_msg ("original address does not match any alternative, "
	       "not optimizing this access\n");
      a->set_should_optimize (false);
    }
}

int
sh_ams::get_reg_mod_cost (delegate &dlg, const_rtx reg, const_rtx val,
			  const access_sequence& as,
			  access_sequence::const_iterator acc)
{
  if (REG_P (val))
    return 0;

  return dlg.addr_reg_mod_cost (reg, val, as, acc);
}

unsigned int
sh_ams::execute (function* fun)
{
  log_msg ("sh-ams pass\n");
  log_options (m_options);
  log_msg ("\n\n");

//  df_set_flags (DF_DEFER_INSN_RESCAN); // needed?

  df_note_add_problem ();
  df_analyze ();

  std::list<access_sequence> sequences;
  std::vector<std::pair<rtx*, access_type_t> > mems;

  log_msg ("extracting access sequences\n");
  basic_block bb;
  FOR_EACH_BB_FN (bb, fun)
    {
      rtx_insn* i;

      log_msg ("BB #%d:\n", bb->index);
      log_msg ("finding mem accesses\n");

      // Construct the access sequence from the access insns.
      sequences.push_back (access_sequence ());
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
  for (std::list<access_sequence>::iterator as = sequences.begin ();
       as != sequences.end ();)
    {
      log_access_sequence (*as, false);
      log_msg ("\n\n");

      if (as->accesses ().empty ())
	{
	  ++as;
	  continue;
	}

      log_msg ("add_missing_reg_mods\n");
      as->add_missing_reg_mods ();

      log_access_sequence (*as, false);
      log_msg ("\n\n");

      log_msg ("find_reg_uses\n");
      as->find_reg_uses (m_delegate);

      log_access_sequence (*as, false);
      log_msg ("\n\n");

      log_msg ("find_reg_end_values\n");
      as->find_reg_end_values ();

      log_access_sequence (*as, false);
      log_msg ("\n\n");

      log_msg ("split_access_sequence\n");
      if (m_options.split_sequences)
        as = split_access_sequence (as, sequences);
      else
        ++as;
    }

  log_msg ("\nprocessing split sequences\n");
  for (std::list<access_sequence>::iterator as = sequences.begin ();
       as != sequences.end (); ++as)
    {
      log_access_sequence (*as, false);
      log_msg ("\n\n");

      if (as->accesses ().empty ())
	continue;

      log_msg ("doing adjacency analysis\n");
      as->calculate_adjacency_info ();

      log_access_sequence (*as, false);
      log_msg ("\n\n");

      log_msg ("updating access alternatives\n");
      {
	typedef access_to_optimize match;
	typedef filter_iterator<access_sequence::iterator, match> iter;

	for (iter a = as->begin<match> (), a_end = as->end<match> ();
	     a != a_end; ++a)
	  as->update_access_alternatives (m_delegate, a,
					  m_options.force_alt_validation,
					  m_options.disable_alt_validation);
      }

      log_access_sequence (*as, true);
      log_msg ("\n\n");

      log_msg ("updating costs\n");
      {
	typedef access_type_matches<load, store> match;
	typedef filter_iterator<access_sequence::iterator, match> iter;

	for (iter m = as->begin<match> (), mend = as->end<match> ();
	     m != mend; ++m)
	  for (access::alternative_set::iterator
		alt = m->alternatives ().begin ();
	       alt != m->alternatives ().end (); ++alt)
	    m_delegate.adjust_alternative_costs (*alt, *as, m.base_iterator ());
      }

      as->update_cost (m_delegate);
      int original_cost = as->cost ();

      log_access_sequence (*as);
      log_msg ("\n\n");

      if (as->cost_already_minimal ())
        {
          log_msg ("costs are already minimal\n");

	  if (m_options.check_minimal_cost)
	    continue;

	  log_msg ("continuing anyway\n");
        }

      log_msg ("gen_address_mod\n");
      as->gen_address_mod (m_delegate, m_options.base_lookahead_count);

      as->update_cost (m_delegate);
      int new_cost = as->cost ();

      log_access_sequence (*as, false);
      log_msg ("\n");

      as->set_modify_insns (true);
      if (new_cost >= original_cost)
	{
	  log_msg ("new_cost (%d) >= original_cost (%d)",
		   new_cost, original_cost);

	  if (m_options.check_original_cost)
	    {
	      log_msg ("  not modifying\n");
	      as->set_modify_insns (false);
	    }
	  else
	    log_msg ("  modifying anyway\n");
	}

      log_msg ("\n\n");
    }

  log_msg ("\nupdating sequence insns\n");
  for (std::list<access_sequence>::iterator as_it = sequences.begin ();
       as_it != sequences.end (); ++as_it)
    {
      access_sequence& as = *as_it;
      if (as.modify_insns ())
        {
          log_access_sequence (as, false);
          log_msg ("\n");
          as.update_insn_stream (m_options.allow_mem_addr_change_new_insns);
          log_msg ("\n\n");
        }
    }

  // Unfortunately, passes tend to access global variables to see if they
  // are supposed to actually execute.  Save those variables, set them
  // and restore them afterwards.
  int f0 = flag_rerun_cse_after_global_opts;
  int f1 = flag_rerun_cse_after_loop;
  int f2 = optimize;

  flag_rerun_cse_after_global_opts = 1;
  flag_rerun_cse_after_loop = 1;
  optimize = 2;

  // The CSE passes below don't pay attention to REG_INC notes when they
  // propagate/rename regs inside mems.  Thus we have to fix those up
  // or else wrong REG_INC notes will produce wrong code later on.
  bool recreate_reginc_notes = false;

  if (m_options.cse)
    {
      log_msg ("\nrunning CSE\n");
      std::auto_ptr<rtl_opt_pass> p (make_pass_cse (m_ctxt));
      p->execute (fun);
      recreate_reginc_notes = true;
    }
  if (m_options.cse2)
    {
      log_msg ("\nrunning CSE2\n");
      std::auto_ptr<rtl_opt_pass> p (make_pass_cse2 (m_ctxt));
      p->execute (fun);
      recreate_reginc_notes = true;
    }
  if (m_options.gcse)
    {
      log_msg ("\nrunning GCSE\n");
      std::auto_ptr<rtl_opt_pass> p (make_pass_cse_after_global_opts (m_ctxt));
      p->execute (fun);
      recreate_reginc_notes = true;
    }

  flag_rerun_cse_after_global_opts = f0;
  flag_rerun_cse_after_loop = f1;
  optimize = f2;

  if (recreate_reginc_notes)
    {
      log_msg ("recreating reg inc notes after CSE\n");
      basic_block bb;
      FOR_EACH_BB_FN (bb, fun)
	{
	  rtx_insn* i;

	  FOR_BB_INSNS (bb, i)
	    {
	      if (!INSN_P (i) || !NONDEBUG_INSN_P (i))
	        continue;

	      remove_incdec_notes (i);
	      sh_check_add_incdec_notes (i);
	    }
	}
    }

  log_return (0, "\n\n");
}
