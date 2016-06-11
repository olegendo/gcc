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

#include "sh_ams2.h"

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
log_options (const sh_ams2::options& opt)
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
  if (x == sh_ams2::invalid_regno)
    log_msg ("(nil)");
  else if (x == sh_ams2::any_regno)
    log_msg ("(reg:%s *)", GET_MODE_NAME (Pmode));
  else
    log_rtx (x);
}

void
log_addr_expr (const sh_ams2::addr_expr& ae)
{
  if (dump_file == NULL)
    return;

  if (ae.is_invalid ())
    {
      log_msg ("(invalid)");
      return;
    }

  if (ae.type () == sh_ams2::pre_mod)
    {
      log_msg ("@( += %"PRId64, ae.disp ());
      log_reg (ae.base_reg ());
      log_msg (" )");
      return;
    }

  if (ae.type () == sh_ams2::post_mod)
    {
      log_msg ("@( ");
      log_reg (ae.base_reg ());
      log_msg (" += %"PRId64 " )", ae.disp ());
      return;
    }

  if (ae.type () == sh_ams2::non_mod)
    {
      log_msg ("@( ");

      log_reg (ae.base_reg ());

      if (ae.index_reg () != sh_ams2::invalid_regno)
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
log_sequence_element_location (const sh_ams2::sequence_element& e)
{
  if (e.insn () != NULL)
    log_msg ("at insn %d [bb %d]", INSN_UID (e.insn ()),
				   BLOCK_FOR_INSN (e.insn ())->index);
  else
    log_msg ("at insn: ?");
}

void
log_sequence_element (const sh_ams2::sequence_element& e,
                      bool log_alternatives = true,
                      bool log_dependencies = false)
{
  if (dump_file == NULL)
    return;

  if (e.type () == sh_ams2::type_mem_load)
    log_msg ("mem_load ");
  else if (e.type () == sh_ams2::type_mem_store)
    log_msg ("mem_store ");
  else if (e.type () == sh_ams2::type_mem_operand)
    log_msg ("mem_operand ");
  else if (e.type () == sh_ams2::type_reg_mod)
    log_msg ("reg_mod ");
  else if (e.type () == sh_ams2::type_reg_barrier)
    log_msg ("reg_barrier ");
  else if (e.type () == sh_ams2::type_reg_use)
    log_msg ("reg_use ");
  else
    gcc_unreachable ();

  log_sequence_element_location (e);

  if (e.is_mem_access ())
    {
      const sh_ams2::mem_access& m = (const sh_ams2::mem_access&)e;

      log_msg ("\n  current addr:   ");

      if (m.current_addr ().is_invalid ())
        {
          if (m.current_addr_rtx ())
            log_rtx (m.current_addr_rtx ());
          else
            log_msg ("unknown");
        }
      else
        log_addr_expr (m.current_addr ());

      if (!m.effective_addr ().is_invalid ())
        {
          log_msg ("\n  effective addr:  ");
          log_addr_expr (m.effective_addr ());
        }
    }
  else if (e.type () == sh_ams2::type_reg_mod)
    {
      const sh_ams2::reg_mod& rm = (const sh_ams2::reg_mod&)e;
      log_msg ("  set ");
      log_rtx (rm.reg ());
      log_msg ("\n  current addr:   ");

      if (rm.addr ().is_invalid ())
        {
          if (rm.value ())
            log_rtx (rm.value ());
          else
            log_msg ("unknown");
        }
      else
        log_addr_expr (rm.addr ());

      if (!rm.effective_addr ().is_invalid ())
        {
          log_msg ("\n  effective addr:  ");
          log_addr_expr (rm.effective_addr ());
        }
    }
  else if (e.type () == sh_ams2::type_reg_use)
    {
      const sh_ams2::reg_use& ru = (const sh_ams2::reg_use&)e;
      log_msg ("\n  use ");
      if (ru.reg_ref ())
        log_rtx (*ru.reg_ref ());
      else
        log_rtx (ru.reg ());
      log_msg ("\n  effective addr:   ");

      if (ru.effective_addr ().is_invalid ())
        log_msg ("unknown");
      else
        log_addr_expr (ru.effective_addr ());
      if (ru.reg_ref ())
        {
          log_msg ("\n  in insn\n");
          log_insn (ru.insn ());
        }
    }

  if (e.cost () == sh_ams2::infinite_costs)
    log_msg ("\n  cost: infinite");
  else
    log_msg ("\n  cost: %d", e.cost ());

  if (e.inc_chain ().length () > 1)
    log_msg ("\n  (inc chain pos: %d  length: %d)", e.inc_chain ().pos (),
						    e.inc_chain ().length ());
  if (e.dec_chain ().length () > 1)
    log_msg ("\n  (dec chain pos: %d  length: %d)", e.dec_chain ().pos (),
						    e.dec_chain ().length ());

  if (log_dependencies)
    {
      log_msg ("\n  use count: %ld\n", e.use_count ());
      if (!e.dependencies ().empty ())
        {
          log_msg ("\n  dependencies:\n");
          for (std::list<ref_counting_ptr<sh_ams2::sequence_element> >
               ::const_iterator it = e.dependencies ().begin ();
               it != e.dependencies ().end (); ++it)
            {
              log_sequence_element (*it->get (), log_alternatives, false);
              log_msg ("\n");
            }
          log_msg ("\n  ----\n");
        }
    }

  if (log_alternatives
      && (e.type () == sh_ams2::type_mem_load
          || e.type () == sh_ams2::type_mem_store
          || e.type () == sh_ams2::type_mem_operand))
    {
      const sh_ams2::mem_access& m = (const sh_ams2::mem_access&)e;

      log_msg ("\n  %d alternatives:\n", m.alternatives ().size ());
      int alt_count = 0;
      for (sh_ams2::alternative_set::const_iterator
		alt = m.alternatives ().begin ();
           alt != m.alternatives ().end (); ++alt)
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
log_sequence (const sh_ams2::sequence& seq, bool log_alternatives = true,
              bool log_dependencies = false)
{
  if (dump_file == NULL)
    return;

  log_msg ("=====\naccess sequence %p: %s\n\n", (const void*)&seq,
	   seq.elements ().empty () ? "is empty" : "");

  if (seq.elements ().empty ())
    return;

  for (sh_ams2::sequence_const_iterator it = seq.elements ().begin ();
       it != seq.elements ().end (); ++it)
    {
      log_sequence_element (**it, log_alternatives, log_dependencies);
      log_msg ("\n-----\n");
    }

  int c = seq.cost ();
  if (c == sh_ams2::infinite_costs)
    log_msg ("total cost: infinite");
  else
    log_msg ("total cost: %d", seq.cost ());
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

const pass_data sh_ams2::default_pass_data =
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

const rtx sh_ams2::invalid_regno = (const rtx)0;
const rtx sh_ams2::any_regno = (const rtx)1;

sh_ams2::sh_ams2 (gcc::context* ctx, const char* name, delegate& dlg,
		const options& opt)
: rtl_opt_pass (default_pass_data, ctx),
  m_delegate (dlg),
  m_options (opt)
{
  this->name = name;
}

sh_ams2::~sh_ams2 (void)
{
}

bool sh_ams2::gate (function* /*fun*/)
{
  return optimize > 0;
}

void sh_ams2::set_options (const options& opt)
{
  m_options = opt;
}

sh_ams2::options::options (void)
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

sh_ams2::options::options (const char* str)
{
  *this = options (std::string (str == NULL ? "" : str));
}

sh_ams2::options::options (const std::string& str)
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
sh_ams2::addr_expr::to_rtx (void) const
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
sh_ams2::addr_expr::set_base_reg (rtx val)
{
  if (val == m_base_reg)
    return;

  m_base_reg = val;
  m_cached_to_rtx = NULL;
}

void
sh_ams2::addr_expr::set_index_reg (rtx val)
{
  if (val == m_index_reg)
    return;

  m_index_reg = val;
  m_cached_to_rtx = NULL;
}

void
sh_ams2::addr_expr::set_disp (disp_t val)
{
  if (val == m_disp)
    return;

  m_disp = m_disp_min = m_disp_max = val;
  m_cached_to_rtx = NULL;
}

void
sh_ams2::addr_expr::set_scale (scale_t val)
{
  if (val == m_scale)
    return;

  m_scale = m_scale_min = m_scale_max = val;
  m_cached_to_rtx = NULL;
}

struct sh_ams2::element_to_optimize
{
  bool operator () (const sequence_element& el) const
  {
    return (el.type () == type_mem_load || el.type () == type_mem_store
            || el.type () == type_mem_operand
            || el.type () == type_reg_mod || el.type () == type_reg_use);
  }
};

// Get all sub-expressions that are contained inside the addr_expr.
// For an addr_expr of the form base+index*scale+disp, the following
// sub-expressions are returned:
//
// nothing -> represented with an invalid address
// base
// index
// index*scale
// base+index*scale
// disp
// base+disp
// index*scale+disp
// base+index*scale+disp
template <typename OutputIterator> void
sh_ams2::addr_expr::get_all_subterms (OutputIterator out) const
{
  *out++ = make_invalid_addr ();
  if (is_invalid ())
    return;

  if (has_disp ())
    *out++ = make_const_addr (disp ());
  if (has_index_reg ())
    {
      *out++ = make_reg_addr (index_reg ());
      if (scale () == 1)
        {
          if (has_disp ())
            *out++ = non_mod_addr (index_reg (), invalid_regno, 1, disp ());
        }
      else
        {
          *out++ = non_mod_addr (invalid_regno, index_reg (), scale (), 0);
          if (has_disp ())
            *out++ = non_mod_addr (invalid_regno, index_reg (), scale (), disp ());
        }
    }

  if (has_base_reg ())
    {
      *out++ = make_reg_addr (base_reg ());
      if (has_disp ())
        *out++ = non_mod_addr (base_reg (), invalid_regno, 1, disp ());

      if (has_index_reg ())
        {
          // If the index and base reg are interchangeable, put the one with
          // the smallest regno first.
          if (scale () == 1 && REGNO (index_reg ())  < REGNO (base_reg ()))
            {
              *out++ = non_mod_addr (index_reg (), base_reg (), 1, 0);
              if (has_disp ())
                *out++ = non_mod_addr (index_reg (), base_reg (), 1, disp ());
            }
          else
            {
              *out++ = non_mod_addr (base_reg (), index_reg (), scale (), 0);
              if (has_disp ())
                *out++ = non_mod_addr (base_reg (), index_reg (), scale (), disp ());
            }
        }
    }
}

void
sh_ams2::sequence_element::add_dependency (sh_ams2::sequence_element* dep)
{
  for (std::list<ref_counting_ptr<sequence_element> >::iterator it
         = m_dependencies.begin (); it != m_dependencies.end (); ++it)
    {
      if (elements_equal (dep, it->get ()))
        return;
    }
  m_dependencies.push_back (ref_counting_ptr<sequence_element> (dep));
}

const sh_ams2::adjacent_chain_info sh_ams2::sequence_element::g_no_incdec_chain;

// Add a reg mod for every insn that modifies an address register.
void
sh_ams2::sequence::find_addr_reg_mods (void)
{
  rtx prev_reg = NULL;
  rtx_insn* last_insn = BB_END (start_bb ());

  for (addr_reg_map::iterator it = m_addr_regs.begin ();
       it != m_addr_regs.end (); ++it)
    {
      rtx reg = it->first;
      if (regs_equal (reg, prev_reg))
        continue;

      while (last_insn != NULL)
        {
          std::pair<rtx, rtx_insn*> prev_val = find_reg_value (reg, last_insn);
          rtx value = prev_val.first;
          rtx_insn* mod_insn = prev_val.second;

          if (value != NULL_RTX && REG_P (value) && regs_equal (value, reg))
            break;

          addr_expr reg_current_addr
            = find_reg_note (mod_insn, REG_INC, NULL_RTX)
            ? make_reg_addr (reg) : rtx_to_addr_expr (value);
          sequence_iterator new_reg_mod
            = insert_element (new reg_mod (mod_insn, reg, value,
                                           reg_current_addr));
          addr_expr reg_effective_addr = rtx_to_addr_expr (value, Pmode,
                                                           this, *new_reg_mod);
          ((reg_mod*)*new_reg_mod)->set_effective_addr (reg_effective_addr);

          last_insn = prev_nonnote_insn_bb (mod_insn);
        }
    }
}

// Add a reg use for every use of an address register that's not a
// memory access or address reg modification.
void
sh_ams2::sequence::find_addr_reg_uses (void)
{
  std::set<rtx, cmp_by_regno> visited_addr_regs;
  std::map<rtx, reg_mod*, cmp_by_regno> live_addr_regs;
  std::vector<rtx*> reg_use_refs;
  rtx_insn* last_el_insn = NULL;

  for (rtx_insn* i = start_insn (); i != NULL_RTX; i = next_nonnote_insn_bb (i))
    {
      // Search for reg uses only if the insn doesn't contain any
      // mem accesses or reg mods.
      std::pair<insn_map::iterator, insn_map::iterator>
        els_in_insn = elements_in_insn (i);

      if (els_in_insn.first == els_in_insn.second)
        {
          for (std::set<rtx, cmp_by_regno>::iterator
                 regs = visited_addr_regs.begin ();
               regs !=  visited_addr_regs.end (); ++regs)
            {
              // Check if the reg is used in this insn.
              if (reg_overlap_mentioned_p (*regs, PATTERN (i))
                  || (CALL_P (i) && find_reg_fusage (i, USE, *regs)))
                {
                  // If so, find all references to the reg in this insn.
                  reg_use_refs.clear ();
                  find_addr_reg_uses_1 (*regs, PATTERN (i),
                                        std::back_inserter (reg_use_refs));

                  // If no refs were found, an unspecified reg use will be
                  // created.
                  if (reg_use_refs.empty ())
                    reg_use_refs.push_back (NULL);

                  // Create a reg use for each reference that was found.
                  for (std::vector<rtx*>::iterator it = reg_use_refs.begin ();
                       it != reg_use_refs.end (); ++it)
                    {
                      rtx* use_ref = *it;
                      reg_use* new_reg_use = (reg_use*)*insert_element (
                        new reg_use (i, *regs, use_ref));
                      addr_expr effective_addr
                        = rtx_to_addr_expr (*regs, Pmode, this, new_reg_use);

                      // If the use ref also contains a constant displacement,
                      // add that to the effective address.
                      if (!effective_addr.is_invalid () && use_ref
                          && (UNARY_P (*use_ref) || ARITHMETIC_P (*use_ref)))
                        {
                          addr_expr use_expr = rtx_to_addr_expr (*use_ref);
                          effective_addr = check_make_non_mod_addr (
                            effective_addr.base_reg (),
                            effective_addr.index_reg (),
                            effective_addr.scale (),
                            effective_addr.disp () + use_expr.disp ());
                        }
                      new_reg_use->set_effective_addr (effective_addr);

                      last_el_insn = new_reg_use->insn ();
                    }
                }
            }
        }

      // Update the visited and live address regs list.
      for (insn_map::iterator els = els_in_insn.first;
           els != els_in_insn.second; ++els)
        {
          if ((*els->second)->type () == type_reg_mod)
            {
              reg_mod* rm = (reg_mod*)*els->second;
              visited_addr_regs.insert (rm->reg ());
              live_addr_regs[rm->reg ()] = rm;
            }
          last_el_insn = (*els->second)->insn ();
        }
      for (std::map<rtx, reg_mod*, cmp_by_regno>::iterator it
             = live_addr_regs.begin (); it != live_addr_regs.end ();)
        {
          if (find_reg_note (i, REG_DEAD, it->first))
            live_addr_regs.erase (it++);
          else
            ++it;
        }
    }

  // Add unspecified reg uses for regs that are still alive at the
  // end of the sequence.
  for (std::map<rtx, reg_mod*, cmp_by_regno>::iterator it
         = live_addr_regs.begin (); it != live_addr_regs.end (); ++it)
    {
      rtx reg = it->first;
      reg_mod* rm = it->second;
      reg_use* new_reg_use = (reg_use*)*insert_element (
        new reg_use (last_el_insn, reg, NULL));
      new_reg_use->set_effective_addr (rm->effective_addr ());
      new_reg_use->add_dependency (rm);
    }
}

// The recursive part of find_addr_reg_uses. Find all references to REG
// in X and add them to OUT.
template <typename OutputIterator> void
sh_ams2::sequence::find_addr_reg_uses_1 (rtx reg, rtx& x, OutputIterator out)
{
  switch (GET_CODE (x))
    {
    case REG:
      if (regs_equal (reg, x))
          *out++ = &x;
      break;

    case PARALLEL:
      for (int i = 0; i < XVECLEN (x, 0); i++)
	find_addr_reg_uses_1 (reg, XVECEXP (x, 0, i), out);
      break;

    case SET:
      find_addr_reg_uses_1 (reg, SET_SRC (x), out);
      break;

    default:
      if (UNARY_P (x) || ARITHMETIC_P (x))
        {
          // If the reg is inside a (plus reg (const_int ...)) rtx,
          // add the whole rtx instead of just the reg.
          addr_expr use_expr = rtx_to_addr_expr (x);
          if (!use_expr.is_invalid () && use_expr.has_no_index_reg ()
              && use_expr.has_base_reg () && use_expr.has_disp ()
              && regs_equal (reg, use_expr.base_reg ()))
            {
              *out++ = &x;
              break;
            }

	  for (int i = 0; i < GET_RTX_LENGTH (GET_CODE (x)); i++)
	    find_addr_reg_uses_1 (reg, XEXP (x, i), out);
        }
      break;
    }
}

// The basic block of the first insn in the access sequence.
basic_block
sh_ams2::sequence::start_bb (void) const
{
  for (sequence_const_iterator e = elements ().begin ();
       e != elements ().end (); ++e)
    {
      if ((*e)->insn () && BLOCK_FOR_INSN ((*e)->insn ()))
        return BLOCK_FOR_INSN ((*e)->insn ());
    }
  gcc_unreachable ();
}

// The first insn in the access sequence.
rtx_insn*
sh_ams2::sequence::start_insn (void) const
{
  for (sequence_const_iterator e = elements ().begin ();
       e != elements ().end (); ++e)
    {
      if ((*e)->insn ())
        return (*e)->insn ();
    }
  gcc_unreachable ();
}

// Insert a new element into the sequence.  Return an iterator pointing
// to the newly inserted element.
sh_ams2::sequence_iterator
sh_ams2::sequence::insert_element (sh_ams2::sequence_element* el,
                                   sh_ams2::sequence_iterator insert_before)
{
  sequence_iterator iter = elements ().insert (insert_before, el);

  // Update the insn -> element map.
  if (el->insn ())
      m_insn_el_map.insert (std::make_pair (el->insn (), iter));

  // Update the address reg list.
  if (el->type () == type_reg_mod)
      m_addr_regs.insert (std::make_pair (((reg_mod*)el)->reg (), iter));

  return iter;
}

// Same as the previous function, except that the place of the element
// is determined by its insn and no duplicates are allowed.
// If the element has a duplicate already in the sequence, return an
// iterator to the duplicate and delete the original one.
sh_ams2::sequence_iterator
sh_ams2::sequence::insert_element (sh_ams2::sequence_element* el)
{
  if (elements ().empty ())
    return insert_element (el, elements ().end ());

  // Elements without an insn go to the sequence's start.
  if (!el->insn ())
    {
      // Check for duplicates.
      for (sequence_iterator els = elements ().begin ();
           els != elements ().end () && !(*els)->insn (); ++els)
        {
          if (elements_equal (el, *els))
            {
              delete el;
              return els;
            }
        }

      return insert_element (el, elements ().begin ());
    }

  if (!elements ().back ()->insn ())
      return insert_element (el, elements ().end ());

  // If the sequence element's insn contains other elements, insert
  // the element after them.
  std::pair<insn_map::iterator, insn_map::iterator>
    els_in_insn = elements_in_insn (el->insn ());

  if (els_in_insn.first != els_in_insn.second)
    {
      // Check for duplicates.
      for (insn_map::iterator els = els_in_insn.first;
           els != els_in_insn.second; ++els)
        {
          if (elements_equal (el, *els->second))
            {
              delete el;
              return els->second;
            }

        }

      for (insn_map::iterator els = els_in_insn.first;
           els != els_in_insn.second; ++els)
        {
          sequence_iterator insert_after = els->second;
          if (stdx::next(insert_after) == elements ().end ()
              || (*stdx::next (insert_after))->insn ()
                != (*insert_after)->insn ())
            return insert_element (el, stdx::next (insert_after));
        }
    }

  // Otherwise, insert it before the next insn's elements.
  for (rtx_insn* i = NEXT_INSN (el->insn ()); ; i = NEXT_INSN (i))
    {
      els_in_insn = elements_in_insn (i);
      if (els_in_insn.first == els_in_insn.second)
        {
          // If there are no elements after this insn, insert it to the
          // sequence's end.
          if (i == NULL)
            return insert_element (el, elements ().end ());
          continue;
        }


      for (insn_map::iterator els = els_in_insn.first;
           els != els_in_insn.second; ++els)
        {
          sequence_iterator insert_before = els->second;
          if (insert_before == elements ().begin ()
              || (*stdx::prev (insert_before))->insn ()
                != (*insert_before)->insn ())
            return insert_element (el, insert_before);
        }
      gcc_unreachable ();
    }

  gcc_unreachable ();
}

// Remove an element from the sequence.  Return an iterator pointing
// to the next element.
sh_ams2::sequence_iterator
sh_ams2::sequence::remove_element (sh_ams2::sequence_iterator el)
{
  // Update the insn -> element map.
  if ((*el)->insn ())
    {
      std::pair<insn_map::iterator, insn_map::iterator> range
        = m_insn_el_map.equal_range ((*el)->insn ());
      for (insn_map::iterator it = range.first; it != range.second; ++it)
        {
          if (it->second == el)
            {
              m_insn_el_map.erase (it);
              break;
            }
        }
    }

  // Update the address reg list.
  if ((*el)->type () == type_reg_mod)
    {
      std::pair<addr_reg_map::iterator, addr_reg_map::iterator> range
        = m_addr_regs.equal_range (((reg_mod*)*el)->reg ());
      for (addr_reg_map::iterator it = range.first; it != range.second; ++it)
        {
          if (it->second == el)
            {
              m_addr_regs.erase (it);
              break;
            }
        }
    }

  return elements ().erase (el);
}

// The total cost of the accesses in the sequence.
int
sh_ams2::sequence::cost (void) const
{
  int cost = 0;
  for (sequence_const_iterator els = elements ().begin ();
       els != elements ().end () && cost != infinite_costs; ++els)
    cost += (*els)->cost ();
  return cost;
}

// Find the value that REG was last set to, starting the search from
// START_INSN.  Return that value along with the insn in which REG gets
// modified.  If the value of REG cannot be determined, return NULL.
// If REG didn't get modified, return the REG itself.
std::pair<rtx, rtx_insn*>
sh_ams2::sequence::find_reg_value (rtx reg, rtx_insn* start_insn)
{
  std::vector<mem_access*> mems;

  // Go back through the insn list until we find the last instruction
  // that modified the register.
  rtx_insn* i;
  for (i = start_insn; i != NULL_RTX; i = prev_nonnote_insn_bb (i))
    {
      if (BARRIER_P (i))
	return std::make_pair (NULL_RTX, i);
      if (!INSN_P (i) || DEBUG_INSN_P (i))
	continue;
      if (reg_set_p (reg, i) && CALL_P (i))
	return std::make_pair (NULL_RTX, i);

      std::pair<rtx, bool> r = find_reg_value_1 (reg, i);
      if (!r.second)
        continue;

      if (r.first == NULL)
        {
          if (find_regno_note (i, REG_INC, REGNO (reg)) != NULL)
            {

              // Search for auto-mod memory accesses in the current
              // insn that modify REG.
              std::pair<insn_map::iterator, insn_map::iterator>
                els_in_insn = elements_in_insn (i);
              for (insn_map::iterator els = els_in_insn.first;
                   els != els_in_insn.second; ++els)
                {
                  if (!(*els->second)->is_mem_access ())
                    continue;

                  mem_access* acc = (mem_access*)*els->second;
                  rtx mem_addr = acc->current_addr_rtx ();
                  rtx_code code = GET_CODE (mem_addr);

                  if (GET_RTX_CLASS (code) == RTX_AUTOINC
                      && REG_P (XEXP (mem_addr, 0))
                      && regs_equal (XEXP (mem_addr, 0), reg))
                    return std::make_pair (mem_addr, i);
                }
              gcc_unreachable ();
            }
          else
            {
              // The reg is modified in some unspecified way, e.g. a clobber.
              return std::make_pair (NULL_RTX, i);
            }
        }
      else
        {
          if (GET_CODE (r.first) == SET)
            return std::make_pair (SET_SRC (r.first), i);
          else
            return std::make_pair (NULL_RTX, i);
        }
    }

  return std::make_pair (reg, i);
}

// The recursive part of find_reg_value. If REG is modified in INSN,
// return true and the SET pattern that modifies it. Otherwise, return
// false.
std::pair<rtx, bool>
sh_ams2::sequence::find_reg_value_1 (rtx reg, const_rtx insn)
{
  if (INSN_P (insn) && GET_CODE (PATTERN (insn)) == SEQUENCE)
    {
      for (int i = 0; i < XVECLEN (PATTERN (insn), 0); ++i)
        {
          std::pair<rtx, bool> r =
                        find_reg_value_1 (reg, XVECEXP (PATTERN (insn), 0, i));
          if (r.second)
            return r;
        }
      return std::make_pair (NULL_RTX, false);
    }

  if (INSN_P (insn)
      && (FIND_REG_INC_NOTE (insn, reg)
          || (CALL_P (insn)
              && ((REG_P (reg)
                   && REGNO (reg) < FIRST_PSEUDO_REGISTER
                   && overlaps_hard_reg_set_p (regs_invalidated_by_call,
                                               GET_MODE (reg), REGNO (reg)))
                  || find_reg_fusage (insn, CLOBBER, reg)))))
    return std::make_pair (NULL_RTX, true);

  rtx r = const_cast<rtx> (set_of (reg, insn));
  return std::make_pair (r, r != NULL);
}

// TODO: Implement these functions.  For now, they are defined as empty
// functions to avoid undefined references.
bool sh_ams2::
mem_load::try_replace_addr (const sh_ams2::addr_expr& new_addr) { return true; }
bool sh_ams2::
mem_load::replace_addr (const sh_ams2::addr_expr& new_addr) { return true; }
bool sh_ams2::
mem_load::try_replace_addr_rtx (const sh_ams2::addr_expr& new_addr) { return true; }
bool sh_ams2::
mem_load::replace_addr_rtx (const sh_ams2::addr_expr& new_addr) { return true; }

bool
sh_ams2::mem_store::try_replace_addr (const sh_ams2::addr_expr& new_addr) { return true; }
bool sh_ams2::mem_store::replace_addr (const sh_ams2::addr_expr& new_addr) { return true; }
bool sh_ams2::
mem_store::try_replace_addr_rtx (const sh_ams2::addr_expr& new_addr) { return true; }
bool sh_ams2::
mem_store::replace_addr_rtx (const sh_ams2::addr_expr& new_addr) { return true; }

bool sh_ams2::
mem_operand::try_replace_addr (const sh_ams2::addr_expr& new_addr) { return true; }
bool sh_ams2::
mem_operand::replace_addr (const sh_ams2::addr_expr& new_addr) { return true; }
bool sh_ams2::
mem_operand::try_replace_addr_rtx (const sh_ams2::addr_expr& new_addr) { return true; }
bool sh_ams2::
mem_operand::replace_addr_rtx (const sh_ams2::addr_expr& new_addr) { return true; }

// Check whether two sequence elements are duplicates.
bool
sh_ams2::elements_equal (const sequence_element* el1,
                         const sequence_element* el2)
{
  if (el1->type () != el2->type ())
    return false;

  if (el1->is_mem_access ())
    {
      const mem_access* m1 = (const mem_access*)el1;
      const mem_access* m2 = (const mem_access*)el2;
      return m1->effective_addr () == m2->effective_addr ()
        && m1->current_addr_rtx () == m2->current_addr_rtx ()
        && m1->current_addr () == m2->current_addr ();
    }

  if (el1->type () == type_reg_mod)
    {
      const reg_mod* rm1 = (const reg_mod*)el1;
      const reg_mod* rm2 = (const reg_mod*)el2;
      return regs_equal (rm1->reg (), rm2->reg ())
        && rm1->value () == rm2->value ()
        && rm1->addr () == rm2->addr ();
    }

  if (el1->type () == type_reg_barrier)
    return regs_equal (((const reg_barrier*)el1)->reg (),
                       ((const reg_barrier*)el2)->reg ());

  if (el1->type () == type_reg_use)
    {
      const reg_use* ru1 = (const reg_use*)el1;
      const reg_use* ru2 = (const reg_use*)el2;
      return regs_equal (ru1->reg (), ru2->reg ());
    }

  gcc_unreachable ();
}

// Return a non_mod_addr if it can be created with the given scale and
// displacement.  Otherwise, return an invalid address.
sh_ams2::addr_expr
sh_ams2::check_make_non_mod_addr (rtx base_reg, rtx index_reg,
                                  HOST_WIDE_INT scale, HOST_WIDE_INT disp)
{
  if (((base_reg || index_reg)
       && sext_hwi (disp, GET_MODE_PRECISION (Pmode)) != disp)
      || sext_hwi (scale, GET_MODE_PRECISION (Pmode)) != scale)
    return make_invalid_addr ();

  return non_mod_addr (base_reg, index_reg, scale, disp);
}

// Extract an addr_expr of the form (base_reg + index_reg * scale + disp)
// from the rtx X.
// If SEQ and EL is not null, trace back the effective addresses of the
// registers in X (starting from EL) and insert a reg mod into the sequence
// for every address modifying insn that was used.
sh_ams2::addr_expr
sh_ams2::rtx_to_addr_expr (rtx x, machine_mode mem_mach_mode,
                           sh_ams2::sequence* seq,
                           sh_ams2::sequence_element* el)
{
  const bool trace_back_addr = (seq != NULL && el != NULL);

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
      op0 = rtx_to_addr_expr (XEXP (x, 0), mem_mach_mode, seq, el);
      op1 = rtx_to_addr_expr (XEXP (x, 1), mem_mach_mode, seq, el);
      if (op0.is_invalid () || op1.is_invalid ())
        return make_invalid_addr ();
    }
  else if (code == NEG)
    {
      op1 = rtx_to_addr_expr (XEXP (x, 0), mem_mach_mode, seq, el);
      if (op1.is_invalid ())
        return op1;
    }

  else if (GET_RTX_CLASS (code) == RTX_AUTOINC)
    {
      addr_type_t mod_type;
      bool apply_post_disp = (!trace_back_addr || !el->is_mem_access ());

      switch (code)
        {
        case POST_DEC:
          disp = apply_post_disp ? -GET_MODE_SIZE (mem_mach_mode) : 0;
          mod_type = post_mod;
          break;
        case POST_INC:
          disp = apply_post_disp ? GET_MODE_SIZE (mem_mach_mode) : 0;
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
            addr_expr a = rtx_to_addr_expr (XEXP (x, apply_post_disp ? 1 : 0),
                                            mem_mach_mode, seq, el);
            if (a.is_invalid ())
              return make_invalid_addr ();
            return post_mod_addr (a.base_reg (), a.disp ());
          }
        case PRE_MODIFY:
          {
            addr_expr a = rtx_to_addr_expr (XEXP (x, 1), mem_mach_mode,
                                            seq, el);
            if (a.is_invalid ())
              return make_invalid_addr ();
            return pre_mod_addr (a.base_reg (), a.disp ());
          }

        default:
          return make_invalid_addr ();
        }

      op1 = rtx_to_addr_expr (XEXP (x, 0), mem_mach_mode, seq, el);
      if (op1.is_invalid ())
        return op1;

      disp += op1.disp ();

      if (trace_back_addr)
        return non_mod_addr (op1.base_reg (), op1.index_reg (),
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
      if (trace_back_addr)
        {
          // Find the expression that the register was last set to
          // and convert it to an addr_expr.
          std::pair<rtx, rtx_insn*> prev_val
            = seq->find_reg_value (x, prev_nonnote_insn_bb (el->insn ()));
          rtx value = prev_val.first;
          rtx_insn* mod_insn = prev_val.second;

          // Stop expanding the reg if the reg can't be expanded any further.
          if (value != NULL_RTX && REG_P (value) && regs_equal (value, x))
            {
              // Add to the sequence's start a reg mod that sets the reg
              // to itself. This will be used by the address modification
              // generator as a starting address.
              sequence_iterator new_reg_mod
                = seq->insert_element (new reg_mod (NULL, x, x));
              el->add_dependency (*new_reg_mod);

              return make_reg_addr (x);
            }

          addr_expr reg_current_addr
            = find_reg_note (mod_insn, REG_INC, NULL_RTX)
            ? make_reg_addr (x)
            : rtx_to_addr_expr (value, mem_mach_mode);

          // Insert the modifying insn into the sequence as a reg mod.
          sequence_iterator new_reg_mod
            = seq->insert_element (new reg_mod (mod_insn, x, value,
                                                reg_current_addr));
          el->add_dependency (*new_reg_mod);

          // Expand the register's value further.
          addr_expr reg_effective_addr = rtx_to_addr_expr (
            value, mem_mach_mode, seq, *new_reg_mod);

          ((reg_mod*)*new_reg_mod)->set_effective_addr (reg_effective_addr);

          // If the expression is something AMS can't handle, use the original
          // reg instead.
          if (reg_effective_addr.is_invalid ()
              || reg_current_addr.is_invalid ())
            return make_reg_addr (x);

          return reg_effective_addr;
        }
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

// Find the memory accesses in the rtx X of the insn I and add them to OUT.
// TYPE indicates the type of the next mem that we find (i.e. mem_load,
// mem_store or mem_operand).
template <typename OutputIterator> void
sh_ams2::find_mem_accesses (rtx_insn* i, rtx& x, OutputIterator out,
                            sh_ams2::element_type type)
{
  switch (GET_CODE (x))
    {
    case MEM:
      mem_access* acc;

      switch (type)
        {
        case type_mem_load:
          acc = new mem_load (i, GET_MODE (x));
          break;
        case type_mem_store:
          acc = new mem_store (i, GET_MODE (x));
          break;
        case type_mem_operand:
          acc = new mem_operand (i, GET_MODE (x));
          break;
        default:
          gcc_unreachable ();
        }
      acc->set_current_addr_rtx (XEXP (x, 0));
      rtx_to_addr_expr (XEXP (x, 0), GET_MODE (x));
      acc->set_current_addr (rtx_to_addr_expr (XEXP (x, 0), GET_MODE (x)));
      *out++ = acc;
      break;

    case PARALLEL:
      for (int j = 0; j < XVECLEN (x, 0); j++)
        find_mem_accesses (i, XVECEXP (x, 0, j), out, type);
      break;

    case SET:
      find_mem_accesses (i, SET_DEST (x), out, type_mem_store);
      find_mem_accesses (i, SET_SRC (x), out, type_mem_load);
      break;

    case CALL:
      find_mem_accesses (i, XEXP (x, 0), out, type_mem_load);
      break;

    default:
      if (UNARY_P (x) || ARITHMETIC_P (x))
        {
          for (int j = 0; j < GET_RTX_LENGTH (GET_CODE (x)); j++)
            find_mem_accesses (i, XEXP (x, j), out, type);
        }
      break;
    }
}

unsigned int
sh_ams2::execute (function* fun)
{
  log_msg ("sh-ams pass (WIP)\n");
  log_options (m_options);
  log_msg ("\n\n");

//  df_set_flags (DF_DEFER_INSN_RESCAN); // needed?

  df_note_add_problem ();
  df_analyze ();

  std::list<sequence> sequences;
  std::vector<mem_access*> mems;

  log_msg ("extracting access sequences\n");
  basic_block bb;
  FOR_EACH_BB_FN (bb, fun)
    {
      rtx_insn* i;

      log_msg ("BB #%d:\n", bb->index);
      log_msg ("finding mem accesses\n");

      // Create a new sequence from the mem accesses in this BB.
      sequences.push_back (sequence ());
      sequence& seq = sequences.back ();

      FOR_BB_INSNS (bb, i)
        {
          if (!INSN_P (i) || !NONDEBUG_INSN_P (i))
            continue;

          // Search for memory accesses inside the current insn
          // and add them to the address sequence.
          mems.clear ();
          find_mem_accesses (i, PATTERN (i), std::back_inserter (mems));

          for (std::vector<mem_access*>::iterator m = mems.begin ();
               m != mems.end (); ++m)
            {
              seq.insert_element (*m, seq.elements ().end ());
              (*m)->set_effective_addr (rtx_to_addr_expr (
                                        (*m)->current_addr_rtx (),
                                        (*m)->mach_mode (), &seq, (*m)));
            }
         }
    }

  log_msg ("\nprocessing extracted sequences\n");
  for (std::list<sequence>::iterator it = sequences.begin ();
       it != sequences.end (); ++it)
    {
      sequence& seq = *it;

      if (seq.elements ().empty ())
        continue;

      log_msg ("find_addr_reg_mods\n");
      seq.find_addr_reg_mods ();

      log_sequence (seq, false);
      log_msg ("\n\n");

      log_msg ("find_addr_reg_uses\n");
      seq.find_addr_reg_uses ();

      log_sequence (seq, false, true);
      log_msg ("\n\n");
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
