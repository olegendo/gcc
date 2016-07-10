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

      if (!m.optimization_enabled ())
        log_msg ("\n  (won't be optimized)");
    }
  else if (e.type () == sh_ams2::type_reg_mod)
    {
      const sh_ams2::reg_mod& rm = (const sh_ams2::reg_mod&)e;
      log_msg ("  set ");
      log_rtx (rm.reg ());
      log_msg ("\n  current addr:   ");

      if (rm.current_addr ().is_invalid ())
        {
          if (rm.value ())
            log_rtx (rm.value ());
          else
            log_msg ("unknown");
        }
      else
        log_addr_expr (rm.current_addr ());

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
      log_rtx (ru.reg ());
      if (ru.reg_ref ())
        {
          log_msg ("in expr\n");
          log_rtx (*ru.reg_ref ());
        }

      log_msg ("\n  effective addr:   ");
      if (ru.effective_addr ().is_invalid ())
        log_msg ("unknown");
      else
        log_addr_expr (ru.effective_addr ());
      if (!ru.optimization_enabled ())
        log_msg ("\n  (won't be optimized)");
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
      if (!e.dependencies ().empty ())
        {
          log_msg ("\n  dependencies:\n");
          for (std::list<sh_ams2::sequence_element*>::const_iterator it =
                 e.dependencies ().begin ();
               it != e.dependencies ().end (); ++it)
            {
              log_sequence_element (**it, log_alternatives, false);
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

template <typename Container> struct element_is_in_func
{
  const Container& container;

  element_is_in_func (const Container& c) : container (c) { }

  bool operator () (typename Container::const_reference val) const
  {
    return std::find (container.begin (), container.end (), val)
	   != container.end ();
  }
};

template <typename T> struct element_is_in_func<std::set<T> >
{
  const std::set<T>& container;

  element_is_in_func (const std::set<T>& c) : container (c) { }

  bool operator () (typename std::set<T>::const_reference val) const
  {
    return container.find (val) != container.end ();
  }
};

template <typename Container> element_is_in_func<Container>
element_is_in (const Container& c)
{
  return element_is_in_func<Container> (c);
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
  get_int_opt (allow_mem_addr_change_new_insns);
  get_int_opt (gcse);

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
  bool operator () (const ref_counting_ptr<sequence_element>& el) const
  {
    return ((el->is_mem_access () || el->type () == type_reg_use)
            && el->optimization_enabled ());
  }
};

struct sh_ams2::alternative_valid
{
  bool operator () (const alternative& a) const { return a.valid (); }
};

struct sh_ams2::alternative_invalid
{
  bool operator () (const alternative& a) const { return !a.valid (); }
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
  if (std::find_if (m_dependencies.begin (), m_dependencies.end (),
		    sequence_element::equals (dep)) == m_dependencies.end ())
    m_dependencies.push_back (dep);
}
void
sh_ams2::sequence_element::remove_dependency (sh_ams2::sequence_element* dep)
{
  m_dependencies.remove_if (sequence_element::equals (dep));
}

void
sh_ams2::sequence_element::add_dependent_el (sh_ams2::sequence_element* dep)
{
  if (std::find_if (m_dependent_els.begin (), m_dependent_els.end (),
		    sequence_element::equals (dep)) == m_dependent_els.end ())
    m_dependent_els.push_back (dep);
}
void
sh_ams2::sequence_element::remove_dependent_el (sh_ams2::sequence_element* dep)
{
  m_dependencies.remove_if (sequence_element::equals (dep));
}

// Return true if the element is used (directly or indirectly) by
// another element that cannot be optimized.
bool
sh_ams2::sequence_element::used_by_unoptimizable_el (void) const
{
  for (std::list<sequence_element*>::const_iterator it
         = m_dependent_els.begin (); it != m_dependent_els.end (); ++it)
    {
      if (!(*it)->optimization_enabled ()
          || (*it)->effective_addr ().is_invalid ()
          || (*it)->used_by_unoptimizable_el ())
        return true;
    }
  return false;
}

// Return true if the effective address of FIRST and SECOND only differs in
// the constant displacement and the difference is DIFF.
bool
sh_ams2::sequence_element::distance_equals (
  const ref_counting_ptr<sequence_element>& first,
  const ref_counting_ptr<sequence_element>& second,
  disp_t diff)
{
  if (!first->is_mem_access () || (!second->is_mem_access ()
                                   && second->type () != type_reg_use))
    return false;
  if (first->effective_addr ().is_invalid ()
      || second->effective_addr ().is_invalid ())
    return false;

  std::pair<disp_t, bool> distance
    = second->effective_addr () - first->effective_addr ();
  return distance.second && distance.first == diff;
}

// Return true if the effective address of FIRST and SECOND only differs in
// the constant displacement and the difference is the access size of FIRST.
bool
sh_ams2::sequence_element::adjacent_inc (
  const ref_counting_ptr<sequence_element>& first,
  const ref_counting_ptr<sequence_element>& second)
{
  if (!first->is_mem_access ())
    return false;

  return distance_equals (first, second,
                          ((const mem_access*)first.get ())->access_size ());
}

bool
sh_ams2::sequence_element::not_adjacent_inc (
  const ref_counting_ptr<sequence_element>& first,
  const ref_counting_ptr<sequence_element>& second)
{
  return !adjacent_inc (first, second);
}

// Same as adjacent_inc, except that the displacement of SECOND should
// be the smaller one.
bool
sh_ams2::sequence_element::adjacent_dec (
  const ref_counting_ptr<sequence_element>& first,
  const ref_counting_ptr<sequence_element>& second)
{
  if (!first->is_mem_access ())
    return false;

  return distance_equals (first, second,
                          -((const mem_access*)first.get ())->access_size ());
}

bool
sh_ams2::sequence_element::not_adjacent_dec (
  const ref_counting_ptr<sequence_element>& first,
  const ref_counting_ptr<sequence_element>& second)
{
  return !adjacent_dec (first, second);
}

void
sh_ams2::mem_access::update_cost (delegate& d ATTRIBUTE_UNUSED,
                                  sequence& seq ATTRIBUTE_UNUSED,
                                  sequence_iterator el_it ATTRIBUTE_UNUSED)
{
  if (!optimization_enabled () || effective_addr ().is_invalid ())
    {
      set_cost (0);
      return;
    }

  // Find the alternative that the access uses and update
  // its cost accordingly.
  // FIXME: When selecting an alternative, remember the alternative
  // iterator as the "currently selected alternative".  Then we don't
  // need to find it over and over again.
  for (alternative_set::const_iterator alt = alternatives ().begin (); ; ++alt)
    {
      if (matches_alternative (*alt))
        {
          set_cost (alt->cost ());
          return;
        }
    }
  gcc_unreachable ();
}

void
sh_ams2::reg_mod::update_cost (delegate& d, sequence& seq,
                               sequence_iterator el_it)
{
  if (current_addr ().is_invalid ())
    {
      set_cost (0);
      return;
    }

  int cost = 0;
  const addr_expr &ae = current_addr ();

  // Scaling costs
  if (ae.has_no_base_reg () && ae.has_index_reg () && ae.scale () != 1)
    cost += d.addr_reg_mod_cost (reg (),
                                 gen_rtx_MULT (Pmode,
                                               ae.index_reg (),
                                               GEN_INT (ae.scale ())),
                                 seq, el_it);

  // Costs for adding or subtracting another reg
  else if (ae.has_no_disp () && std::abs (ae.scale ()) == 1
           && ae.has_base_reg () && ae.has_index_reg ())
    cost += d.addr_reg_mod_cost (reg (),
                                 gen_rtx_PLUS (Pmode,
                                               ae.index_reg (),
                                               ae.base_reg ()),
                                 seq, el_it);

  // Constant displacement costs
  else if (ae.has_base_reg () && ae.has_no_index_reg ()
           && ae.has_disp ())
    cost += d.addr_reg_mod_cost (reg (),
                                 gen_rtx_PLUS (Pmode,
                                               ae.base_reg (),
                                               GEN_INT (ae.disp ())),
                                 seq, el_it);

  // Constant loading costs
  else if (ae.has_no_base_reg () && ae.has_no_index_reg ())
    cost += d.addr_reg_mod_cost (reg (),
                                 GEN_INT (ae.disp ()),
                                 seq, el_it);

  // If none of the previous branches were taken, the reg-mod
  // is a (reg <- reg) copy, and doesn't have any modification cost.
  else
    {
      gcc_assert (ae.has_base_reg () && ae.has_no_index_reg ()
                  && ae.has_no_disp ());
      cost = 0;
    }

  set_cost (cost);

  // Cloning costs:

  rtx reused_reg = NULL;

  if (current_addr ().has_base_reg ())
    reused_reg = current_addr ().base_reg ();
  else if (current_addr ().has_index_reg ())
    reused_reg = current_addr ().index_reg ();
  else
    return;

  // There's no cloning cost for reg-mods that set the reg to itself.
  if (regs_equal (reused_reg, reg ()))
    return;

  // Find the reg-mod of the reused register.
  reg_mod* reused_rm = NULL;
  for (std::list<sh_ams2::sequence_element*>::iterator it =
         dependencies ().begin (); it != dependencies ().end (); ++it)
    {
      if ((*it)->type () != type_reg_mod)
        continue;

      if (regs_equal (((reg_mod*)*it)->reg (), reused_reg))
        {
          reused_rm = (reg_mod*)*it;
          break;
        }
    }
  gcc_assert (reused_rm != NULL);

  // Find the first element that also uses the reused register.
  for (std::list<sh_ams2::sequence_element*>::iterator it =
         reused_rm->dependent_els ().begin ();
       it != reused_rm->dependent_els ().end (); ++it)
    {
      if ((*it)->type () != type_reg_mod)
        continue;

      if (((reg_mod*)*it)->current_addr ().is_invalid ())
        continue;

      rtx dep_reused_reg;
      if (((reg_mod*)*it)->current_addr ().has_base_reg ())
        dep_reused_reg = ((reg_mod*)*it)->current_addr ().base_reg ();
      else if (((reg_mod*)*it)->current_addr ().has_index_reg ())
        dep_reused_reg = ((reg_mod*)*it)->current_addr ().index_reg ();
      else
        continue;

      if (regs_equal (reused_reg, dep_reused_reg))
        {
          // If this reg-mod is the first to use the reg, there's
          // no need to clone it.
          if (*it == this)
              return;

          // Otherwise, we'll have to apply cloning costs.
          adjust_cost (d.addr_reg_clone_cost (reused_reg, seq, el_it));
          return;
        }
    }
  gcc_unreachable ();
}

const sh_ams2::adjacent_chain_info sh_ams2::sequence_element::g_no_incdec_chain;
bool sh_ams2::mem_access::allow_new_insns = true;

// Used to store information about newly created sequences during
// sequence splitting.
class sh_ams2::split_sequence_info
{
public:
  split_sequence_info (sequence* seq) : m_seq (seq), m_addr_regs () {}

  // The sequence itself.
  sequence* seq (void) const { return m_seq; }

  // Return true if REG is present in m_addr_regs.
  bool uses_addr_reg (rtx reg) const
  {
    return m_addr_regs.find (reg) != m_addr_regs.end ();
  }

  // Add REG to the address reg lists.
  void add_reg (rtx reg) { m_addr_regs.insert (reg); }

private:
  sequence *m_seq;

  // A set of the address registers used in the sequence.
  std::set<rtx, cmp_by_regno> m_addr_regs;
};

// Used to keep track of shared address (sub)expressions
// during sequence splitting.
class sh_ams2::shared_term
{
public:
  shared_term (addr_expr& t, sequence_element* el)
    : m_term (t), m_sharing_els (), m_new_seq (NULL) {
    m_sharing_els.push_back (el);
  }

  // The shared term.
  const addr_expr& term () { return m_term; }

  // The elements that share this term.
  std::vector<sequence_element*>& sharing_els () { return m_sharing_els; }

  // The term's newly created access sequence.
  split_sequence_info* new_seq (void) const { return m_new_seq; }
  void set_new_seq (split_sequence_info *s) {  m_new_seq = s; }

  static bool compare (shared_term* a, shared_term* b)
  { return a->score () > b->score (); }

  // A score that's used to determine which shared expressions should
  // be used for splitting access sequences.  A higher score means that
  // the shared term is more likely to be selected as a base for a
  // new sequence.
  unsigned int score (void) const
  {
    if (m_term.is_invalid ())
      return 0;

    unsigned int score = 10;

    // Displacement-only terms with large displacements are
    // represented with a constant 0 address.
    if (m_term.has_no_base_reg () && m_term.has_no_index_reg ()
        && m_term.has_no_disp ())
      score += 2;

    if (m_term.has_base_reg ())
      score += 2;
    if (m_term.has_index_reg ())
      {
        score += 2;
        if (m_term.scale () != 1)
          ++score;
      }
    if (m_term.has_disp ())
      ++score;

    return score*m_sharing_els.size ();
  }

private:
  addr_expr m_term;
  std::vector<sequence_element*> m_sharing_els;
  split_sequence_info* m_new_seq;
};

// Return all the start addresses that could be used to arrive at END_ADDR.
// FIXME: Avoid copying the list elements over and over.
template <typename OutputIterator> void
sh_ams2::start_addr_list::get_relevant_addresses (const addr_expr& end_addr,
                                                  OutputIterator out)
{
  // Constant displacements can always be used as start addresses.
  for (std::list<reg_mod*>::iterator it = m_const_addresses.begin ();
       it != m_const_addresses.end (); ++it)
    *out++ = *it;

  // Addresses containing registers might be used if they have a
  // register in common with the end address.
  typedef std::pair <reg_map::iterator, reg_map::iterator> matching_range_t;
  if (end_addr.has_base_reg ())
    {
      matching_range_t r = m_reg_addresses.equal_range (end_addr.base_reg ());
      for (matching_range_t::first_type it = r.first; it != r.second; ++it)
        *out++ = it->second;
    }
  if (end_addr.has_index_reg ())
    {
      matching_range_t r = m_reg_addresses.equal_range (end_addr.index_reg ());
      for (matching_range_t::first_type it = r.first; it != r.second; ++it)
        *out++ = it->second;
    }
}

// Add START_ADDR to the list of available start addresses.
void
sh_ams2::start_addr_list::add (reg_mod* start_addr)
{
  addr_expr addr = start_addr->effective_addr ().is_invalid ()
    ? make_reg_addr (start_addr->reg ()) : start_addr->effective_addr ();

  // If the address has a base or index reg, add it to M_REG_ADDRESSES.
  if (addr.has_base_reg ())
    m_reg_addresses.insert (std::make_pair (addr.base_reg (), start_addr));
  if (addr.has_index_reg ())
    m_reg_addresses.insert (std::make_pair (addr.index_reg (), start_addr));

  // Otherwise, add it to the constant list.
  if (addr.has_no_base_reg () && addr.has_no_index_reg ())
    m_const_addresses.push_back (start_addr);
}

// Remove START_ADDR from the list of available start addresses.
void
sh_ams2::start_addr_list::remove (reg_mod* start_addr)
{
  addr_expr addr = start_addr->effective_addr ().is_invalid ()
    ? make_reg_addr (start_addr->reg ()) : start_addr->effective_addr ();

  std::pair <reg_map::iterator, reg_map::iterator> matching_range;
  if (addr.has_base_reg ())
    {
      matching_range = m_reg_addresses.equal_range (addr.base_reg ());
      for (reg_map::iterator it = matching_range.first;
           it != matching_range.second; ++it)
        {
          if (it->second == start_addr)
            {
              m_reg_addresses.erase (it);
              break;
            }
        }
    }
  if (addr.has_index_reg ())
    {
      matching_range = m_reg_addresses.equal_range (addr.index_reg ());
      for (reg_map::iterator it = matching_range.first;
           it != matching_range.second; ++it)
        {
          if (it->second == start_addr)
            {
              m_reg_addresses.erase (it);
              break;
            }
        }
    }

  if (addr.has_no_base_reg () && addr.has_no_index_reg ())
    m_const_addresses.remove (start_addr);
}

// Split the access sequence pointed to by SEQ_IT into multiple sequences,
// grouping the accesses that have common terms in their effective address
// together.  Return an iterator to the sequence that comes after the newly
// inserted sequences.
std::list<sh_ams2::sequence>::iterator
sh_ams2::sequence::split (std::list<sequence>::iterator seq_it,
                          std::list<sequence>& sequences)
{
  typedef std::map<sequence_element*, split_sequence_info*> element_to_seq_map;
  typedef std::map<addr_expr, shared_term, cmp_addr_expr> shared_term_map;

  // Stores the newly created sequences.
  std::list<split_sequence_info> new_seqs;

  // Shows which new sequence each sequence element should go into.
  element_to_seq_map element_new_seqs;

  shared_term_map shared_terms;
  sequence& seq = *seq_it;

  // Find all terms that appear in the effective addresses of the mem accesses
  // and reg uses.  These will be used as potential bases for new sequences.
  std::vector<addr_expr> terms;
  for (sequence_iterator el = seq.elements ().begin ();
       el != seq.elements ().end (); ++el)
    {
      if (!(*el)->is_mem_access () && (*el)->type () != type_reg_use)
        continue;

      addr_expr addr = (*el)->effective_addr ();

      // If a reg-use's effective address isn't known, group it
      // together with other elements that use its register.
      if (addr.is_invalid () && (*el)->type () == type_reg_use)
        addr = make_reg_addr (((reg_use*)el->get ())->reg ());

      terms.clear ();
      addr.get_all_subterms (std::back_inserter (terms));
      for (std::vector<addr_expr>::iterator it = terms.begin ();
           it != terms.end (); ++it)
        {
          if (!it->is_invalid () && it->has_no_base_reg ()
              && it->has_no_index_reg ())
            {
              // If a displacement-only term fits into an address alternative,
              // it's not likely to be useful as a base term, so skip those.
              if (!(*el)->is_mem_access ())
                continue;
              if (((mem_access*)el->get ())
                  ->displacement_fits_alternative (it->disp ()))
                continue;

              // If it doesn't fit, treat them as one base term instead of
              // having a separate term for each constant.
              else
                *it = make_const_addr ((disp_t)0);
            }

          shared_term_map::iterator term = shared_terms.find (*it);
          if (term == shared_terms.end ())
            shared_terms.insert (
              std::make_pair (*it, shared_term (*it, el->get ())));
          else
            term->second.sharing_els ().push_back (el->get ());
        }
    }

  // Sort the shared terms by their score.
  std::vector<shared_term*> sorted_terms;
  sorted_terms.reserve (shared_terms.size ());
  for (shared_term_map::iterator it = shared_terms.begin ();
       it != shared_terms.end (); ++it)
      sorted_terms.push_back (&(it->second));
  std::sort (sorted_terms.begin (), sorted_terms.end (), shared_term::compare);

  // Create new sequences for the shared terms with the highest scores
  // and mark the accesses' new sequences in ELEMENT_NEW_SEQS appropriately.
  std::set<sequence_element*> inserted_els;
  for (std::vector<shared_term*>::iterator it
         = sorted_terms.begin (); it != sorted_terms.end (); ++it)
    {
      shared_term& term = **it;
      for (std::vector<sequence_element*>::iterator el
             = term.sharing_els ().begin ();
           el != term.sharing_els ().end (); ++el)
        {
          if (inserted_els.find (*el) != inserted_els.end ())
            continue;

          inserted_els.insert (*el);

          if (!term.new_seq ())
            {
              sequence& new_seq = *sequences.insert (seq_it, sequence ());
              new_seqs.push_back (split_sequence_info (&new_seq));
              term.set_new_seq (&new_seqs.back ());
            }

          element_new_seqs[*el] = term.new_seq ();
        }
    }

  // Add each mem access and reg use from the original sequence to the
  // appropriate new sequence based on ELEMENT_NEW_SEQS.  Also add the
  // reg mods to all sequences where they are used to calculate addresses.
  //
  // To determine which reg mods should be added to a sequence, we go over
  // the elements twice: In the first pass, we record the address regs that
  // the sequence uses.  In the second, we add the relevant elements to the
  // sequence.
  sequence_iterator last_non_mod = seq.elements ().end ();
  for (unsigned pass = 0; pass < 2; ++pass)
    {
      bool add_to_seq = (pass==1);
      for (sequence_reverse_iterator it =
             seq.elements ().rbegin (); it != seq.elements ().rend (); ++it)
        {
          sequence_element* el = it->get ();
          if (el->type () == type_reg_mod)
            // Add reg mods to multiple sequences.
            split_1 (new_seqs, (reg_mod*)el, add_to_seq, false);
          else
            {
              if (add_to_seq && last_non_mod == seq.elements ().end ())
                last_non_mod = stdx::prev (it.base ());

              // Find which sequence the element should go to
              // and place it to that sequence's front.
              split_sequence_info& new_seq
                = *(element_new_seqs.find (el)->second);

              split_2 (new_seq, el);
              if (add_to_seq)
                new_seq.seq ()->insert_element (
                  ref_counting_ptr<sequence_element>(el),
                  new_seq.seq ()->elements ().begin ());
            }
        }
    }

  // Add the remaining reg mods from the end of the original sequence.
  for (sequence_iterator it = last_non_mod; it != seq.elements ().end (); ++it)
    {
      sequence_element* el = it->get ();
      if (el->type () == type_reg_mod)
        split_1 (new_seqs, (reg_mod*)el, false, true);
    }

  // Remove the old sequence and return the next element after the
  // newly inserted sequences.
  return sequences.erase (seq_it);
}

// Internal function of access_sequence::split.  Adds the reg_mod RM to
// those sequences in NEW_SEQS that use it in their address calculations.
void
sh_ams2::sequence::split_1 (std::list<split_sequence_info>& new_seqs,
                            sh_ams2::reg_mod* rm, bool add_to_front,
                            bool add_to_back)
{
  for (std::list<split_sequence_info>::iterator seq_info = new_seqs.begin ();
       seq_info != new_seqs.end (); ++seq_info)
    {
      sequence& seq = *seq_info->seq ();

      // Add the reg mod only if it's used to calculate
      // one of the addresses in this new sequence.
      if (!seq_info->uses_addr_reg (rm->reg ()))
        continue;

      split_2 (*seq_info, rm);
      if (add_to_front)
        seq.insert_element (ref_counting_ptr<reg_mod>(rm),
                            seq.elements ().begin ());
      else if (add_to_back)
        seq.insert_element (ref_counting_ptr<reg_mod>(rm),
                            seq.elements ().end ());
    }
}

// Internal function of access_sequence::split.  Adds all the address regs
// referenced by EL to SEQ_INFO.
void
sh_ams2::sequence::split_2 (split_sequence_info& seq_info,
                            sh_ams2::sequence_element* el)
{
  if (el->type () == type_reg_mod && ((reg_mod*)el)->reg () != NULL)
    seq_info.add_reg (((reg_mod*)el)->reg ());

  if (el->type () == type_reg_use)
    {
      if (((reg_use*)el)->reg () != NULL)
        seq_info.add_reg (((reg_use*)el)->reg ());
      return;
    }

  addr_expr address;
  rtx addr_rtx;

  if (el->is_mem_access ())
    {
      mem_access* m = (mem_access*)el;
      address = m->current_addr ();
      addr_rtx = m->current_addr_rtx ();
    }
  else if (el->type () == type_reg_mod)
    {
      reg_mod* rm = (reg_mod*)el;
      address = rm->current_addr ();
      addr_rtx = rm->value ();
    }
  else
    gcc_unreachable ();

  if (!address.is_invalid ())
    {
      if (address.has_base_reg ())
        seq_info.add_reg (address.base_reg ());
      if (address.has_index_reg ())
        seq_info.add_reg (address.index_reg ());
    }
  else if (addr_rtx != NULL)
    {
      // Search the RTX for regs.
      subrtx_var_iterator::array_type array;
      FOR_EACH_SUBRTX_VAR (it, array, addr_rtx, NONCONST)
        {
          rtx x = *it;
          if (REG_P (x))
            seq_info.add_reg (x);
        }
    }
}

sh_ams2::sequence::~sequence (void)
{
  for (sequence_iterator els = elements ().begin ();
       els != elements ().end ();)
    {
      (*els)->sequences ().erase (this);
      els = remove_element (els, false);
    }
}

// Find all mem accesses in the rtx X of the insn I and add them to the
// sequence.  TYPE indicates the type of the next mem that we find
// (i.e. mem_load, mem_store or mem_operand).
// FIXME: Handle mem_operands properly.
void
sh_ams2::sequence::find_mem_accesses (rtx_insn* i, rtx& x, element_type type)
{
  static_vector<rtx*, 16> v;
  ref_counting_ptr<mem_access> acc;

  switch (GET_CODE (x))
    {
    case MEM:

      switch (type)
        {
        case type_mem_load:
          acc = make_ref_counted<mem_load> (i, GET_MODE (x), &x, XEXP (x, 0));
          break;
        case type_mem_store:
          acc = make_ref_counted<mem_store> (i, GET_MODE (x), &x, XEXP (x, 0));
          break;
        case type_mem_operand:
          v.push_back (&x);
          acc = make_ref_counted<mem_operand> (i, GET_MODE (x), v, XEXP (x, 0));
          break;
        default:
          gcc_unreachable ();
        }

      acc->set_current_addr (rtx_to_addr_expr (XEXP (x, 0), GET_MODE (x)));
      insert_element (acc, elements ().end ());
      break;

    case PARALLEL:
      for (int j = 0; j < XVECLEN (x, 0); j++)
        find_mem_accesses (i, XVECEXP (x, 0, j), type);
      break;

    case SET:
      find_mem_accesses (i, SET_DEST (x), type_mem_store);
      find_mem_accesses (i, SET_SRC (x), type_mem_load);
      break;

    case CALL:
      find_mem_accesses (i, XEXP (x, 0), type_mem_load);
      break;

    default:
      if (UNARY_P (x) || ARITHMETIC_P (x))
        {
          for (int j = 0; j < GET_RTX_LENGTH (GET_CODE (x)); j++)
            find_mem_accesses (i, XEXP (x, j), type);
        }
      break;
    }
}

// Add a reg mod for every insn that modifies an address register.
void
sh_ams2::sequence::find_addr_reg_mods (void)
{
  rtx_insn* last_insn = BB_END (start_bb ());
  reg_mod* last_reg_mod = NULL;

  for (addr_reg_map::iterator it = m_addr_regs.begin ();
       it != m_addr_regs.end (); ++it)
    {
      rtx reg = it->first;

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

          reg_mod* new_reg_mod
            = (reg_mod*)insert_unique (
                make_ref_counted<reg_mod> (mod_insn, reg, value,
                                           reg_current_addr))->get ();
          addr_expr reg_effective_addr = rtx_to_addr_expr (value, Pmode,
                                                           this, new_reg_mod);
          new_reg_mod->set_effective_addr (reg_effective_addr);

          if (last_reg_mod != NULL)
            {
              last_reg_mod->add_dependency (new_reg_mod);
              new_reg_mod->add_dependent_el (last_reg_mod);
            }

          last_insn = prev_nonnote_insn_bb (mod_insn);
          last_reg_mod = new_reg_mod;
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
      if (!INSN_P (i) || DEBUG_INSN_P (i))
	continue;

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
                      reg_use* new_reg_use
                        = (reg_use*)insert_unique (
                            make_ref_counted<reg_use> (i, *regs,
                                                       use_ref))->get ();
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
          sequence_element* el = els->second->get ();
          if (el->type () == type_reg_mod)
            {
              reg_mod* rm = (reg_mod*)el;
              visited_addr_regs.insert (rm->reg ());
              live_addr_regs[rm->reg ()] = rm;
            }
          last_el_insn = el->insn ();
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
      reg_use* new_reg_use
        = (reg_use*)insert_unique (
            make_ref_counted<reg_use> (last_el_insn, reg,
                                       (rtx_def**)NULL))->get ();
      new_reg_use->set_effective_addr (rm->effective_addr ());
      new_reg_use->add_dependency (rm);
      rm->add_dependent_el (new_reg_use);
    }
}

// A structure used for tracking and reverting modifications
// to access sequences.
class sh_ams2::mod_tracker
{
public:
  mod_tracker (sequence& seq, std::set<reg_mod*>& used_reg_mods,
               std::set<reg_mod*>& visited_reg_mods)
    : m_seq (seq), m_used_reg_mods (used_reg_mods),
      m_visited_reg_mods (visited_reg_mods)
  {
    m_dependent_els.reserve (8);
    m_inserted_reg_mods.reserve (8);
    m_use_changed_reg_mods.reserve (4);
    m_visited_changed_reg_mods.reserve (4);
    m_addr_changed_els.reserve (4);
  }

  void reset_changes (void)
  {
    for (std::vector<std::pair<sequence_element*, sequence_element*> >::
         reverse_iterator it = m_dependent_els.rbegin ();
         it != m_dependent_els.rend (); ++it)
      {
        it->second->remove_dependency (it->first);
        it->first->remove_dependent_el (it->second);
      }
    m_dependent_els.clear ();

    for (std::vector<reg_mod*>::iterator
           it = m_use_changed_reg_mods.begin ();
         it != m_use_changed_reg_mods.end (); ++it)
      m_used_reg_mods.erase (*it);
    m_use_changed_reg_mods.clear ();

    for (std::vector<reg_mod*>::iterator
           it = m_visited_changed_reg_mods.begin ();
         it != m_visited_changed_reg_mods.end (); ++it)
      m_visited_reg_mods.erase (*it);
    m_visited_changed_reg_mods.clear ();

    for (std::vector<std::pair <sequence_element*, addr_expr> >
           ::reverse_iterator it = m_addr_changed_els.rbegin ();
         it != m_addr_changed_els.rend (); ++it)
      {
        if (it->first->is_mem_access ())
          ((mem_access*)it->first)->set_current_addr (it->second);
        else if (it->first->type () == type_reg_use)
          ((reg_use*)it->first)->set_reg (it->second.base_reg ());
        else
          gcc_unreachable ();
      }
    m_addr_changed_els.clear ();

    for (std::vector<sequence_iterator>::reverse_iterator it
           = m_inserted_reg_mods.rbegin ();
         it != m_inserted_reg_mods.rend (); ++it)
      {
        m_seq.remove_element (*it);
        m_visited_reg_mods.erase ((reg_mod*)(*it)->get ());
        m_used_reg_mods.erase ((reg_mod*)(*it)->get ());
      }
    m_inserted_reg_mods.clear ();
  }

  // List of sequence elements that got new dependencies.
  std::vector<std::pair<sequence_element*, sequence_element*> >&
  dependent_els (void) { return m_dependent_els; }

  // List of reg-mods that were inserted into the sequence.
  std::vector<sequence_iterator>&
  inserted_reg_mods (void) { return m_inserted_reg_mods; }

  // List of reg-mods whose value got used by another reg-mod.
  std::vector<reg_mod*>&
  use_changed_reg_mods (void) { return m_use_changed_reg_mods; }

  // List of reg-mods that got visited.
  std::vector<reg_mod*>&
  visited_changed_reg_mods (void) { return m_visited_changed_reg_mods; }

  // List of sequence elements whose address changed, along
  // with their previous values.
  std::vector<std::pair <sequence_element*, addr_expr> >&
  addr_changed_els (void) { return m_addr_changed_els; }

private:
  sequence& m_seq;
  std::vector<std::pair<sequence_element*, sequence_element*> > m_dependent_els;
  std::vector<sequence_iterator> m_inserted_reg_mods;
  std::vector<reg_mod*> m_use_changed_reg_mods, m_visited_changed_reg_mods;
  std::vector<std::pair <sequence_element*, addr_expr> > m_addr_changed_els;
  std::set<reg_mod*>& m_used_reg_mods, m_visited_reg_mods;
};

// Generate the address modifications needed to arrive at the
// addresses in the sequence.
void
sh_ams2::sequence::gen_address_mod (delegate& dlg, int base_lookahead)
{
  typedef element_type_matches<type_reg_mod> reg_mod_match;
  typedef filter_iterator<sequence_iterator, reg_mod_match> reg_mod_iter;

  // Remove the sequence's original reg-mods.
  for (reg_mod_iter els = begin<reg_mod_match> (),
       els_end = end<reg_mod_match> (); els != els_end; )
    {
      if ((*els)->insn () == NULL || (*els)->used_by_unoptimizable_el ()
          || (*els)->effective_addr ().is_invalid ())
        {
          ++els;
          continue;
        }
      els = remove_element (els);
    }

  std::set<reg_mod*> used_reg_mods, visited_reg_mods;
  typedef filter_iterator<sequence_iterator, element_to_optimize> el_opt_iter;
  sequence_iterator prev_el = elements ().begin ();

  for (el_opt_iter els = begin<element_to_optimize> (),
       els_end = end<element_to_optimize> (); els != els_end; ++els)
    {
      // Mark the reg-mods before the current element as visited.
      for (sequence_iterator it = prev_el; it != els; ++it)
        {
          if ((*it)->type () == type_reg_mod)
            visited_reg_mods.insert ((reg_mod*)it->get ());
        }

      gen_address_mod_1 (els, dlg, used_reg_mods, visited_reg_mods,
                         base_lookahead
                         + dlg.adjust_lookahead_count (*this,
                                                       (sequence_iterator)els));
    }

  // Remove the unused reg <- constant copies that might have been
  // added while trying different address calculations.
  for (reg_mod_iter els = begin<reg_mod_match> (),
       els_end = end<reg_mod_match> (); els != els_end; )
    {
      gcc_assert ((*els)->type() == type_reg_mod);
      reg_mod* rm = (reg_mod*)els->get ();
      if (!rm->current_addr ().is_invalid ()
	  && rm->current_addr ().has_no_base_reg () &&
          rm->current_addr ().has_no_index_reg ())
	{
	  if (!reg_used_in_sequence (rm->reg (),
                                     stdx::next ((sequence_iterator)els)))
	    {
	      els = remove_element (els);
	      continue;
            }
        }
      ++els;
    }
}

// Internal function of gen_address_mod. Generate reg-mods needed to arrive at
// the address of EL and return the cost of the address modifications.
// If RECORD_IN_SEQUENCE is false, don't insert the actual modifications
// in the sequence, only calculate the cost.
int sh_ams2::sequence::
gen_address_mod_1 (filter_iterator<sequence_iterator, element_to_optimize> el,
                   delegate& dlg, std::set<reg_mod*>& used_reg_mods,
                   std::set<reg_mod*>& visited_reg_mods,
                   int lookahead_num, bool record_in_sequence)
{
  const addr_expr& ae = (*el)->effective_addr ();

  if (ae.is_invalid ())
    return 0;

  if (record_in_sequence)
    {
      log_msg ("\nprocessing element ");
      log_sequence_element (**el);
      log_msg ("\n");
    }

  int min_cost = infinite_costs;
  const alternative* min_alternative = NULL;
  reg_mod* min_start_base;
  reg_mod* min_start_index;
  addr_expr min_end_base, min_end_index;
  mod_tracker tracker (*this, used_reg_mods, visited_reg_mods);

  filter_iterator<sequence_iterator, element_to_optimize> next_el =
    lookahead_num ? stdx::next (el) : end<element_to_optimize> ();

  const alternative_set* alternatives;

  alternative_set reg_use_alt;
  if ((*el)->type () == type_reg_use)
    {
      // If this is a reg use, the address will be stored in a single reg.
      reg_use_alt.push_back (alternative (0, make_reg_addr (any_regno)));
      alternatives = &reg_use_alt;
    }
  else
    // Otherwise, the mem access' alternatives will be used.
    alternatives = &((mem_access*)el->get ())->alternatives ();

  // Find the alternative with the least cost.
  for (alternative_set::const_iterator alt = alternatives->begin ();
       alt != alternatives->end (); ++alt)
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

      std::pair<int, reg_mod*> base_start_addr =
        find_cheapest_start_addr (end_base, (sequence_iterator)el,
                                  alt_ae.disp_min (), alt_ae.disp_max (),
                                  alt_ae.type (), dlg,
                                  used_reg_mods, visited_reg_mods);

      if (base_start_addr.first == infinite_costs)
        continue;

      alt_min_cost += base_start_addr.first;

      std::pair<int, reg_mod*> index_start_addr;

      if (alt_ae.has_index_reg ())
        {
          index_start_addr
            = find_cheapest_start_addr (end_index, (sequence_iterator)el,
                                        alt_ae.disp_min (), alt_ae.disp_max (),
                                        alt_ae.type (), dlg,
                                        used_reg_mods, visited_reg_mods);
          if (index_start_addr.first == infinite_costs)
            continue;

          alt_min_cost += index_start_addr.first;
        }

      // Calculate the costs of the next element when this alternative is used.
      // This is done by inserting the address modifications of this alternative
      // into the sequence, calling this function on the next element and then
      // removing the inserted address mods.
      if (next_el != elements ().end ())
        {
          insert_address_mods (*alt, base_start_addr.second,
                               index_start_addr.second,
                               end_base, end_index, el,
                               tracker, used_reg_mods, visited_reg_mods, dlg);

          // Mark the reg-mods between the current and next element as visited.
          // This will be undone by the mod-tracker later.
          for (sequence_iterator it = el; it != next_el; ++it)
            {
              if ((*it)->type () == type_reg_mod)
                {
                  reg_mod* rm = (reg_mod*)it->get ();
                  visited_reg_mods.insert (rm);
                  tracker.visited_changed_reg_mods ().push_back (rm);
                }
            }

          int next_cost = gen_address_mod_1 (next_el, dlg,
                                             used_reg_mods, visited_reg_mods,
                                             lookahead_num-1, false);
          tracker.reset_changes ();

          if (next_cost == infinite_costs)
            continue;
          alt_min_cost += next_cost;
        }

      if (alt_min_cost < min_cost)
        {
          min_cost = alt_min_cost;
          min_start_base = base_start_addr.second;
          min_end_base = end_base;
          if (alt_ae.has_index_reg ())
            {
              min_start_index = index_start_addr.second;
              min_end_index = end_index;
            }
          min_alternative = alt;
        }
    }

  gcc_assert (min_cost != infinite_costs);

  if (record_in_sequence)
    {
      log_msg ("  min alternative: %d  min costs = %d\n",
               (int)(min_alternative - alternatives->begin ()),
               min_cost);
      insert_address_mods (*min_alternative,
                           min_start_base, min_start_index,
                           min_end_base, min_end_index, el,
                           tracker, used_reg_mods, visited_reg_mods, dlg);
    }

  return min_cost;
}

// The return type of try_insert_address_mods. Stores the reg-mod that contains
// the final address, the costs of the address modifications and the constant
// displacement that the mem access needs to use.
class sh_ams2::mod_addr_result
{
public:
  int cost;
  reg_mod* final_addr;
  disp_t addr_disp;

  mod_addr_result (int c)
    : cost (c), final_addr (NULL), addr_disp (0) { }

  mod_addr_result (reg_mod* addr)
    : cost (infinite_costs), final_addr (addr), addr_disp (0) { }

  mod_addr_result (reg_mod* addr, disp_t disp)
    : cost (infinite_costs), final_addr (addr), addr_disp (disp) { }

  mod_addr_result (int c, reg_mod* addr, disp_t disp)
    : cost (c), final_addr (addr), addr_disp (disp) { }
};

// Find the cheapest starting address that can be used to arrive at END_ADDR.
// Return it along with the cost of the address modifications.
std::pair<int, sh_ams2::reg_mod*> sh_ams2::sequence::
find_cheapest_start_addr (const addr_expr& end_addr, sequence_iterator el,
                          disp_t min_disp, disp_t max_disp,
                          addr_type_t addr_type,
                          delegate& dlg, std::set<reg_mod*>& used_reg_mods,
                          std::set<reg_mod*>& visited_reg_mods)
{
  int min_cost = infinite_costs;
  reg_mod* min_start_addr = NULL;
  mod_tracker tracker (*this, used_reg_mods, visited_reg_mods);
  machine_mode acc_mode = Pmode;
  if ((*el)->type () == type_reg_use)
    acc_mode = GET_MODE (((reg_use*)el->get ())->reg ());

  std::list<reg_mod*> start_addrs;
  start_addresses ().get_relevant_addresses (end_addr,
                                             std::back_inserter (start_addrs));
  for (start_addr_list::iterator addrs = start_addrs.begin ();
       addrs != start_addrs.end (); ++addrs)
    {
      // We can only use those reg-mods as starting addresses that
      // are before the current sequence element.
      if (visited_reg_mods.find (*addrs) == visited_reg_mods.end ())
        continue;

      int cost = try_insert_address_mods (*addrs, end_addr, min_disp, max_disp,
                                          addr_type, acc_mode, el, tracker,
                                          used_reg_mods, visited_reg_mods,
                                          dlg).cost;
      tracker.reset_changes ();
      if (cost < min_cost)
        {
          min_cost = cost;
          min_start_addr = *addrs;
        }
    }

  // If the end address is a constant address, try loading it into
  // the reg directly.
  if (end_addr.has_no_base_reg () && end_addr.has_no_index_reg ())
    {
      rtx const_reg = gen_reg_rtx (acc_mode);

      reg_mod* const_load
        = (reg_mod*)insert_element (
            make_ref_counted<reg_mod> ((rtx_insn*)NULL, const_reg, NULL_RTX,
                                       make_const_addr (end_addr.disp ()),
                                       make_const_addr (end_addr.disp ())),
            elements ().begin ())->get ();
      int cost = try_insert_address_mods (const_load, end_addr,
                                          min_disp, max_disp,
                                          addr_type, acc_mode, el,
                                          tracker, used_reg_mods,
                                          visited_reg_mods, dlg).cost;
      cost += dlg.addr_reg_mod_cost (const_reg, GEN_INT (end_addr.disp ()),
                                     *this, elements ().begin ());

      tracker.reset_changes ();
      if (cost < min_cost)
        {
          min_cost = cost;
          min_start_addr = const_load;

          // If the costs are reduced, this const reg might be used in the
          // final sequence, so we can't remove it.  However, it shouldn't
          // be visible when trying other alternatives.
          m_start_addr_list.remove ((reg_mod*)elements ().begin ()->get ());
        }
      // If this doesn't reduce the costs, we can safely remove the new reg-mod.
      else
        remove_element (elements ().begin ());
    }

  return std::make_pair (min_cost, min_start_addr);
}

// Generate the address modifications needed to arrive at BASE_END_ADDR and
// INDEX_END_ADDR from BASE/INDEX_START_ADDR when using ALT as the access
// alternative.  Record any changes to the sequence in TRACKER.
void sh_ams2::sequence::
insert_address_mods (const alternative& alt, reg_mod* base_start_addr,
                     reg_mod* index_start_addr,
                     const addr_expr& base_end_addr,
                     const addr_expr& index_end_addr,
                     sequence_iterator el, mod_tracker& tracker,
                     std::set<reg_mod*>& used_reg_mods,
                     std::set<reg_mod*>& visited_reg_mods, delegate& dlg)
{
  machine_mode acc_mode;
  const addr_expr& ae = (*el)->effective_addr ();

  if ((*el)->is_mem_access ())
    acc_mode = Pmode;
  else if ((*el)->type () == type_reg_use)
    acc_mode = GET_MODE (((reg_use*)el->get ())->reg ());
  else
    gcc_unreachable ();

  // Insert the modifications needed to arrive at the address
  // in the base reg.
  mod_addr_result base_insert_result =
    try_insert_address_mods (base_start_addr, base_end_addr,
                             alt.address ().disp_min (),
                             alt.address ().disp_max (),
                             alt.address ().type (),
                             acc_mode, el, tracker,
                             used_reg_mods, visited_reg_mods, dlg);

  (*el)->add_dependency (base_insert_result.final_addr);
  base_insert_result.final_addr->add_dependent_el (el->get ());
  tracker.dependent_els ()
    .push_back (std::make_pair (base_insert_result.final_addr, el->get ()));

  addr_expr new_addr;
  if (alt.address ().has_no_index_reg ())
    {
      disp_t disp = ae.disp () - base_insert_result.addr_disp;
      new_addr = non_mod_addr (base_insert_result.final_addr->reg (),
                               invalid_regno, 1, disp);
    }
  else
    {
      // Insert the modifications needed to arrive at the address
      // in the index reg.
      mod_addr_result index_insert_result =
        try_insert_address_mods (index_start_addr, index_end_addr,
                                 0, 0,
                                 alt.address ().type (),
                                 acc_mode, el, tracker,
                                 used_reg_mods, visited_reg_mods, dlg);

      (*el)->add_dependency (index_insert_result.final_addr);
      index_insert_result.final_addr->add_dependent_el (el->get ());
      tracker.dependent_els ()
        .push_back (std::make_pair (index_insert_result.final_addr,
                                    el->get ()));

      new_addr = non_mod_addr (base_insert_result.final_addr->reg (),
                               index_insert_result.final_addr->reg (), 1, 0);
    }

  if (alt.address ().type () == pre_mod)
    new_addr = pre_mod_addr (new_addr.base_reg (), alt.address ().disp ());
  else if (alt.address ().type () == post_mod)
    new_addr = post_mod_addr (new_addr.base_reg (), alt.address ().disp ());

  if ((*el)->is_mem_access ())
    {
      // Update the current address of the mem access with the alternative.
      mem_access* m = (mem_access*)el->get ();
      tracker.addr_changed_els ()
        .push_back (std::make_pair (m, m->current_addr ()));
      m->set_current_addr (new_addr);
      m->set_cost (alt.cost ());
    }
  else if ((*el)->type () == type_reg_use)
    {
      reg_use* ru = (reg_use*)el->get ();
      gcc_assert (new_addr.has_no_index_reg () && new_addr.has_no_disp ());
      if (ru->reg_ref () != NULL)
        {
          // If the expression in which the reg is used is known, modify the
          // reg that'll be used in the expression.
          tracker.addr_changed_els ()
            .push_back (std::make_pair (ru, make_reg_addr (ru->reg ())));
          ru->set_reg (new_addr.base_reg ());
        }
      else
        {
          // Otherwise, insert a reg-mod that sets the used reg to
          // the correct value.

          sequence_iterator inserted_el
            = insert_element (
              make_ref_counted<reg_mod> ((rtx_insn*)NULL, ru->reg (), NULL_RTX,
                                         new_addr, ru->effective_addr ()), el);
          tracker.inserted_reg_mods ().push_back (inserted_el);

          // Find and add the dependency for the new reg-mod
          for (sequence_iterator it = stdx::prev (inserted_el); ; --it)
            {
              if ((*it)->type () == type_reg_mod)
                {
                  reg_mod* rm = (reg_mod*)it->get ();
                  if (regs_equal (rm->reg (), new_addr.base_reg ())
                      || regs_equal (rm->reg (), new_addr.index_reg ()))
                    {
                      (*inserted_el)->add_dependency (rm);
                      rm->add_dependent_el (inserted_el->get ());
                      tracker.dependent_els ()
                        .push_back (std::make_pair (rm, inserted_el->get ()));
                      break;
                    }
                }

              if (it == elements ().begin ())
                gcc_unreachable ();
            }
        }
    }
}

// Try to generate the address modifications needed to arrive at END_ADDR
// from START_ADDR. Record any changes to the sequence in TRACKER.  If the
// final address is going to be used in a mem access, DISP_MIN and DISP_MAX
// indicate the displacement range of the access.
// Return the register that stores the final address, the cost of the
// modifications and the constant displacement that the mem access needs to use.
// If it's not possible to arrive at the final address, the returned cost will
// be infinite.
sh_ams2::mod_addr_result sh_ams2::sequence::
try_insert_address_mods (reg_mod* start_addr, const addr_expr& end_addr,
                         disp_t min_disp, disp_t max_disp,
                         addr_type_t addr_type, machine_mode acc_mode,
                         sequence_iterator el, mod_tracker& tracker,
                         std::set<reg_mod*>& used_reg_mods,
                         std::set<reg_mod*>& visited_reg_mods, delegate& dlg)
{
  int total_cost = 0;
  int clone_cost = used_reg_mods.find (start_addr) != used_reg_mods.end ()
                   ? dlg.addr_reg_clone_cost (start_addr->reg (), *this, el)
                   : 0;

  // Canonicalize the start and end addresses by converting
  // addresses of the form base+disp into index*1+disp.
  addr_expr c_start_addr = start_addr->effective_addr ().is_invalid ()
    ? make_reg_addr (start_addr->reg ()) : start_addr->effective_addr ();
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
    return mod_addr_result (infinite_costs);

  // Same for index regs, unless we can get to the end address
  // by subtracting.
  if (!regs_equal (c_start_addr.index_reg (), c_end_addr.index_reg ()))
    {
      if (!(c_start_addr.has_no_base_reg ()
            && c_end_addr.has_index_reg ()
            && regs_equal (c_start_addr.index_reg (), c_end_addr.base_reg ())
            && c_start_addr.scale () == 1
            && c_end_addr.scale () == -1))
        return mod_addr_result (infinite_costs);
    }

  // The start address' regs need to have the same machine mode as the access.
  if (c_start_addr.has_base_reg ()
      && GET_MODE (c_start_addr.base_reg ()) != acc_mode)
    return mod_addr_result (infinite_costs);
  if (c_start_addr.has_index_reg ()
      && GET_MODE (c_start_addr.index_reg ()) != acc_mode)
    return mod_addr_result (infinite_costs);


  // Add scaling.
  if (c_start_addr.has_index_reg ()
      && regs_equal (c_start_addr.index_reg (), c_end_addr.index_reg ())
      && c_start_addr.scale () != c_end_addr.scale ())
    {
      // We can't scale if the address has displacement or a base reg.
      if (c_start_addr.has_disp () || c_start_addr.has_base_reg ())
        return mod_addr_result (infinite_costs);

      // We can only scale by integers.
      gcc_assert (c_start_addr.scale () != 0);
      std::div_t sr = std::div (c_end_addr.scale (), c_start_addr.scale ());

      if (sr.rem != 0)
        return mod_addr_result (infinite_costs);

      scale_t scale = sr.quot;

      start_addr = insert_addr_mod (start_addr, acc_mode,
                                    gen_rtx_MULT (acc_mode, start_addr->reg (),
                                                  GEN_INT (scale)),
                                    non_mod_addr (invalid_regno,
                                                  start_addr->reg (),
                                                  scale, 0),
                                    non_mod_addr (invalid_regno,
                                                  c_start_addr.index_reg (),
                                                  c_end_addr.scale (), 0),
                                    el, tracker,
                                    used_reg_mods, visited_reg_mods, dlg);
      c_start_addr = start_addr->effective_addr ();
      start_addr->adjust_cost (clone_cost);
      clone_cost = 0;
      total_cost += start_addr->cost ();
    }

  // Try subtracting regs.
  if (c_start_addr.has_no_base_reg ()
      && c_end_addr.has_index_reg ()
      && regs_equal (c_start_addr.index_reg (), c_end_addr.base_reg ())
      && c_start_addr.scale () == 1
      && c_end_addr.scale () == -1)
    {
      reg_mod* index_reg_addr
        = find_start_addr_for_reg (c_end_addr.index_reg (),
                                   used_reg_mods, visited_reg_mods);
      bool index_reg_used
        = used_reg_mods.find (index_reg_addr) != used_reg_mods.end ();

      reg_mod* new_addr
        = insert_addr_mod (index_reg_addr, acc_mode,
                           gen_rtx_PLUS (acc_mode, start_addr->reg (),
                                         index_reg_addr->reg ()),
                           non_mod_addr (start_addr->reg (),
                                         index_reg_addr->reg (),
                                         -1, 0),
                           non_mod_addr (c_start_addr.index_reg (),
                                         c_end_addr.index_reg (),
                                         -1, c_start_addr.disp ()),
                           el, tracker, used_reg_mods, visited_reg_mods, dlg);
      new_addr->add_dependency (start_addr);
      start_addr->add_dependent_el (new_addr);
      tracker.dependent_els ().push_back (std::make_pair (start_addr,
                                                          new_addr));
      start_addr = new_addr;
      c_start_addr = start_addr->effective_addr ();
      start_addr->adjust_cost (clone_cost);
      clone_cost = 0;

      if (index_reg_used)
        {
          // Take into account the cloning costs of the index reg.
          int extra_cost = dlg.addr_reg_clone_cost (index_reg_addr->reg (),
                                                    *this, el);
          start_addr->adjust_cost (extra_cost);
        }

      total_cost += start_addr->cost ();
    }

  // Add missing base reg.
  if (c_start_addr.has_no_base_reg () && c_end_addr.has_base_reg ())
    {
      reg_mod* base_reg_addr
        = find_start_addr_for_reg (c_end_addr.base_reg (),
                                   used_reg_mods, visited_reg_mods);
      bool base_reg_used
        = used_reg_mods.find (base_reg_addr) != used_reg_mods.end ();

      reg_mod* new_addr
        = insert_addr_mod (base_reg_addr, acc_mode,
                           gen_rtx_PLUS (acc_mode, base_reg_addr->reg (),
                                         start_addr->reg ()),
                           non_mod_addr (base_reg_addr->reg (),
                                         start_addr->reg (), 1, 0),
                           non_mod_addr (c_end_addr.base_reg (),
                                         c_start_addr.index_reg (),
                                         c_start_addr.scale (),
                                         c_start_addr.disp ()),
                           el, tracker, used_reg_mods, visited_reg_mods, dlg);
      new_addr->add_dependency (start_addr);
      start_addr->add_dependent_el (new_addr);
      tracker.dependent_els ().push_back (std::make_pair (start_addr,
                                                          new_addr));
      start_addr = new_addr;
      c_start_addr = start_addr->effective_addr ();
      start_addr->adjust_cost (clone_cost);
      clone_cost = 0;

      if (base_reg_used)
        {
          // Take into account the cloning costs of the base reg.
          int extra_cost = dlg.addr_reg_clone_cost (base_reg_addr->reg (),
                                                    *this, el);
          start_addr->adjust_cost (extra_cost);
        }

      total_cost += start_addr->cost ();
    }

  // Set auto-inc/dec displacement that's added to the base reg.
  disp_t auto_mod_disp = 0;
  if (addr_type != non_mod)
    {
      gcc_assert (min_disp == max_disp);
      auto_mod_disp = min_disp;

      // If the base is only modified after the access, the
      // displacement range should be considered to be zero.
      if (addr_type == post_mod)
          min_disp = max_disp = 0;
    }

  // Add displacement.
  if (c_start_addr.disp () + min_disp > c_end_addr.disp ()
      || c_start_addr.disp () + max_disp < c_end_addr.disp ())
    {
      // Make the displacement as small as possible, since
      // adding smaller constants often costs less.
      disp_t disp = c_end_addr.disp () - c_start_addr.disp () - min_disp;
      disp_t alt_disp = c_end_addr.disp () - c_start_addr.disp () - max_disp;
      if (std::abs (alt_disp) < std::abs (disp))
        disp = alt_disp;

      start_addr = insert_addr_mod (start_addr, acc_mode,
                                    gen_rtx_PLUS (acc_mode, start_addr->reg (),
                                                  GEN_INT (disp)),
                                    non_mod_addr (start_addr->reg (),
                                                  invalid_regno, 1, disp),
                                    non_mod_addr (c_end_addr.base_reg (),
                                                  c_start_addr.index_reg (),
                                                  c_start_addr.scale (),
                                                  c_start_addr.disp () + disp),
                                    el, tracker,
                                    used_reg_mods, visited_reg_mods, dlg);
      c_start_addr = start_addr->effective_addr ();
      start_addr->adjust_cost (clone_cost);
      clone_cost = 0;
      total_cost += start_addr->cost ();
    }

  // For auto-mod accesses, copy the base reg into a new pseudo that will
  // be used by the auto-mod access.  This way, both the pre-access and
  // post-access version of the base reg can be reused by later accesses.
  // Do the same for constant displacement addresses so that there's no
  // cloning penalty for reusing the constant address in another access.
  if (addr_type != non_mod
      || (c_end_addr.has_no_base_reg () && c_end_addr.has_no_index_reg ()))
    {
      rtx pre_mod_reg = start_addr->reg ();
      start_addr
        = insert_addr_mod (start_addr, acc_mode,
                           pre_mod_reg,
                           make_reg_addr (pre_mod_reg),
                           non_mod_addr (c_end_addr.base_reg (),
                                         c_start_addr.index_reg (),
                                         c_start_addr.scale (),
                                         c_start_addr.disp () + auto_mod_disp),
                           el, tracker, used_reg_mods, visited_reg_mods, dlg);
      c_start_addr = start_addr->effective_addr ();
      start_addr->adjust_cost (clone_cost);
      clone_cost = 0;
      total_cost += start_addr->cost ();
    }

  return mod_addr_result (total_cost, start_addr, c_start_addr.disp ());
}

// Internal function of try_insert_address_mods.  Inserts a reg-mod with
// mode and addresses specified by ACC_MODE, CURR_ADDR_RTX, CURR_ADDR and
// EFFECTIVE_ADDR before EL in the sequence.  This reg-mod will depend
// on USED_RM.
sh_ams2::reg_mod* sh_ams2::sequence::
insert_addr_mod (reg_mod* used_rm, machine_mode acc_mode,
                 rtx curr_addr_rtx, const addr_expr& curr_addr,
                 const addr_expr& effective_addr,
                 sequence_iterator el, mod_tracker& tracker,
                 std::set<reg_mod*>& used_reg_mods,
                 std::set<reg_mod*>& visited_reg_mods, delegate& dlg)
{
  if (used_reg_mods.find (used_rm) == used_reg_mods.end ())
    {
      used_reg_mods.insert (used_rm);
      tracker.use_changed_reg_mods ().push_back (used_rm);
    }
  rtx new_reg = gen_reg_rtx (acc_mode);
  sequence_iterator inserted_el
    = insert_element (
        make_ref_counted<reg_mod> ((rtx_insn*)NULL, new_reg, NULL_RTX,
                                   curr_addr, effective_addr), el);
  visited_reg_mods.insert ((reg_mod*)inserted_el->get ());
  (*inserted_el)->add_dependency (used_rm);
  used_rm->add_dependent_el (inserted_el->get ());
  tracker.inserted_reg_mods ().push_back (inserted_el);
  tracker.dependent_els ().push_back (std::make_pair (used_rm,
                                                      inserted_el->get ()));
  (*inserted_el)->set_cost (dlg.addr_reg_mod_cost (new_reg, curr_addr_rtx,
                                             *this, el));
  return (reg_mod*)inserted_el->get ();
}

// Find a starting address whose effective address is the single base reg REG.
// If there are multiple such addresses, try to return one that wasn't used
// before (so that there's no cloning cost when using it).
sh_ams2::reg_mod* sh_ams2::sequence::
find_start_addr_for_reg (rtx reg, std::set<reg_mod*>& used_reg_mods,
                         std::set<reg_mod*>& visited_reg_mods)
{
  std::list<reg_mod*> start_addrs;
  start_addresses ().get_relevant_addresses (make_reg_addr (reg),
                                             std::back_inserter (start_addrs));
  reg_mod* found_addr = NULL;

  for (start_addr_list::iterator addrs = start_addrs.begin ();
       addrs != start_addrs.end (); ++addrs)
    {
      if (visited_reg_mods.find (*addrs) == visited_reg_mods.end ())
        continue;

      const addr_expr &ae = (*addrs)->effective_addr ().is_invalid ()
                            ? make_reg_addr ((*addrs)->reg ())
                            : (*addrs)->effective_addr ();
      if (ae.has_no_index_reg () && regs_equal (ae.base_reg (), reg))
        {
          found_addr = *addrs;
          if (used_reg_mods.find (found_addr) == used_reg_mods.end ())
            break;
        }
    }

  gcc_assert (found_addr != NULL);
  return found_addr;
}

// Update the original insn stream with the changes in this sequence.
void
sh_ams2::sequence::update_insn_stream (void)
{
  bool insn_sequence_started = false;
  rtx_insn* last_insn = NULL;

  for (sequence_iterator els = elements ().begin ();
       els != elements ().end (); ++els)
    {
      if ((*els)->insn ())
        {
          last_insn = (*els)->insn ();

          if (insn_sequence_started)
            {
              rtx_insn* new_insns = get_insns ();
              end_sequence ();
              insn_sequence_started = false;

              log_msg ("emitting new insns = \n");
              log_rtx (new_insns);
              log_msg ("\nbefore insn\n");
              log_insn ((*els)->insn ());
              log_msg ("\n");
              emit_insn_before (new_insns, (*els)->insn ());
            }
        }

      if (!(*els)->optimization_enabled ())
        {
          log_msg ("element didn't get optimized, skipping\n");
          continue;
        }
      insn_sequence_started
        = (*els)->generate_new_insns (insn_sequence_started);
    }

  // Emit remaining address modifying insns after the last insn in the access.
  if (insn_sequence_started)
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
// FIXME: in which cases can an insn in the sequence NOT belong to a basic block?
// either this check is unnecessary, or add a comment.
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

// FIXME:
// start_bb and start_insn should use this.
sh_ams2::sequence_const_iterator
sh_ams2::sequence::start_insn_element (void) const
{
  for (sequence_const_iterator e = elements ().begin ();
       e != elements ().end (); ++e)
    if ((*e)->insn ())
      return e;

//  gcc_unreachable ();   FIXME: sure?  always?
  return elements ().end ();
}

// Insert a new element into the sequence.  Return an iterator pointing
// to the newly inserted element.
sh_ams2::sequence_iterator
sh_ams2::sequence::insert_element (const ref_counting_ptr<sequence_element>& el,
                                   sequence_iterator insert_before)
{
  sequence_iterator iter = elements ().insert (insert_before, el);

  el->sequences ().insert (this);

  // Update the insn -> element map.
  if (el->insn ())
      m_insn_el_map.insert (std::make_pair (el->insn (), iter));

  // Update the address reg and the start address list.
  if (el->type () == type_reg_mod)
    {
      reg_mod* rm = (reg_mod*)el.get ();
      ++m_addr_regs[rm->reg ()];
      m_start_addr_list.add (rm);
    }

  return iter;
}

// If EL is unique, insert it into the sequence and return an iterator
// pointing to it.  If it already has a duplicate in the sequence, don't
// insert it and return an iterator to the already inserted duplicate instead.
// The place of the element is determined by its insn.
sh_ams2::sequence_iterator
sh_ams2::sequence::insert_unique (const ref_counting_ptr<sequence_element>& el)
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
          if (*el == **els)
            return els;
        }

/*
      // FIXME: this should be the same as above, shouldn't it?
      // start_insn_element returns the first element that's got an insn,
      // so we can use that as an end iterator.  It's a bit easier to grasp.
      sequence_const_iterator first_insn_i = start_insn_element ();
      sequence_iterator els = std::find_if (elements ().begin (), first_insn_i,
					    sequence_element::equals (*el));
      if (els != first_insn_i)
	return els;
*/
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
          if (*el == **els->second)
            return els->second;
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
sh_ams2::sequence::remove_element (sh_ams2::sequence_iterator el,
                                   bool clear_deps)
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

  // Update the address reg and the start address list.
  if ((*el)->type () == type_reg_mod)
    {
      reg_mod* rm = (reg_mod*)el->get ();
      addr_reg_map::iterator addr_reg
        = m_addr_regs.find (rm->reg ());
      --addr_reg->second;
      if (addr_reg->second == 0)
        m_addr_regs.erase (addr_reg);

      m_start_addr_list.remove (rm);
    }

  // Update the element's dependencies.
  if (clear_deps)
    {
      for (std::list<sequence_element*>::iterator deps
             = (*el)->dependencies ().begin ();
           deps != (*el)->dependencies ().end (); ++deps)
        (*deps)->remove_dependent_el (el->get ());
      (*el)->dependencies ().clear ();
      for (std::list<sequence_element*>::iterator dep_els
             = (*el)->dependent_els ().begin ();
           dep_els != (*el)->dependent_els ().end (); ++dep_els)
        (*dep_els)->remove_dependency (el->get ());
      (*el)->dependent_els ().clear ();
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

// Check whether REG is used in any element after START.
bool
sh_ams2::sequence
::reg_used_in_sequence (rtx reg, sequence_const_iterator start) const
{
  for (sequence_const_iterator els = start; els != elements ().end (); ++els)
    {
      if ((*els)->uses_reg (reg))
        return true;
    }
  return false;
}

// Fill the m_inc/dec_chain fields of the elements in the sequence.
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
sh_ams2::sequence::calculate_adjacency_info (void)
{
  typedef filter_iterator<sequence_iterator, element_to_optimize> iter;

  for (iter m = begin<element_to_optimize> (),
         mend = end<element_to_optimize> ();
       m != mend; )
    {
      iter inc_end = std::adjacent_find (m, mend,
                                         sequence_element::not_adjacent_inc);
      if (inc_end != mend)
        ++inc_end;

      const int inc_len = std::distance (m, inc_end);
      const sequence_element* first_el = m->get ();
      iter last_el = inc_end;
      --last_el;

      for (int i = 0; i < inc_len; ++i)
	{
	  (*m)->set_inc_chain (adjacent_chain_info (i, inc_len, first_el,
                                                    last_el->get ()));
	  ++m;
	}
    }

  for (iter m = begin<element_to_optimize> (),
         mend = end<element_to_optimize> ();
       m != mend; )
    {
      iter dec_end = std::adjacent_find (m, mend,
                                         sequence_element::not_adjacent_dec);
      if (dec_end != mend)
        ++dec_end;

      const int dec_len = std::distance (m, dec_end);
      const sequence_element* first_el = m->get ();
      iter last_el = dec_end;
      --last_el;

      for (int i = 0; i < dec_len; ++i)
	{
	  (*m)->set_dec_chain (adjacent_chain_info (i, dec_len, first_el,
                                                    last_el->get ()));
	  ++m;
	}
    }
}

// Re-calculate the sequence's cost.
void
sh_ams2::sequence::update_cost (delegate& d)
{
  for (sequence_iterator els = elements ().begin ();
       els != elements ().end (); ++els)
    (*els)->update_cost (d, *this, els);
}

// Check whether the cost of the sequence is already minimal and
// can't be improved further, i.e. if all memory accesses use the
// cheapest alternative and there are no reg-mods with nonzero cost.
bool
sh_ams2::sequence::cost_already_minimal (void) const
{
  for (sequence_const_iterator els = elements ().begin ();
       els != elements ().end (); ++els)
    {
      if ((*els)->is_mem_access ())
        {
          mem_access *m = (mem_access*)els->get ();
          for (alternative_set::const_iterator
		  alt = m->alternatives ().begin ();
               alt != m->alternatives ().end (); ++alt)
            {
              if (alt->cost () < m->cost ())
                return false;
            }
        }
      else if ((*els)->cost () > 0)
        return false;
    }
  return true;
}

// Update the alternatives of the sequence's accesses.
void
sh_ams2::sequence::update_access_alternatives (delegate& d,
                                               bool force_validation,
                                               bool disable_validation,
                                               bool adjust_costs)
{
  typedef element_type_matches<type_mem_load, type_mem_store, type_mem_operand>
    match;
  typedef filter_iterator<sequence_iterator, match> iter;

  for (iter e = begin<match> (), e_end = end<match> (); e != e_end; ++e)
    ((mem_access*)e->get ())
      ->update_access_alternatives (*this, e.base_iterator (),
                                    d, force_validation, disable_validation);
  if (!adjust_costs)
    return;

  for (iter e = begin<match> (), e_end = end<match> (); e != e_end; ++e)
    {
      mem_access* m = (mem_access*)e->get ();
      for (alternative_set::iterator alt = m->alternatives ().begin ();
           alt != m->alternatives ().end (); ++alt)
        d.adjust_alternative_costs (*alt, *this, e.base_iterator ());
    }
}

// Update the alternatives of the access.
void
sh_ams2::mem_access::update_access_alternatives (const sequence& seq,
                                                 sequence_const_iterator it,
                                                 delegate& d,
                                                 bool force_validation,
                                                 bool disable_validation)
{
  bool val_alts = alternative_validation_enabled ();

  alternatives ().clear ();

  d.mem_access_alternatives (alternatives (), seq, it, val_alts);
  set_alternative_validation (val_alts);

  typedef alternative_valid match;
  typedef filter_iterator<alternative_set::iterator, match> iter;

  // By default alternative validation is enabled for all accesses.
  // The target's delegate implementation might disable validation for insns
  // to speed up processing, if it knows that all the alternatives are valid.
  if ((alternative_validation_enabled () || force_validation)
      && !disable_validation)
    {
      log_msg ("\nvalidating alternatives for insn\n");
      log_insn (insn ());

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

      for (iter alt = iter (alternatives ().begin (),
			    alternatives ().end ()),
	   alt_end = iter (alternatives ().end (),
			   alternatives ().end ()); alt != alt_end; ++alt)
	{
	  if (alt->address ().has_no_base_reg ())
	    log_invalidate_cont ("has no base reg");

	  tmp_addr = alt->address ();
	  if (tmp_addr.base_reg () == any_regno)
	    tmp_addr.set_base_reg (tmp_reg);
	  if (tmp_addr.index_reg () == any_regno)
	    tmp_addr.set_index_reg (tmp_reg);

	  if (!try_replace_addr (tmp_addr))
	    log_invalidate_cont ("failed to substitute regs");

	  if (alt->address ().disp_min () > alt->address ().disp_max ())
	    log_invalidate_cont ("min disp > max disp");

	  if (alt->address ().disp_min () != alt->address ().disp_max ())
	    {
	      // Probe some displacement values and hope that we cover enough.
	      tmp_addr.set_disp (alt->address ().disp_min ());
	      if (!try_replace_addr (tmp_addr))
		log_invalidate_cont ("bad min disp");

	      tmp_addr.set_disp (alt->address ().disp_max ());
	      if (!try_replace_addr (tmp_addr))
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
		  if (!try_replace_addr (tmp_addr))
		    log_invalidate_cont ("bad min disp min scale");

		  tmp_addr.set_disp (alt->address ().disp_min ());
		  tmp_addr.set_scale (alt->address ().scale_max ());
		  if (!try_replace_addr (tmp_addr))
		    log_invalidate_cont ("bad min disp max scale");

		  tmp_addr.set_disp (alt->address ().disp_max ());
		  tmp_addr.set_scale (alt->address ().scale_min ());
		  if (!try_replace_addr (tmp_addr))
		    log_invalidate_cont ("bad max disp min scale");

		  tmp_addr.set_disp (alt->address ().disp_max ());
		  tmp_addr.set_scale (alt->address ().scale_max ());
		  if (!try_replace_addr (tmp_addr))
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
  alternative_set::iterator first_invalid =
    std::stable_partition (alternatives ().begin (), alternatives ().end (),
                           alternative_valid ());

  // FIXME: Implement erase (iter, iter) for alternative_set.
  if (first_invalid != alternatives ().end ())
    {
      unsigned int c = std::distance (first_invalid, alternatives ().end ());
      log_msg ("removing %u invalid alternatives\n", c);

      for (; c > 0; --c)
	alternatives ().pop_back ();
    }

  if (alternatives ().empty ())
    {
      log_msg ("no valid alternatives, not optimizing this access\n");
      set_optimization_enabled (false);
    }

  // At least on clang/libc++ there is a problem with bind1st, mem_fun and
  // &access::matches_alternative.
  alternative_set::iterator alt_match;
  for (alt_match = alternatives ().begin ();
       alt_match != alternatives ().end (); ++alt_match)
    if (matches_alternative (*alt_match))
      break;

  if (alt_match == alternatives ().end ())
    {
      log_msg ("original address does not match any alternative, "
	       "not optimizing this access\n");
      set_optimization_enabled (false);
    }
}

bool
sh_ams2::mem_access::matches_alternative (const sh_ams2::alternative& alt) const
{
  const addr_expr& ae = current_addr ();
  const addr_expr& alt_ae = alt.address ();

  if (ae.type () != alt_ae.type ())
    return false;

  if (ae.has_base_reg () != alt_ae.has_base_reg ())
    return false;
  if (ae.has_index_reg () != alt_ae.has_index_reg ())
    return false;

  if (ae.has_base_reg () && alt_ae.has_base_reg ()
      && !regs_match (ae.base_reg (), alt_ae.base_reg ()))
    return false;

  if (ae.disp () < alt_ae.disp_min () || ae.disp () > alt_ae.disp_max ())
    return false;

  if (ae.has_index_reg ()
      && (ae.scale () < alt_ae.scale_min ()
          || ae.scale () > alt_ae.scale_max ()
          || !regs_match (ae.index_reg (), alt_ae.index_reg ())))
    return false;

  return true;
}

// Check if DISP can be used as constant displacement in any of the address
// alternatives of the access.
bool
sh_ams2::mem_access::displacement_fits_alternative (disp_t disp) const
{
  for (alternative_set::const_iterator alt = alternatives ().begin ();
       alt != alternatives ().end (); ++alt)
    {
      if (alt->address ().disp_min () <= disp
          && alt->address ().disp_max () >= disp)
        return true;
    }
  return false;
}

// Update the reg-use expression to NEW_REG.  Return false if the update
// was unsuccessful.
bool
sh_ams2::reg_use::set_reg_ref (rtx new_reg)
{
  return validate_change (insn (), m_reg_ref, new_reg, false);
}

bool
sh_ams2::mem_access::generate_new_insns (bool insn_sequence_started)
{
  if (current_addr ().is_invalid ())
    {
      log_msg ("current address not valid, skipping\n");
      return insn_sequence_started;
    }

  // Update the mem access rtx with the element's current_addr.

  // If the original access used an auto-mod addressing mode,
  // remove the original REG_INC note.
  // FIXME: Maybe remove only the notes for the particular regs
  // instead of removing them all?  Might be interesting for
  // multi-mem insns.
  remove_incdec_notes (insn ());

  gcc_assert (!insn_sequence_started);
  if (!replace_addr (current_addr ()))
    {
      log_msg ("failed to replace mem rtx with new address\n");
      log_addr_expr (current_addr ());
      log_msg ("\nin insn\n");
      log_insn (insn ());
      log_msg ("\n");
      abort ();
    }

  sh_check_add_incdec_notes (insn ());
  return insn_sequence_started;
}

bool
sh_ams2::reg_use::generate_new_insns (bool insn_sequence_started)
{
  if (reg_ref () == NULL)
    {
      log_msg ("reg-use is unspecified, skipping\n");
      return insn_sequence_started;
    }

  gcc_assert (set_reg_ref (reg ()));
  return insn_sequence_started;
}

bool
sh_ams2::reg_mod::generate_new_insns (bool insn_sequence_started)
{
  if (insn () != NULL)
    {
      log_msg ("reg-mod already has an insn, skipping\n");
      return insn_sequence_started;
    }

  if (current_addr ().has_base_reg () && current_addr ().has_no_index_reg ()
      && regs_equal (current_addr ().base_reg (), reg ()))
    {
      log_msg ("reg-mod sets the reg to itself, skipping\n");
      return insn_sequence_started;
    }

  if (!insn_sequence_started)
    {
      start_sequence ();
      insn_sequence_started = true;
    }

  rtx new_val;
  if (current_addr ().has_no_base_reg () && current_addr ().has_no_index_reg ())
    {
      new_val = GEN_INT (current_addr ().disp ());
      log_msg ("reg mod new val (1) = ");
      log_rtx (new_val);
      log_msg ("\n");
    }
  else
    {
      if (current_addr ().has_index_reg ())
        {
          bool subtract = current_addr ().has_base_reg ()
            && current_addr ().scale () == -1;
          rtx index = subtract ? current_addr ().index_reg ()
            : expand_mult (current_addr ().index_reg (),
                           current_addr ().scale ());

          if (current_addr ().has_no_base_reg ())
            new_val = index;
          else if (subtract)
            new_val = expand_minus (current_addr ().base_reg (), index);
          else
            new_val = expand_plus (current_addr ().base_reg (), index);
          log_msg ("reg mod new val (2) = ");
          log_rtx (new_val);
          log_msg ("\n");
        }
      else
        {
          new_val = current_addr ().base_reg ();
          log_msg ("reg mod new val (3) = ");
          log_rtx (new_val);
          log_msg ("\n");
        }

      new_val = expand_plus (new_val, current_addr ().disp ());
    }

  set_insn (emit_move_insn (reg (), new_val));
  return insn_sequence_started;
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

                  mem_access* acc = (mem_access*)els->second->get ();
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

bool
sh_ams2::mem_load::try_replace_addr (const sh_ams2::addr_expr& new_addr)
{
  rtx prev_rtx = XEXP (*m_mem_ref, 0);
  rtx new_rtx = new_addr.to_rtx ();

  XEXP (*m_mem_ref, 0) = new_rtx;

  int new_insn_code = recog (PATTERN (insn ()), insn (), NULL);

  XEXP (*m_mem_ref, 0) = prev_rtx;
  return new_insn_code >= 0;
}

bool
sh_ams2::mem_load::replace_addr (const sh_ams2::addr_expr& new_addr)
{
  // In some cases we might actually end up with 'new_addr' being not
  // really a valid address.  validate_change will then use the
  // target's 'legitimize_address' function to make a valid address out of
  // it.  While doing so the target might emit new insns which we must
  // capture and re-emit before the actual insn.
  // If this happens it means that something with the alternatives or
  // mem insn matching is not working as intended.

  start_sequence ();
  bool r = validate_change (insn (), m_mem_ref,
                            replace_equiv_address (*m_mem_ref,
                                                   new_addr.to_rtx ()),
                            false);

  rtx_insn* new_insns = get_insns ();
  end_sequence ();

  if (r && !mem_access::allow_new_insns && new_insns != NULL)
    {
      log_msg ("validate_change produced new insns: \n");
      log_rtx (new_insns);
      abort ();
    }

  if (r && new_insns != NULL)
    emit_insn_before (new_insns, insn ());

  return r;
}

bool
sh_ams2::mem_store::try_replace_addr (const sh_ams2::addr_expr& new_addr)
{
  // FIXME: same as mem_load::replace_addr.
  // move to base class? (see mem_store::replace_addr)

  rtx prev_rtx = XEXP (*m_mem_ref, 0);
  rtx new_rtx = new_addr.to_rtx ();

  XEXP (*m_mem_ref, 0) = new_rtx;

  int new_insn_code = recog (PATTERN (insn ()), insn (), NULL);

  XEXP (*m_mem_ref, 0) = prev_rtx;
  return new_insn_code >= 0;
}

bool
sh_ams2::mem_store::replace_addr (const sh_ams2::addr_expr& new_addr)
{
  // FIXME: same as mem_load::replace_addr.

  // this should be implemented in the base class mem_access.  for that,
  // the base class has to get access to the sub-class's addr rtx locations.
  // idea: add a new function
  //    virtual std::pair<const rtx*, const rtx*> mem_access::mem_refs (void) const;
  //
  // -> override that function accordingly in mem_load, mem_store and mem_operand.
  // -> use 'validate_change' with in_group argument = true, for each occurrence
  //    of the addr rtx to be changed.  then use 'apply_change_group' to change
  //    them all at once.

  start_sequence ();
  bool r = validate_change (insn (), m_mem_ref,
                            replace_equiv_address (*m_mem_ref,
                                                   new_addr.to_rtx ()),
                            false);

  rtx_insn* new_insns = get_insns ();
  end_sequence ();

  if (r && !mem_access::allow_new_insns && new_insns != NULL)
    {
      log_msg ("validate_change produced new insns: \n");
      log_rtx (new_insns);
      abort ();
    }

  if (r && new_insns != NULL)
    emit_insn_before (new_insns, insn ());

  return r;
}

bool
sh_ams2::mem_operand::try_replace_addr (const sh_ams2::addr_expr& new_addr)
{
  rtx new_rtx = new_addr.to_rtx ();
  static_vector<rtx, 16> prev_rtx;
  static_vector<rtx*, 16>::iterator it;
  static_vector<rtx, 16>::iterator prev_it;

  for (it = m_mem_refs.begin (); it != m_mem_refs.end (); ++it)
    {
      prev_rtx.push_back (XEXP (**it, 0));
      XEXP (**it, 0) = new_rtx;
    }

  int new_insn_code = recog (PATTERN (insn ()), insn (), NULL);

  for (it = m_mem_refs.begin (), prev_it = prev_rtx.begin ();
       it != m_mem_refs.end (); ++it, ++prev_it)
    XEXP (**it, 0) = *prev_it;

  return new_insn_code >= 0;
}

bool
sh_ams2::mem_operand::replace_addr (const sh_ams2::addr_expr& new_addr)
{
  rtx new_rtx = new_addr.to_rtx ();
  bool r = true;
  for (static_vector<rtx*, 16>::iterator it = m_mem_refs.begin ();
       it != m_mem_refs.end (); ++it)
    {
      start_sequence ();
      r &= !validate_change (insn (),
                             *it, replace_equiv_address (**it, new_rtx), true);
      if (!r)
        break;
    }

  if (!r)
    return false;

  apply_change_group ();
  rtx_insn* new_insns = get_insns ();
  end_sequence ();

  if (r && !mem_access::allow_new_insns && new_insns != NULL)
    {
      log_msg ("validate_change produced new insns: \n");
      log_rtx (new_insns);
      abort ();
    }

  if (r && new_insns != NULL)
    emit_insn_before (new_insns, insn ());

  return true;
}

bool sh_ams2::mem_access::
operator == (const sequence_element& other) const
{
  return sequence_element::operator == (other)
    && effective_addr () == effective_addr ()
    && current_addr_rtx () == ((const mem_access&)other).current_addr_rtx ()
    && current_addr () == ((const mem_access&)other).current_addr ();
}

bool sh_ams2::reg_mod::
operator == (const sequence_element& other) const
{
  return sequence_element::operator == (other)
    && sh_ams2::regs_equal (reg (), ((const reg_mod&)other).reg ())
    && value () == ((const reg_mod&)other).value ()
    && current_addr () == ((const reg_mod&)other).current_addr ();
}

bool sh_ams2::reg_barrier::
operator == (const sequence_element& other) const
{
  return sequence_element::operator == (other)
    && sh_ams2::regs_equal (
         reg (), ((const sh_ams2::reg_barrier&)other).reg ());
}


bool sh_ams2::reg_use::
operator == (const sequence_element& other) const
{
  return sequence_element::operator == (other)
    && sh_ams2::regs_equal (reg (), ((const reg_use&)other).reg ());
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
  const bool trace_back_addr = seq != NULL && el != NULL;

  addr_expr op0 = make_invalid_addr ();
  addr_expr op1 = make_invalid_addr ();
  HOST_WIDE_INT disp;
  HOST_WIDE_INT scale;
  rtx base_reg, index_reg;
  if (x == NULL_RTX)
    return make_invalid_addr ();

  rtx_code code = GET_CODE (x);

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
                = seq->insert_unique (
                    make_ref_counted<reg_mod> ((rtx_insn*)NULL, x, x,
                                               make_reg_addr (x),
                                               make_reg_addr (x)));
              el->add_dependency (new_reg_mod->get ());
              (*new_reg_mod)->add_dependent_el (el);

              return make_reg_addr (x);
            }

          addr_expr reg_current_addr
            = find_reg_note (mod_insn, REG_INC, NULL_RTX)
            ? make_reg_addr (x)
            : rtx_to_addr_expr (value, mem_mach_mode);

          // Insert the modifying insn into the sequence as a reg mod.
          sequence_iterator new_reg_mod
            = seq->insert_unique (make_ref_counted<reg_mod> (mod_insn, x, value,
                                                             reg_current_addr));
          el->add_dependency (new_reg_mod->get ());
          (*new_reg_mod)->add_dependent_el (el);

          // Expand the register's value further.
          addr_expr reg_effective_addr = rtx_to_addr_expr (
            value, mem_mach_mode, seq, new_reg_mod->get ());

          (*new_reg_mod)->set_effective_addr (reg_effective_addr);

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

unsigned int
sh_ams2::execute (function* fun)
{
  log_msg ("sh-ams pass (WIP)\n");
  log_options (m_options);
  log_msg ("\n\n");
  mem_access::allow_new_insns = m_options.allow_mem_addr_change_new_insns;

  typedef element_type_matches<type_mem_load, type_mem_store,
                               type_mem_operand> mem_match;
  typedef filter_iterator<sequence_iterator, mem_match> mem_acc_iter;
  typedef element_type_matches<type_reg_mod> reg_mod_match;
  typedef filter_iterator<sequence_iterator, reg_mod_match> reg_mod_iter;
  typedef element_type_matches<type_reg_use> reg_use_match;
  typedef filter_iterator<sequence_iterator, reg_use_match> reg_use_iter;

//  df_set_flags (DF_DEFER_INSN_RESCAN); // needed?

  df_note_add_problem ();
  df_analyze ();

  std::list<sequence> sequences;

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

          seq.find_mem_accesses (i, PATTERN (i));
         }

      for (mem_acc_iter m_it = seq.begin<mem_match> (),
             m_end = seq.end<mem_match> (); m_it != m_end; ++m_it)
        {
          mem_access* m = (mem_access*)m_it->get ();
          m->set_effective_addr (rtx_to_addr_expr (m->current_addr_rtx (),
                                                   m->mach_mode (), &seq, m));
        }
    }

  std::vector<ref_counting_ptr<sequence_element> > original_reg_mods;
  log_msg ("\nprocessing extracted sequences\n");
  for (std::list<sequence>::iterator it = sequences.begin ();
       it != sequences.end ();)
    {
      sequence& seq = *it;

      if (seq.elements ().empty ())
        {
          ++it;
          continue;
        }

      log_msg ("find_addr_reg_mods\n");
      seq.find_addr_reg_mods ();

      // Add the sequence's reg-mods to the original reg-mod list.
      for (reg_mod_iter rm = seq.begin<reg_mod_match> (),
             rm_end = seq.end<reg_mod_match> (); rm != rm_end; ++rm)
        original_reg_mods.push_back (ref_counting_ptr<sequence_element> (*rm));

      log_sequence (seq, false);
      log_msg ("\n\n");

      log_msg ("find_addr_reg_uses\n");
      seq.find_addr_reg_uses ();

      log_sequence (seq, false);
      log_msg ("\n\n");

      log_msg ("updating access alternatives\n");
      seq.update_access_alternatives (m_delegate,
                                      m_options.force_alt_validation,
                                      m_options.disable_alt_validation);

      log_sequence (seq, true, true);
      log_msg ("\n\n");

      log_msg ("split_access_sequence\n");
      if (m_options.split_sequences)
        it = sequence::split (it, sequences);
      else
        ++it;
    }

  std::set<sequence*> seqs_to_skip;
  log_msg ("\nprocessing split sequences\n");
  for (std::list<sequence>::iterator it = sequences.begin ();
       it != sequences.end (); ++it)
    {
      sequence& seq = *it;

      log_sequence (seq, false);
      log_msg ("\n\n");

      if (seq.elements ().empty ())
        {
          log_msg ("skipping empty sequence\n");
          continue;
        }

      if (seq.begin<mem_match> () == seq.end<mem_match> ())
        {
          log_msg ("skipping sequence as it contains no memory accesses\n");

          // Mark all reg-uses of this sequence unoptimizable.
          for (reg_use_iter ru = seq.begin<reg_use_match> (),
                 ru_end = seq.end<reg_use_match> (); ru != ru_end; ++ru)
            (*ru)->set_optimization_enabled (false);

          continue;
        }

      log_msg ("doing adjacency analysis\n");
      seq.calculate_adjacency_info ();

      log_msg ("updating access alternatives\n");
      seq.update_access_alternatives (m_delegate,
                                      m_options.force_alt_validation,
                                      m_options.disable_alt_validation, true);

      log_msg ("updating sequence cost\n");
      seq.update_cost (m_delegate);

      log_sequence (seq, true);
      log_msg ("\n\n");

      if (seq.cost_already_minimal ())
        {
          log_msg ("costs are already minimal\n");

	  if (m_options.check_minimal_cost)
	    continue;

	  log_msg ("continuing anyway\n");
        }
    }

  log_msg ("generating new address modifications\n");
  for (std::list<sequence>::iterator it = sequences.begin ();
       it != sequences.end (); ++it)
    {
      sequence& seq = *it;
      int original_cost = seq.cost ();

      log_sequence (seq, true);
      log_msg ("\n\n");

      log_msg ("gen_address_mod\n");
      seq.gen_address_mod (m_delegate, m_options.base_lookahead_count);

      seq.update_cost (m_delegate);
      int new_cost = seq.cost ();

      log_sequence (seq, false, true);
      log_msg ("\n");

      if (new_cost >= original_cost)
	{
	  log_msg ("new_cost (%d) >= original_cost (%d)",
		   new_cost, original_cost);

	  if (m_options.check_original_cost)
            {
              log_msg ("  not modifying\n");
              seqs_to_skip.insert (&seq);
            }
	  else
	    log_msg ("  modifying anyway\n");
	}
    }

  log_msg ("\nremoving unused reg-mods\n");
  for (std::vector<ref_counting_ptr<sequence_element> >::iterator it
         = original_reg_mods.begin (); it != original_reg_mods.end ();)
    {
      if ((*it)->insn () == NULL || !(*it)->dependent_els ().empty ())
        {
          ++it;
          continue;
        }

      log_sequence_element (**it);
      log_msg ("\n");

      // Keep the reg-mod's insn if there's a sequence that doesn't get updated.
      if (std::find_if ((*it)->sequences ().begin (),
                        (*it)->sequences ().end (),
			element_is_in (seqs_to_skip))
          != (*it)->sequences ().end ())
        {
          log_msg ("reg-mod is used by a sequence that won't be updated\n");
          log_msg ("keeping insn\n");

          // In this case, all other sequences that used this reg-mod
          // can't be updated either.
          for (std::set<sequence*>::iterator el_seqs
                 = (*it)->sequences ().begin ();
               el_seqs != (*it)->sequences ().end (); ++el_seqs)
            {
              if (seqs_to_skip.find (*el_seqs) == seqs_to_skip.end ())
                {
                  log_msg ("sequence %p won't be modified either\n",
                           (const void*)*el_seqs);
                  seqs_to_skip.insert (*el_seqs);
                }
            }
        }
      else if ((*it)->insn ())
        {
          // Also keep the insn if it has other sequence elements in it.
          for (std::set<sequence*>::iterator seqs
                 = (*it)->sequences ().begin ();
               seqs != (*it)->sequences ().end (); ++seqs)
            {
              std::pair<insn_map::iterator, insn_map::iterator>
                els_in_insn = (*seqs)->elements_in_insn ((*it)->insn ());
              for (insn_map::iterator els = els_in_insn.first;
                   els != els_in_insn.second; ++els)
                {
                  if (*els->second != *it
                      // For unspecified reg-uses it doesn't matter
                      // whether the insn exists, so we can remove it.
                      && ((*els->second)->type () != type_reg_use
                          || ((reg_use*)els->second->get ())->reg_ref ()
                              != NULL))
                    {
                      log_msg ("reg-mod's insn has other elements\n");
                      log_msg ("keeping insn\n");
                      goto next;
                    }
                }
            }
          set_insn_deleted ((*it)->insn ());
        }
    next:
      it = original_reg_mods.erase (it);
    }

  log_msg ("\nupdating sequence insns\n");
  for (std::list<sequence>::iterator it = sequences.begin ();
       it != sequences.end (); ++it)
    {
      sequence& seq = *it;
      if (seqs_to_skip.find (&seq) != seqs_to_skip.end ())
        continue;

      log_sequence (seq, false);
      log_msg ("\nupdating insns\n");
      seq.update_insn_stream ();
      log_msg ("\n\n");
    }

  seqs_to_skip.clear ();
  sequences.clear ();


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
