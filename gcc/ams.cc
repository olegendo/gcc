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
#include "print-tree.h"
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

#include "ams.h"
#include "tmp_rtx.h"

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
log_options (const ams::options& opt)
{
  if (dump_file == NULL)
    return;

  log_msg ("option check_minimal_cost = %d\n", opt.check_minimal_cost);
  log_msg ("option check_original_cost = %d\n", opt.check_original_cost);
  log_msg ("option split_sequences = %d\n", opt.split_sequences);
  log_msg ("option remove_reg_copies = %d\n", opt.remove_reg_copies);
  log_msg ("base_lookahead_count = %d", opt.base_lookahead_count);
}

void
log_reg (const ams::addr_reg& reg)
{
  if (reg == ams::invalid_reg)
    log_msg ("(nil)");
  else if (reg == ams::any_reg)
    log_msg ("(reg:%s *)", GET_MODE_NAME (Pmode));
  else
    log_rtx (reg.reg_rtx ());
  if (reg.insn () != NULL)
    log_msg ("@%d", reg.insn_uid ());
}

void
log_addr_expr (const ams::addr_expr& ae)
{
  if (dump_file == NULL)
    return;

  if (ae.is_invalid ())
    {
      log_msg ("(invalid)");
      return;
    }

  if (ae.type () == ams::pre_mod)
    {
      log_msg ("@( += %"PRId64, ae.disp ());
      log_reg (ae.base_reg ());
      log_msg (" )");
      return;
    }

  if (ae.type () == ams::post_mod)
    {
      log_msg ("@( ");
      log_reg (ae.base_reg ());
      log_msg (" += %"PRId64 " )", ae.disp ());
      return;
    }

  if (ae.type () == ams::non_mod)
    {
      log_msg ("@( ");

      log_reg (ae.base_reg ());

      if (ae.index_reg () != ams::invalid_reg)
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
log_sequence_element_location (const ams::sequence_element& e)
{
  if (e.insn () != NULL)
    log_msg ("at insn %d [bb %d]", INSN_UID (e.insn ()),
				   BLOCK_FOR_INSN (e.insn ())->index);
  else
    log_msg ("at insn: ?");
}

void
log_sequence_element (const ams::sequence_element& e,
                      bool log_alternatives = true,
                      bool log_dependencies = false)
{
  if (dump_file == NULL)
    return;

  if (e.type () == ams::type_mem_load)
    log_msg ("mem_load ");
  else if (e.type () == ams::type_mem_store)
    log_msg ("mem_store ");
  else if (e.type () == ams::type_mem_operand)
    log_msg ("mem_operand ");
  else if (e.type () == ams::type_reg_mod)
    log_msg ("reg_mod ");
  else if (e.type () == ams::type_reg_barrier)
    log_msg ("reg_barrier ");
  else if (e.type () == ams::type_reg_use)
    log_msg ("reg_use ");
  else
    gcc_unreachable ();

  log_sequence_element_location (e);

  if (e.is_mem_access ())
    {
      const ams::mem_access& m = (const ams::mem_access&)e;

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

      if (m.effective_addr ().is_valid ())
        {
          log_msg ("\n  effective addr:  ");
          log_addr_expr (m.effective_addr ());
        }
    }
  else if (e.type () == ams::type_reg_mod)
    {
      const ams::reg_mod& rm = (const ams::reg_mod&)e;
      log_msg ("  set ");
      log_reg (rm.reg ());
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

      if (rm.effective_addr ().is_valid ())
        {
          log_msg ("\n  effective addr:  ");
          log_addr_expr (rm.effective_addr ());
        }
    }
  else if (e.type () == ams::type_reg_use)
    {
      const ams::reg_use& ru = (const ams::reg_use&)e;
      log_msg ("\n  use ");
      log_reg (ru.reg ());
      if (ru.reg_ref ())
        {
          log_msg (" in expr\n");
          if (ru.current_addr ().is_invalid ())
            log_rtx (*ru.reg_ref ());
          else
            log_addr_expr (ru.current_addr ());
        }

      log_msg ("\n  effective addr:   ");
      if (ru.effective_addr ().is_invalid ())
        log_msg ("unknown");
      else
        log_addr_expr (ru.effective_addr ());
    }

  if (!e.optimization_enabled ())
    log_msg ("\n  (won't be optimized)");

  if (e.cost () == ams::infinite_costs)
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
          for (ams::sequence_element::dependency_set::const_iterator it =
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
      && (e.type () == ams::type_mem_load
          || e.type () == ams::type_mem_store
          || e.type () == ams::type_mem_operand))
    {
      const ams::mem_access& m = (const ams::mem_access&)e;

      log_msg ("\n  %d alternatives:\n", m.alternatives ().size ());
      int alt_count = 0;
      for (ams::alternative_set::const_iterator
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
log_sequence (const ams::sequence& seq, bool log_alternatives = true,
              bool log_dependencies = false)
{
  if (dump_file == NULL)
    return;

  log_msg ("=====\naccess sequence ");
  dump_addr (dump_file, "", (const void*)&seq);
  log_msg (": %s\n\n", seq.empty () ? "is empty" : "");

  if (seq.empty ())
    return;

  for (ams::sequence::const_iterator it = seq.begin ();
       it != seq.end (); ++it)
    {
      log_sequence_element (*it, log_alternatives, log_dependencies);
      log_msg ("\n-----\n");
    }

  int c = seq.cost ();
  if (c == ams::infinite_costs)
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

// compensate the lack of decltype a little
template <typename T> T make_of_type (const T&)
{
  return T ();
}

template <typename T, typename A0>
T make_of_type (const T&, const A0& a0)
{
  return T (a0);
}

template <typename T, typename A0, typename A1>
T make_of_type (const T&, const A0& a0, const A1& a1)
{
  return T (a0, a1);
}

template <typename T, typename A0, typename A1, typename A2>
T make_of_type (const T&, const A0& a0, const A1& a1, const A2& a2)
{
  return T (a0, a1, a2);
}

/* Given an insn check if it contains any post/pre inc/dec mem operands and
   add the REG_INC notes accordingly.
   FIXME: Copy pasted from config/sh/sh.c.  Move to rtl utilities.  */
rtx_insn*
check_add_incdec_notes (rtx_insn* i)
{
  struct for_each_inc_dec_clb
  {
    static int func (rtx mem ATTRIBUTE_UNUSED, rtx op ATTRIBUTE_UNUSED,
		     rtx dest, rtx src ATTRIBUTE_UNUSED,
		     rtx srcoff ATTRIBUTE_UNUSED, void* arg)
    {
      gcc_assert (REG_P (dest));

      rtx_insn* i = (rtx_insn*)arg;
      if (find_regno_note (i, REG_INC, REGNO (dest)) == NULL)
	add_reg_note (i, REG_INC, dest);

      return 0;
    }
  };

  for_each_inc_dec (PATTERN (i), for_each_inc_dec_clb::func, i);
  return i;
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


// specializations of is_a_helper (in is-a.h)

template <> template <> inline bool
is_a_helper < ams::mem_access* >::test (ams::sequence_element* p)
{
  return p->type () == ams::type_mem_load
	 || p->type () == ams::type_mem_store
	 || p->type () == ams::type_mem_operand;
}

template <> template <> inline bool
is_a_helper < const ams::mem_access* >::test (ams::sequence_element* p)
{
  return p->type () == ams::type_mem_load
	 || p->type () == ams::type_mem_store
	 || p->type () == ams::type_mem_operand;
}

template <> template <> inline bool
is_a_helper < ams::mem_load* >::test (ams::sequence_element* p)
{
  return p->type () == ams::type_mem_load;
}

template <> template <> inline bool
is_a_helper < ams::mem_store* >::test (ams::sequence_element* p)
{
  return p->type () == ams::type_mem_store;
}

template <> template <> inline bool
is_a_helper < ams::mem_operand* >::test (ams::sequence_element* p)
{
  return p->type () == ams::type_mem_operand;
}

template <> template <> inline bool
is_a_helper < ams::reg_mod* >::test (ams::sequence_element* p)
{
  return p->type () == ams::type_reg_mod;
}

template <> template <> inline bool
is_a_helper < ams::reg_barrier* >::test (ams::sequence_element* p)
{
  return p->type () == ams::type_reg_barrier;
}

template <> template <> inline bool
is_a_helper < ams::reg_use* >::test (ams::sequence_element* p)
{
  return p->type () == ams::type_reg_use;
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// RTL pass class

const pass_data ams::default_pass_data =
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

const rtx ams::invalid_regno = (const rtx)0;
const rtx ams::any_regno = (const rtx)1;

const ams::addr_reg ams::invalid_reg = ams::addr_reg (ams::invalid_regno);
const ams::addr_reg ams::any_reg = ams::addr_reg (ams::any_regno);

ams::ams (gcc::context* ctx, const char* name, delegate& dlg,
          const options& opt)
: rtl_opt_pass (default_pass_data, ctx),
  m_delegate (dlg),
  m_options (opt)
{
  this->name = name;
}

ams::~ams (void)
{
}

bool ams::gate (function* /*fun*/)
{
  return optimize > 0;
}

void ams::set_options (const options& opt)
{
  m_options = opt;
}

ams::options::options (void)
{
  // maybe we can use different sets of options based on the global
  // optimization level.
  check_minimal_cost = true;
  check_original_cost = true;
  split_sequences = true;
  remove_reg_copies = false;
  force_alt_validation = false;
  disable_alt_validation = false;
  cse = false;
  cse2 = false;
  gcse = false;
  allow_mem_addr_change_new_insns = true;
  base_lookahead_count = 1;
}

ams::options::options (const char* str)
{
  *this = options (std::string (str == NULL ? "" : str));
}

ams::options::options (const std::string& str)
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
  get_int_opt (remove_reg_copies);
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
ams::addr_expr::to_rtx (void) const
{
  if (m_cached_to_rtx != NULL)
    return m_cached_to_rtx;

  rtx r = has_base_reg () ? base_reg ().reg_rtx () : NULL;

  // Add (possibly scaled) index reg.
  if (has_index_reg ())
    {
      rtx i = index_reg ().reg_rtx ();
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
ams::addr_expr::set_base_reg (addr_reg val)
{
  if (val == m_base_index_reg[0])
    return;

  m_base_index_reg[0] = val;
  m_cached_to_rtx = NULL;
}

void
ams::addr_expr::set_index_reg (addr_reg val)
{
  if (val == m_base_index_reg[1])
    return;

  m_base_index_reg[1] = val;
  m_cached_to_rtx = NULL;
}

void
ams::addr_expr::set_disp (disp_t val)
{
  if (val == m_disp)
    return;

  m_disp = m_disp_min = m_disp_max = val;
  m_cached_to_rtx = NULL;
}

void
ams::addr_expr::set_scale (scale_t val)
{
  if (val == m_scale)
    return;

  m_scale = m_scale_min = m_scale_max = val;
  m_cached_to_rtx = NULL;
}

struct ams::element_to_optimize
{
  bool operator () (const sequence_element& el) const
  {
    return (el.is_mem_access () || el.type () == type_reg_use)
	   && el.optimization_enabled ();
  }
};

struct ams::alternative_valid
{
  bool operator () (const alternative& a) const { return a.valid (); }
};

struct ams::alternative_invalid
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
ams::addr_expr::get_all_subterms (OutputIterator out) const
{
  *out++ = addr_expr ();
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
            *out++ = non_mod_addr (index_reg (), invalid_reg, 1, disp ());
        }
      else
        {
          *out++ = non_mod_addr (invalid_reg, index_reg (), scale (), 0);
          if (has_disp ())
            *out++ = non_mod_addr (invalid_reg, index_reg (), scale (), disp ());
        }
    }

  if (has_base_reg ())
    {
      *out++ = make_reg_addr (base_reg ());
      if (has_disp ())
        *out++ = non_mod_addr (base_reg (), invalid_reg, 1, disp ());

      if (has_index_reg ())
        {
          // If the index and base reg are interchangeable, put the one with
          // the smallest regno first.
          if (scale () == 1 && index_reg ()  < base_reg ())
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

ams::sequence_element::~sequence_element (void)
{
  m_sequences.clear ();
  for (sequence_element::dependency_set::iterator deps =
         m_dependencies.begin ();
       deps != m_dependencies.end (); ++deps)
    (*deps)->remove_dependent_el (this);
  m_dependencies.clear ();

  for (sequence_element::dependency_set::iterator dep_els =
         m_dependent_els.begin ();
       dep_els != m_dependent_els.end (); ++dep_els)
    (*dep_els)->remove_dependency (this);
  m_dependent_els.clear ();
}

// Return true if the element can be removed or changed by an optimization
// subpass.
bool
ams::sequence_element::can_be_optimized (void) const
{
  if (!optimization_enabled () || effective_addr ().is_invalid ())
    return false;

  for (dependency_set::const_iterator it = m_dependent_els.begin ();
       it != m_dependent_els.end (); ++it)
    {
      if (!(*it)->can_be_optimized ())
        return false;
    }
  return true;
}

bool
ams::reg_mod::can_be_optimized (void) const
{
  if (m_auto_mod_acc && !m_auto_mod_acc->optimization_enabled ())
    return false;
  return sequence_element::can_be_optimized ();
}

// Return true if the effective address of FIRST and SECOND only differs in
// the constant displacement and the difference is DIFF.
bool
ams::sequence_element
::distance_equals (const sequence_element& a, const sequence_element& b,
		   disp_t diff)
{
  if (!a.is_mem_access () || (!b.is_mem_access () && b.type () != type_reg_use))
    return false;
  if (a.effective_addr ().is_invalid () || b.effective_addr ().is_invalid ())
    return false;

  std::pair<disp_t, bool> distance = b.effective_addr () - a.effective_addr ();
  return distance.second && distance.first == diff;
}

// Return true if the effective address of FIRST and SECOND only differs in
// the constant displacement and the difference is the access size of FIRST.
bool
ams::sequence_element
::adjacent_inc (const sequence_element& a, const sequence_element& b)
{
  if (!a.is_mem_access ())
    return false;

  return distance_equals (a, b, ((const mem_access*)&a)->access_size ());
}

bool
ams::sequence_element
::not_adjacent_inc (const sequence_element& a, const sequence_element& b)
{
  return !adjacent_inc (a, b);
}

// Same as adjacent_inc, except that the displacement of SECOND should
// be the smaller one.
bool
ams::sequence_element
::adjacent_dec (const sequence_element& a, const sequence_element& b)
{
  if (!a.is_mem_access ())
    return false;

  return distance_equals (a, b, -((const mem_access*)&a)->access_size ());
}

bool
ams::sequence_element::not_adjacent_dec (
  const sequence_element& first,
  const sequence_element& second)
{
  return !adjacent_dec (first, second);
}

void
ams::mem_access::update_cost (delegate& d ATTRIBUTE_UNUSED,
                              sequence& seq ATTRIBUTE_UNUSED,
                              sequence::iterator el_it ATTRIBUTE_UNUSED)
{
  if (effective_addr ().is_invalid ())
    {
      set_cost (0);
      return;
    }

  if (m_current_alt == alternatives ().end ())
    {
      gcc_assert (!optimization_enabled ());
      set_cost (0);
    }
  else
    set_cost (m_current_alt->cost ());
}

void
ams::reg_mod::update_cost (delegate& d, sequence& seq,
                           sequence::iterator el_it)
{
  if (current_addr ().is_invalid ())
    {
      set_cost (0);
      return;
    }

  int cost = 0;
  const addr_expr& ae = current_addr ();

  // Scaling costs
  if (ae.has_no_base_reg () && ae.has_index_reg () && ae.scale () != 1)
    cost += d.addr_reg_mod_cost (reg ().reg_rtx (),
			tmp_rtx<MULT> (Pmode, ae.index_reg ().reg_rtx (),
				       tmp_rtx<CONST_INT> (ae.scale ())),
			seq, el_it);

  // Costs for adding or subtracting another reg
  else if (ae.has_no_disp () && std::abs (ae.scale ()) == 1
           && ae.has_base_reg () && ae.has_index_reg ())
    cost += d.addr_reg_mod_cost (reg ().reg_rtx (),
				 tmp_rtx<PLUS> (Pmode,
                                                ae.index_reg ().reg_rtx (),
                                                ae.base_reg ().reg_rtx ()),
				 seq, el_it);

  // Constant displacement costs
  else if (ae.has_base_reg () && ae.has_no_index_reg () && ae.has_disp ())
    cost += d.addr_reg_mod_cost (reg ().reg_rtx (),
				 tmp_rtx<PLUS> (Pmode, ae.base_reg ().reg_rtx (),
						tmp_rtx<CONST_INT> (ae.disp ())),
				 seq, el_it);

  // Constant loading costs
  else if (ae.has_no_base_reg () && ae.has_no_index_reg ())
    cost += d.addr_reg_mod_cost (reg ().reg_rtx (),
                                 tmp_rtx<CONST_INT> (ae.disp ()),
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

  if (ae.regs_empty ())
    return;
  const addr_reg& reused_reg = *(ae.regs_begin ());
  // There's no cloning cost for reg-mods that set the reg to itself.
  if (reused_reg == reg ())
    return;
  add_cloning_cost (reused_reg, d, seq, el_it);
}

void
ams::reg_use::update_cost (delegate& d, sequence& seq,
                           sequence::iterator el_it)
{
  set_cost (0);
  if (current_addr ().is_invalid ())
    return;

  // Get the cost of the constant displacement.
  if (current_addr ().has_disp ())
    set_cost (d.addr_reg_mod_cost (
      m_reg.reg_rtx (), tmp_rtx<PLUS> (
        m_reg.mode (), current_addr ().base_reg ().reg_rtx (),
        tmp_rtx<CONST_INT> (current_addr ().disp ())),
      seq, el_it));

  if (!current_addr ().regs_empty ())
    add_cloning_cost (*current_addr ().regs_begin (), d, seq, el_it);
}

void
ams::sequence_element::add_cloning_cost (const addr_reg& reused_reg,
                                         delegate& d, sequence& seq,
                                         sequence::iterator el_it)
{
  // Find the reg-mod of the reused register.
  reg_mod* reused_rm = NULL;
  for (std::set<ams::sequence_element*>::iterator it =
         dependencies ().begin (); it != dependencies ().end (); ++it)
    {
      if (reg_mod* rm = dyn_cast<reg_mod*> (*it))
	if (rm->reg () == reused_reg)
	  {
	    reused_rm = rm;
	    break;
	  }
    }
  gcc_assert (reused_rm != NULL);

  // Find the first element that also uses the reused register.
  for (std::set<ams::sequence_element*>::iterator it =
         reused_rm->dependent_els ().begin ();
       it != reused_rm->dependent_els ().end (); ++it)
    {
      reg_mod* rm = dyn_cast<reg_mod*> (*it);
      if (rm == NULL || rm->current_addr ().is_invalid ()
          || rm->current_addr ().regs_empty ())
        continue;
      const addr_expr& addr = rm->current_addr ();

      const addr_reg& dep_reused_reg = *(addr.regs_begin ());

      if (reused_reg == dep_reused_reg)
        {
          // If this reg-mod is the first to use the reg, there's
          // no need to clone it.
          if (*it == this)
              return;

          // Otherwise, we'll have to apply cloning costs.
          adjust_cost (d.addr_reg_clone_cost (reused_reg.reg_rtx (),
                                              seq, el_it));
          return;
        }
    }
}

const unsigned ams::sequence_element::invalid_id = ~0u;
const ams::adjacent_chain_info ams::sequence_element::g_no_incdec_chain;
bool ams::mem_access::allow_new_insns = true;

// Used to keep track of shared address (sub)expressions
// during sequence splitting.
class ams::shared_term
{
public:
  shared_term (void) : m_score (0), m_sharing_els (), m_new_seq (NULL) { }

  // The elements that share this term.
  std::vector<sequence_element*>& sharing_els () { return m_sharing_els; }

  // The term's newly created access sequence.
  sequence* new_seq (void) const { return m_new_seq; }
  void set_new_seq (sequence *s) {  m_new_seq = s; }

  static bool compare (const shared_term* a, const shared_term* b)
  { return a->score () > b->score (); }

  // A score that's used to determine which shared expressions should
  // be used for splitting access sequences.  A higher score means that
  // the shared term is more likely to be selected as a base for a
  // new sequence.
  unsigned int score (void) const { return m_score; }

  unsigned int calc_score (const addr_expr& term)
  {
    if (term.is_invalid ())
      return m_score = 0;

    m_score = 10;

    // Displacement-only terms with large displacements are
    // represented with a constant 0 address.
    if (term.has_no_base_reg () && term.has_no_index_reg ()
	&& term.has_no_disp ())
      m_score += 2;

    if (term.has_base_reg ())
      m_score += 2;
    if (term.has_index_reg ())
      {
	m_score += 2;
	if (term.scale () != 1)
	  ++m_score;
      }
    if (term.has_disp ())
      ++m_score;

    return m_score = m_score * m_sharing_els.size ();
  }

private:
  unsigned int m_score;
  std::vector<sequence_element*> m_sharing_els;
  sequence* m_new_seq;
};

// The return type of find_reg_value. Stores the reg's value, the modifying
// insn and the modifying mem access in case of auto-mod accesses.
class ams::find_reg_value_result
{
public:
  addr_reg reg;
  rtx value;
  rtx_insn* insn;
  mem_access* acc;
  machine_mode acc_mode;
  bool is_auto_mod;
  reg_mod* rm;

  find_reg_value_result (addr_reg r, rtx v, rtx_insn* i)
  : reg (r), value (v), insn (i), acc (NULL), acc_mode (Pmode),
    is_auto_mod (false), rm (NULL)
  {
  }

  find_reg_value_result (addr_reg r, rtx v, rtx_insn* i, machine_mode m)
  : reg (r), value (v), insn (i), acc (NULL), acc_mode (m),
    is_auto_mod (true), rm (NULL)
  {
  }

  find_reg_value_result (addr_reg r, rtx v, rtx_insn* i, mem_access* a)
  : reg (r), value (v), insn (i), acc (a), acc_mode (a->mach_mode ()),
    is_auto_mod (true), rm (NULL)
  {
  }

  find_reg_value_result (reg_mod* r)
  : reg (addr_reg (r->reg ().reg_rtx ())), value (r->value ()),
    insn (r->insn ()), acc (r->auto_mod_acc ()),
    acc_mode (r->auto_mod_acc () != NULL ? r->auto_mod_acc ()->mach_mode ()
                                         : Pmode),
    is_auto_mod (r->auto_mod_acc () != NULL), rm (r)
  {
  }
};

// Return all the start addresses that could be used to arrive at END_ADDR.
template <typename OutputIterator> void
ams::start_addr_list::get_relevant_addresses (const addr_expr& end_addr,
                                              OutputIterator out)
{
  // Constant displacements can always be used as start addresses.
  out = std::copy (m_const_addresses.begin (), m_const_addresses.end (), out);

  // Addresses containing registers might be used if they have a
  // register in common with the end address.
  for (addr_expr::regs_const_iterator ri = end_addr.regs_begin ();
       ri != end_addr.regs_end (); ++ri)
    {
      std::pair <reg_map::iterator, reg_map::iterator> r =
		m_reg_addresses.equal_range (*ri);

      for (reg_map::iterator it = r.first; it != r.second; ++it)
        *out++ = it->second;
    }
}

// Add START_ADDR to the list of available start addresses.
void
ams::start_addr_list::add (reg_mod* start_addr)
{
  const addr_expr& addr = start_addr->effective_addr ().is_invalid ()
			  ? make_reg_addr (start_addr->reg ())
			  : start_addr->effective_addr ();

  // If the address has a base or index reg, add it to M_REG_ADDRESSES.
  // Otherwise, add it to the constant list.

  for (addr_expr::regs_const_iterator ri = addr.regs_begin ();
       ri != addr.regs_end (); ++ri)
    {
      m_reg_addresses.insert (std::make_pair (*ri, start_addr));
    }

  if (addr.regs_empty ())
    m_const_addresses.push_back (start_addr);
}

// Remove START_ADDR from the list of available start addresses.
void
ams::start_addr_list::remove (reg_mod* start_addr)
{
  const addr_expr& addr = start_addr->effective_addr ().is_invalid ()
			  ? make_reg_addr (start_addr->reg ())
			  : start_addr->effective_addr ();
  for (addr_expr::regs_const_iterator ri = addr.regs_begin ();
       ri != addr.regs_end (); ++ri)
    {
      std::pair <reg_map::iterator, reg_map::iterator> r =
		m_reg_addresses.equal_range (*ri);

      for (reg_map::iterator it = r.first; it != r.second; ++it)
	if (it->second == start_addr)
	  {
	    m_reg_addresses.erase (it);
	    break;
	  }
    }

  if (addr.regs_empty ())
    m_const_addresses.remove (start_addr);
}

// Split the access sequence pointed to by SEQ_IT into multiple sequences,
// grouping the accesses that have common terms in their effective address
// together.  Return an iterator to the sequence that comes after the newly
// inserted sequences.
std::list<ams::sequence>::iterator
ams::sequence::split (std::list<sequence>::iterator seq_it,
                      std::list<sequence>& sequences)
{
  typedef std::map<sequence_element*, sequence*> element_to_seq_map;
  typedef std::map<addr_expr, shared_term, addr_expr::compare> shared_term_map;

  // Shows which new sequence each sequence element should go into.
  element_to_seq_map element_new_seqs;
  std::vector<sequence*> new_seqs;

  shared_term_map shared_terms;
  sequence& seq = *seq_it;

  // Find all terms that appear in the effective addresses of the mem accesses
  // and reg uses.  These will be used as potential bases for new sequences.
  std::vector<addr_expr> terms;
  for (iterator el = seq.begin (); el != seq.end (); ++el)
    {
      if (!el->is_mem_access () && el->type () != type_reg_use)
        continue;

      addr_expr addr = el->effective_addr ();

      // If a reg-use's effective address isn't known, group it
      // together with other elements that use its register.
      if (addr.is_invalid () && el->type () == type_reg_use)
        addr = make_reg_addr (((reg_use*)&*el)->reg ());

      terms.clear ();
      addr.get_all_subterms (std::back_inserter (terms));
      for (std::vector<addr_expr>::iterator it = terms.begin ();
           it != terms.end (); ++it)
        {
          if (it->is_valid () && it->regs_empty ())
            {
	      // If a displacement-only term fits into an address alternative,
	      // it's not likely to be useful as a base term, so skip those.
	      // If it doesn't fit, treat them as one base term instead of
	      // having a separate term for each constant.
	      if (mem_access* ma = dyn_cast<mem_access*> (&*el))
		{
		  if (ma->displacement_fits_alternative (it->disp ()))
		    continue;
		  else
		    *it = make_const_addr ((disp_t)0);
		}
	      else
		continue;
            }

	  shared_terms[*it].sharing_els ().push_back (&*el);
        }
    }

  // Sort the shared terms by their score.
  std::vector<shared_term*> sorted_terms;
  sorted_terms.reserve (shared_terms.size ());
  for (shared_term_map::iterator it = shared_terms.begin ();
       it != shared_terms.end (); ++it)
    {
      it->second.calc_score (it->first);
      sorted_terms.push_back (&(it->second));
    }
  std::sort (sorted_terms.begin (), sorted_terms.end (), shared_term::compare);

  // Create new sequences for the shared terms with the highest scores
  // and mark the accesses' new sequences in ELEMENT_NEW_SEQS appropriately.
  // FIXME: use linear allocator to avoid allocations for temporary set.
  std::set<sequence_element*> inserted_els;
  for (std::vector<shared_term*>::iterator it
         = sorted_terms.begin (); it != sorted_terms.end (); ++it)
    {
      shared_term& term = **it;
      for (std::vector<sequence_element*>::iterator el =
	   term.sharing_els ().begin (); el != term.sharing_els ().end (); ++el)
	if (inserted_els.insert (*el).second)
	  {
	    if (!term.new_seq ())
              {
                term.set_new_seq (
                  &(*sequences.insert (
                    seq_it, sequence (seq, false))));
                new_seqs.push_back (term.new_seq ());
              }
	    element_new_seqs[*el] = term.new_seq ();
	  }
    }

  // Add each mem access and reg use from the original sequence to the
  // appropriate new sequence based on ELEMENT_NEW_SEQS.  Also add their
  // dependencies.
  for (reverse_iterator it = seq.rbegin (); it != seq.rend (); ++it)
    {
      element_to_seq_map::iterator found = element_new_seqs.find (&*it);
      if (found != element_new_seqs.end ())
	split_1 (*found->second, *it.base ());
    }

  // Add to the split sequences those reg-mods that modify one of their
  // address regs, along with their dependencies.
  for (trv_iterator<deref<std::vector<sequence*>::iterator> >
	s (new_seqs.begin ()), s_end (new_seqs.end ()); s != s_end; ++s)
    {
      // Since adding new elements might add more address regs,
      // repeat until no new elements have been added.
      while (1)
        {
          unsigned insert_count = 0;
          for (reg_mod_iter rm (seq.begin<reg_mod_match> ()),
                 rm_end (seq.end<reg_mod_match> ()); rm != rm_end; ++rm)
            {
              if (s->addr_regs ().find (rm->reg ()) != s->addr_regs ().end ())
                insert_count +=
                  split_1 (*s, ref_counting_ptr<sequence_element> (&*rm));
            }
          if (insert_count == 0)
            break;
        }
    }

  // Remove the old sequence and return the next element after the
  // newly inserted sequences.
  return sequences.erase (seq_it);
}

// Internal function of access_sequence::split.  Add EL and its dependencies
// to SEQ.  Return the number of unique elements inserted.
int
ams::sequence::split_1 (sequence& seq,
                        const ref_counting_ptr<sequence_element>& el)
{
  unsigned insert_count = 0;
  unsigned prev_size = seq.size ();

  seq.insert_unique (el);
  if (prev_size < seq.size ())
    ++insert_count;

  for (sequence_element::dependency_set::iterator it =
         el->dependencies ().begin ();
       it != el->dependencies ().end (); ++it)
    insert_count += split_1 (seq, ref_counting_ptr<sequence_element> (*it));
  return insert_count;
}

ams::sequence&
ams::sequence::operator = (const sequence& other)
{
  m_insn_el_map = other.m_insn_el_map;
  m_original_seq = other.m_original_seq;

  for (iterator els = begin (); els != end ();)
    {
      els->sequences ().erase (this);
      els = remove_element (els, false);
    }

  for (const_iterator els = other.begin (); els != other.end (); ++els)
    insert_element (*els.base (), end ());

  return *this;
}

// Find all mem accesses in the insn I and add them to the sequence.
void
ams::sequence::find_mem_accesses (rtx_insn* i)
{
  static_vector<std::pair<rtx*, element_type>, 16> mems;
  find_mem_accesses_1 (PATTERN (i), std::back_inserter (mems));
  std::sort (mems.begin (), mems.end (), sort_found_mems);

  for (static_vector<std::pair<rtx*, element_type>, 16>::iterator
         it = mems.begin (), prev = mems.begin ();
       it != mems.end (); ++it)
    {
      static_vector<std::pair<rtx*, element_type>, 16>::iterator next =
        stdx::next (it);

      if (REGNO (*it->first) != REGNO (*prev->first))
        prev = it;
      if (next == mems.end () || REGNO (*it->first) != REGNO (*next->first))
        {
          ref_counting_ptr<mem_access> acc;
          rtx* mem_ref = it->first;
          element_type type = it->second;

          if (it != prev)
            {
              static_vector<rtx*, 16> v;
              for (static_vector<std::pair<rtx*, element_type>, 16>
                     ::iterator refs = prev; refs != next; ++refs)
                v.push_back (refs->first);
              acc = make_ref_counted<mem_operand> (i, v);
            }
          else if (type == type_mem_load)
            acc = make_ref_counted<mem_load> (i, mem_ref);
          else if (type == type_mem_store)
            acc = make_ref_counted<mem_store> (i, mem_ref);
          else
            gcc_unreachable ();

          acc->set_mach_mode (GET_MODE (*mem_ref));
          acc->set_current_addr_rtx (XEXP (*mem_ref, 0));
          acc->set_current_addr (rtx_to_addr_expr (XEXP (*mem_ref, 0),
                                                   GET_MODE (*mem_ref)));
          insert_element (acc, end ());
        }
    }
}

// The recursive part of find_mem_accesses. Find all mem accesses
// in X and add them to OUT, along with their type (mem_load or mem_store).
// TYPE indicates the type of the next mem that we find.
template <typename OutputIterator> void
ams::sequence::find_mem_accesses_1 (rtx& x, OutputIterator out,
                                    element_type type)
{
  switch (GET_CODE (x))
    {
    case MEM:
      *out++ = std::make_pair (&x, type);
      return;

    case PARALLEL:
    case UNSPEC:
    case UNSPEC_VOLATILE:
      for (int j = 0; j < XVECLEN (x, 0); j++)
        find_mem_accesses_1 (XVECEXP (x, 0, j), out, type);
      break;

    case SET:
      find_mem_accesses_1 (SET_DEST (x), out, type_mem_store);
      find_mem_accesses_1 (SET_SRC (x), out, type_mem_load);
      break;

    case CALL:
      find_mem_accesses_1 (XEXP (x, 0), out, type_mem_load);
      break;

    default:
      if (UNARY_P (x) || ARITHMETIC_P (x))
        {
          for (int j = 0; j < GET_RTX_LENGTH (GET_CODE (x)); j++)
            find_mem_accesses_1 (XEXP (x, j), out, type);
        }
      break;
    }
}

// Comparison function used to sort the found mems in find_mem_accesses.
bool
ams::sequence::sort_found_mems (const std::pair<rtx*, element_type>& a,
                                const std::pair<rtx*, element_type>& b)
{
  return REGNO (*a.first) < REGNO (*b.first);
}

// Add a reg mod for every insn that modifies an address register.
void
ams::sequence::find_addr_reg_mods (void)
{
  basic_block seq_bb = bb ();
  regno_t prev_regno = -1;
  for (addr_reg_map::iterator it = m_addr_regs.begin ();
       it != m_addr_regs.end (); ++it)
    {
      rtx_insn* last_insn = BB_END (seq_bb);
      reg_mod* last_reg_mod = NULL;
      const addr_reg& reg = it->first;

      if (reg.regno () == prev_regno)
        continue;
      prev_regno = reg.regno ();

      while (1)
	{
          reg_mod* new_reg_mod;
	  const find_reg_value_result prev =
            find_reg_value (reg.reg_rtx (), last_insn, g_insn_el_map ());

          if (prev.rm != NULL)
            {
              new_reg_mod = prev.rm;
              last_insn = prev_nonnote_insn_bb (prev.rm->insn ());
            }
          else
            {
              addr_expr reg_curr_addr = prev.is_auto_mod
                ? make_reg_addr (reg)
		: rtx_to_addr_expr (prev.value);

              iterator inserted = insert_unique (
                make_ref_counted<reg_mod> (prev.insn, prev.reg, prev.value,
                                           reg_curr_addr));
              new_reg_mod = as_a<reg_mod*> (&*inserted);

              if (new_reg_mod->effective_addr ().is_invalid ())
                {
                  // Find the reg-mod's effective address.

                  addr_expr reg_effective_addr;
                  if (prev.value != NULL_RTX && REG_P (prev.value)
                      && reg == prev.value)
                    {
                      rtx_insn* insn = BB_HEAD (seq_bb);
                      if (single_pred_p (seq_bb))
                        {
                          // Trace back the reg's value through the previous BB.
                          reg_effective_addr = rtx_to_addr_expr (
                            prev.value, prev.is_auto_mod ? prev.acc_mode : Pmode,
                            this, BB_END (single_pred (seq_bb)),
                            single_pred (seq_bb));
                          if (reg_effective_addr.is_invalid ())
                            reg_effective_addr = make_reg_addr (
                              addr_reg (reg.reg_rtx (), insn));
                        }
                      else
                        reg_effective_addr = make_reg_addr (
                          addr_reg (reg.reg_rtx (), insn));

                      m_start_addr_list.remove (new_reg_mod);
                      new_reg_mod->set_effective_addr (reg_effective_addr);
                      m_start_addr_list.add (new_reg_mod);
                    }
                  else
                    {
                      reg_effective_addr = rtx_to_addr_expr (
                        prev.value, prev.is_auto_mod ? prev.acc_mode : Pmode,
                        this, new_reg_mod);

                      if (reg_curr_addr.is_invalid ()
                          || reg_effective_addr.is_invalid ())
                        new_reg_mod->set_optimization_disabled ();

                      if (reg_effective_addr.is_invalid ())
                        reg_effective_addr = make_reg_addr (
                          addr_reg (reg.reg_rtx (), prev.insn));

                      m_start_addr_list.remove (new_reg_mod);
                      new_reg_mod->set_auto_mod_acc (prev.acc);
                      new_reg_mod->set_effective_addr (reg_effective_addr);
                      m_start_addr_list.add (new_reg_mod);
                    }
                }

              last_insn = prev_nonnote_insn_bb (prev.insn);

              if (prev.value != NULL_RTX && REG_P (prev.value)
                  && reg == prev.value)
                break;
            }

          if (last_reg_mod != NULL)
            {
              last_reg_mod->add_dependency (new_reg_mod);
              new_reg_mod->add_dependent_el (last_reg_mod);
            }
	  last_reg_mod = new_reg_mod;
	}
    }
}

// Add a reg use for every use of an address register that's not a
// memory access or address reg modification.
void
ams::sequence::find_addr_reg_uses (void)
{
  std::set<addr_reg> visited_addr_regs;
  std::map<addr_reg, reg_mod*> live_addr_regs;
  std::vector<rtx*> reg_use_refs;

  for (reg_mod_iter rm (begin<reg_mod_match> ()),
         rm_end (end<reg_mod_match> ()); rm != rm_end; ++rm)
    {
      if (rm->insn () != NULL)
        break;
      visited_addr_regs.insert (rm->reg ());
      live_addr_regs[rm->reg ()] = &*rm;
    }

  for (rtx_insn* i = start_insn (); i != NULL_RTX; i = next_nonnote_insn_bb (i))
    {
      if (!INSN_P (i) || DEBUG_INSN_P (i))
	continue;

      regno_t prev_regno = -1;
      for (std::set<addr_reg>::iterator regs = visited_addr_regs.begin ();
           regs != visited_addr_regs.end (); ++regs)
        {
          if (regs->regno () == prev_regno)
            continue;
          prev_regno = regs->regno ();

          // Find all references to the reg in this insn.
          reg_use_refs.clear ();
          find_addr_reg_uses_1 (regs->reg_rtx (), PATTERN (i),
                                std::back_inserter (reg_use_refs));

          // If no refs were found and the reg is used by a funcall,
          // create an unspecified reg use.
          if (reg_use_refs.empty () && CALL_P (i)
              && live_addr_regs.find (*regs) != live_addr_regs.end ())
            {
              // Check if the reg is used directly.
              if (find_reg_fusage (i, USE, regs->reg_rtx ()))
                reg_use_refs.push_back (NULL);
              else
                {
                  // Check if the reg is used as part of a mem RTX.
                  for (rtx link = CALL_INSN_FUNCTION_USAGE (i); link != NULL;
                       link = XEXP (link, 1))
                    {
                      if (GET_CODE (XEXP (link, 0)) != USE
                          || !MEM_P (XEXP (XEXP (link, 0), 0)))
                        continue;

                      rtx mem = XEXP (XEXP (link, 0), 0);
                      subrtx_var_iterator::array_type array;
                      FOR_EACH_SUBRTX_VAR (it, array, mem, NONCONST)
                        if (REG_P (*it) && *regs == *it)
                          {
                            reg_use_refs.push_back (NULL);
                            goto cont;
                          }
                    }
                }
            }
        cont:

          // Create a reg use for each reference that was found.
          for (std::vector<rtx*>::iterator it = reg_use_refs.begin ();
               it != reg_use_refs.end (); ++it)
            {
              rtx* use_ref = *it;

              if (use_ref == NULL)
                {
                  reg_use* new_reg_use = as_a<reg_use*> (&*insert_unique (
                    make_ref_counted<reg_use> (i, *regs)));
                  std::map<addr_reg, reg_mod*>::iterator found =
                    live_addr_regs.find (*regs);
                  if (found != live_addr_regs.end ())
                    {
                      reg_mod* rm = found->second;
                      new_reg_use->set_effective_addr (rm->effective_addr ());
                      new_reg_use->add_dependency (rm);
                      rm->add_dependent_el (new_reg_use);
                    }
                  continue;
                }

              addr_expr use_expr = rtx_to_addr_expr (*use_ref);
	      reg_use* new_reg_use = as_a<reg_use*> (&*insert_unique (
		    make_ref_counted<reg_use> (i, use_expr.base_reg (),
                                               use_ref, use_expr)));

	      addr_expr effective_addr = rtx_to_addr_expr (regs->reg_rtx (),
                                                           Pmode,
                                                           this, new_reg_use);

              // If the use ref also contains a constant displacement,
              // add that to the effective address.
              if (effective_addr.is_valid () && use_ref
                  && (UNARY_P (*use_ref) || ARITHMETIC_P (*use_ref)))
                {
                  effective_addr = check_make_non_mod_addr (
                    effective_addr.base_reg (),
                    effective_addr.index_reg (),
                    effective_addr.scale (),
                    effective_addr.disp () + use_expr.disp ());
                }
              new_reg_use->set_effective_addr (effective_addr);
            }
        }

      // Update the visited and live address regs list.
      std::pair<insn_map::iterator, insn_map::iterator> els_in_insn =
		elements_in_insn (i);
      for (insn_map::iterator els = els_in_insn.first;
	   els != els_in_insn.second; ++els)
	if (reg_mod* rm = dyn_cast<reg_mod*> (&*els->second))
	  {
	    visited_addr_regs.insert (rm->reg ());
	    live_addr_regs[rm->reg ()] = rm;
	  }

      for (std::map<addr_reg, reg_mod*>::iterator it =
	     live_addr_regs.begin (); it != live_addr_regs.end ();)
	{
	  if (find_regno_note (i, REG_DEAD, (it->first.regno ())))
	    live_addr_regs.erase (it++);
	  else
	    ++it;
	}
    }

  // Add unspecified reg uses for regs that are still alive at the
  // end of the sequence.
  for (std::map<addr_reg, reg_mod*>::iterator it =
         live_addr_regs.begin (); it != live_addr_regs.end (); ++it)
    {
      const addr_reg& reg = it->first;
      reg_mod* rm = it->second;
      reg_use* new_reg_use = as_a<reg_use*> (&*insert_element (
       make_ref_counted<reg_use> ((rtx_insn*)NULL, reg), end ()));
      new_reg_use->set_effective_addr (rm->effective_addr ());
      new_reg_use->add_dependency (rm);
      rm->add_dependent_el (new_reg_use);
    }
}

// A structure used for tracking and reverting modifications
// to access sequences.
class ams::mod_tracker
{
public:
  typedef std::vector<std::pair <sequence_element*,
                                 std::pair<addr_expr,
                                           alternative_set::const_iterator> > >
    addr_changed_list;
  mod_tracker (sequence& seq, std::set<reg_mod*>& used_reg_mods,
               std::map<addr_reg, reg_mod*>& visited_reg_mods)
    : m_seq (seq), m_used_reg_mods (used_reg_mods),
      m_visited_reg_mods (visited_reg_mods)
  {
    m_dependent_els.reserve (8);
    m_inserted_reg_mods.reserve (8);
    m_use_changed_reg_mods.reserve (4);
    m_visited_changed_reg_mods.reserve (4);
    m_addr_changed_els.reserve (4);
  }

  // Undo all the changes that were recorded.
  void reset_changes (void);

  // Mark RM as visited.
  void visit_reg_mod (reg_mod* rm);

  // Mark RM as used.
  void use_reg_mod (reg_mod* rm);

  // Insert RM into the sequence.
  sequence::iterator insert_reg_mod (ref_counting_ptr<reg_mod> rm,
                                     sequence::iterator insert_before);

  // Make two elements dependent.
  void create_dependency (sequence_element* dependency,
                          sequence_element* dependent_el);

  // Clear all recorded changes.
  void clear (void);

  // Return the list of sequence elements whose address changed, along
  // with their previous values.
  addr_changed_list&
  addr_changed_els (void) { return m_addr_changed_els; }

private:
  sequence& m_seq;
  std::vector<std::pair<sequence_element*,
                        sequence_element*> > m_dependent_els;
  std::vector<sequence::iterator> m_inserted_reg_mods;
  std::vector<reg_mod*> m_use_changed_reg_mods;
  std::vector<std::pair<addr_reg, reg_mod*> >  m_visited_changed_reg_mods;
  addr_changed_list m_addr_changed_els;
  std::set<reg_mod*>& m_used_reg_mods;
  std::map<addr_reg, reg_mod*>& m_visited_reg_mods;
};

// Undo all the changes that were recorded.
void ams::mod_tracker::reset_changes (void)
{
  for (std::vector<std::pair<sequence_element*, sequence_element*> >::
         reverse_iterator it = m_dependent_els.rbegin ();
       it != m_dependent_els.rend (); ++it)
    {
      it->second->remove_dependency (it->first);
      it->first->remove_dependent_el (it->second);
    }

  for (std::vector<reg_mod*>::reverse_iterator it =
         m_use_changed_reg_mods.rbegin ();
       it != m_use_changed_reg_mods.rend (); ++it)
    m_used_reg_mods.erase (*it);

  for (std::vector<std::pair<addr_reg, reg_mod*> >::reverse_iterator
         it = m_visited_changed_reg_mods.rbegin ();
       it != m_visited_changed_reg_mods.rend (); ++it)
    {
      if (it->second == NULL)
        m_visited_reg_mods.erase (it->first);
      else
        m_visited_reg_mods[it->first] = it->second;
    }

  for (addr_changed_list::reverse_iterator it = m_addr_changed_els.rbegin ();
       it != m_addr_changed_els.rend (); ++it)
    {
      sequence_element* el = it->first;
      addr_expr& prev_addr = it->second.first;
      alternative_set::const_iterator prev_alt = it->second.second;

      if (mem_access* ma = dyn_cast<mem_access*> (el))
        ma->set_current_addr_and_alt (prev_addr, prev_alt);
      else if (reg_use* ru = dyn_cast<reg_use*> (el))
        {
          ru->set_reg (prev_addr.base_reg ());
          ru->set_current_addr (prev_addr);
        }
      else
        gcc_unreachable ();
    }

  for (std::vector<sequence::iterator>::reverse_iterator it
         = m_inserted_reg_mods.rbegin ();
       it != m_inserted_reg_mods.rend (); ++it)
    {
      m_seq.remove_element (*it);
      m_used_reg_mods.erase ((reg_mod*)&**it);
    }

  clear ();
}

// Mark RM as visited.
void ams::mod_tracker::visit_reg_mod (reg_mod* rm)
{
  std::map<addr_reg, reg_mod*>::iterator prev =
    m_visited_reg_mods.find (rm->reg ());

  if (prev == m_visited_reg_mods.end ())
    {
      m_visited_changed_reg_mods.push_back (
        std::make_pair (rm->reg (), (reg_mod*)NULL));
      m_visited_reg_mods[rm->reg ()] = rm;
    }
  else
    {
      m_visited_changed_reg_mods.push_back (
        std::make_pair (rm->reg (), prev->second));
      prev->second = rm;
    }
}

// Mark RM as used.
void ams::mod_tracker::use_reg_mod (reg_mod* rm)
{
  m_used_reg_mods.insert (rm);
  m_use_changed_reg_mods.push_back (rm);
}

// Insert RM into the sequence. Return an iterator pointing to RM.
ams::sequence::iterator
ams::mod_tracker::insert_reg_mod (ref_counting_ptr<reg_mod> rm,
                                  sequence::iterator insert_before)
{
  sequence::iterator inserted_el = m_seq.insert_element (rm, insert_before);
  m_inserted_reg_mods.push_back (inserted_el);
  visit_reg_mod ((reg_mod*)&*inserted_el);
  return inserted_el;
}

// Make two elements dependent.
void ams::mod_tracker::create_dependency (sequence_element* dependency,
                                          sequence_element* dependent_el)
{
  dependent_el->add_dependency (dependency);
  dependency->add_dependent_el (dependent_el);
  m_dependent_els.push_back (
    std::make_pair (dependency, dependent_el));
}

// Clear all recorded changes.
void ams::mod_tracker::clear (void)
{
  m_dependent_els.clear ();
  m_use_changed_reg_mods.clear ();
  m_visited_changed_reg_mods.clear ();
  m_addr_changed_els.clear ();
  m_inserted_reg_mods.clear ();
}

// Generate the address modifications needed to arrive at the
// addresses in the sequence.
bool
ams::sequence::gen_address_mod (delegate& dlg, int base_lookahead)
{
  bool success = true;

  // Remove the sequence's original reg-mods.
  for (reg_mod_iter rm (begin<reg_mod_match> ()),
       rm_end (end<reg_mod_match> ()); rm != rm_end; )
    {
      if (rm->insn () == NULL || !rm->can_be_optimized ())
        {
          // If an auto-mod mem access' reg-mod can't be removed, the
          // access shouldn't be changed either.
          if (rm->auto_mod_acc ())
            rm->auto_mod_acc ()->set_optimization_disabled ();

          ++rm;
          continue;
        }

      rm = reg_mod_iter (remove_element (rm.base ()), rm_end.base ().base ());
    }

  // FIXME: use linear allocator to avoid allocations for temporary set.
  std::set<reg_mod*> used_reg_mods;
  std::map<addr_reg, reg_mod*> visited_reg_mods;
  typedef filter_iterator<iterator, element_to_optimize> el_opt_iter;
  iterator prev_el = begin ();
  unsigned next_tmp_regno = max_reg_num ();

  for (el_opt_iter els = begin<element_to_optimize> (),
       els_end = end<element_to_optimize> (); els != els_end; ++els)
    {
      // Mark the reg-mods before the current element as visited.
      for (iterator it = prev_el; it != els; ++it)
        if (reg_mod* rm = dyn_cast<reg_mod*> (&*it))
          visited_reg_mods[rm->reg ()] = rm;

      prev_el = els;

      int cost = gen_address_mod_1 (
        els, dlg, used_reg_mods, visited_reg_mods, &next_tmp_regno,
        base_lookahead + dlg.adjust_lookahead_count (*this, els));

      if (cost == infinite_costs)
        success = false;
    }

  std::map<addr_reg, rtx> reg_replacements;
  for (reg_mod_iter rm (begin<reg_mod_match> ()),
       rm_end (end<reg_mod_match> ()); rm != rm_end; )
    {
      // Remove the unused reg <- constant copies that might have been
      // added while trying different address calculations.
      if (rm->insn () == NULL && rm->current_addr ().is_valid ()
          && rm->current_addr ().regs_empty () && rm->dependent_els ().empty ())
	{
          rm = reg_mod_iter (remove_element (rm.base ()), rm_end.base ().base ());
          continue;
        }

      // Replace the temporary reg rtx-es of the inserted reg-mods
      // with permanent ones.
      if (rm->reg () == rm->tmp_reg ())
        {
          rtx new_reg_rtx = gen_reg_rtx (rm->reg ().mode ());
          reg_replacements[rm->reg ()] = new_reg_rtx;
          rm->set_reg_rtx (new_reg_rtx);

          ++m_addr_regs[rm->reg ()];
        }

      ++rm;
    }

  // Replace the temporary reg rtx-es in the elements' addresses.
  for (iterator el = begin (); el != end (); ++el)
    {
      addr_expr addr = el->current_addr ();

      if (reg_mod* rm = dyn_cast<reg_mod*> (&*el))
        m_start_addr_list.remove (rm);

      for (addr_expr::regs_iterator ri = addr.regs_begin ();
           ri != addr.regs_end (); ++ri)
        {
          std::map<addr_reg, rtx>::iterator found =
            reg_replacements.find (*ri);
          if (found != reg_replacements.end ())
            *ri = found->second;
        }

      if (reg_mod* rm = dyn_cast<reg_mod*> (&*el))
          m_start_addr_list.add (rm);
      else if (reg_use* ru = dyn_cast<reg_use*> (&*el))
        if (addr.is_valid ())
          ru->set_reg (addr.base_reg ());

      el->set_current_addr (addr);
    }

  return success;
}

// Internal function of gen_address_mod. Generate reg-mods needed to arrive at
// the address of EL and return the cost of the address modifications.
// If RECORD_IN_SEQUENCE is false, don't insert the actual modifications
// in the sequence, only calculate the cost.
int ams::sequence::
gen_address_mod_1 (filter_iterator<iterator, element_to_optimize> el,
                   delegate& dlg, std::set<reg_mod*>& used_reg_mods,
                   std::map<addr_reg, reg_mod*>& visited_reg_mods,
                   unsigned* next_tmp_regno, int lookahead_num,
                   bool record_in_sequence)
{
  const addr_expr& ae = el->effective_addr ();

  if (ae.is_invalid ())
    return 0;

  if (record_in_sequence)
    {
      log_msg ("\nprocessing element ");
      log_sequence_element (*el);
      log_msg ("\n");
    }

  int min_cost = infinite_costs;
  bool failed_addr_change = false;
  const alternative* min_alternative = NULL;
  reg_mod* min_start_base;
  reg_mod* min_start_index;
  addr_expr min_end_base, min_end_index;
  mod_tracker tracker (*this, used_reg_mods, visited_reg_mods);

  filter_iterator<iterator, element_to_optimize> next_el =
    lookahead_num ? stdx::next (el) : end<element_to_optimize> ();

  const alternative_set* alternatives;

  alternative_set reg_use_alt;
  if (el->type () == type_reg_use)
    {
      // If this is a reg use, the address will be stored in a single reg.
      reg_use_alt.push_back (alternative (0, make_reg_addr (any_reg)));
      alternatives = &reg_use_alt;
    }
  else
    // Otherwise, the mem access' alternatives will be used.
    alternatives = &((mem_access*)&*el)->alternatives ();

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
          end_index = non_mod_addr (invalid_reg, ae.index_reg (),
				    ae.scale (), ae.disp ());
        }

      // Get the costs for using this alternative.
      int alt_min_cost = alt->cost ();

      std::pair<int, reg_mod*> base_start_addr =
        find_cheapest_start_addr (end_base, el, alt_ae.base_reg (),
                                  alt_ae.disp_min (), alt_ae.disp_max (),
                                  alt_ae.type (), dlg,
                                  used_reg_mods, visited_reg_mods,
                                  next_tmp_regno);

      if (base_start_addr.first == infinite_costs)
        continue;

      alt_min_cost += base_start_addr.first;

      std::pair<int, reg_mod*> index_start_addr;

      if (alt_ae.has_index_reg ())
        {
          index_start_addr
            = find_cheapest_start_addr (end_index, el, alt_ae.index_reg (),
                                        alt_ae.disp_min (), alt_ae.disp_max (),
                                        alt_ae.type (), dlg,
                                        used_reg_mods, visited_reg_mods,
                                        next_tmp_regno);
          if (index_start_addr.first == infinite_costs)
            continue;

          alt_min_cost += index_start_addr.first;
        }

      bool success = insert_address_mods (
        alt, base_start_addr.second, index_start_addr.second,
        end_base, end_index, el, tracker, used_reg_mods,
        visited_reg_mods, dlg, next_tmp_regno);

      if (!success)
        {
          failed_addr_change = true;
          tracker.reset_changes ();
          continue;
        }

      // Calculate the costs of the next element when this alternative is used.
      // This is done by inserting the address modifications of this alternative
      // into the sequence, calling this function on the next element and then
      // removing the inserted address mods.
      if (next_el != end ())
        {
          // Mark the reg-mods between the current and next element as visited.
          // This will be undone by the mod-tracker later.
          for (iterator it = el; it != next_el; ++it)
	    if (reg_mod* rm = dyn_cast<reg_mod*> (&*it))
              tracker.visit_reg_mod (rm);

          int next_cost = gen_address_mod_1 (next_el, dlg,
                                             used_reg_mods, visited_reg_mods,
                                             next_tmp_regno,
                                             lookahead_num-1, false);

          if (next_cost == infinite_costs)
            alt_min_cost = infinite_costs;
          else
            alt_min_cost += next_cost;
        }
      tracker.reset_changes ();

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

  if (min_cost == infinite_costs)
    {
      gcc_assert (failed_addr_change);
      return infinite_costs;
    }

  if (record_in_sequence)
    {
      log_msg ("  min alternative: %d  min costs = %d\n",
               (int)(min_alternative - alternatives->begin ()),
               min_cost);
      bool success = insert_address_mods (
        min_alternative, min_start_base, min_start_index,
        min_end_base, min_end_index, el, tracker,
        used_reg_mods, visited_reg_mods, dlg, next_tmp_regno);
      gcc_assert (success);
    }

  return min_cost;
}

// The return type of try_insert_address_mods. Stores the reg-mod that contains
// the final address, the costs of the address modifications and the constant
// displacement that the mem access needs to use.
struct ams::mod_addr_result
{
  int cost;
  reg_mod* final_addr;
  disp_t addr_disp;

  mod_addr_result (void)
  : cost (0), final_addr (NULL), addr_disp (0) { }

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
std::pair<int, ams::reg_mod*> ams::sequence::
find_cheapest_start_addr (const addr_expr& end_addr, iterator el,
                          const addr_reg& reg,
                          disp_t min_disp, disp_t max_disp,
                          addr_type_t addr_type,
                          delegate& dlg, std::set<reg_mod*>& used_reg_mods,
                          std::map<addr_reg, reg_mod*>& visited_reg_mods,
                          unsigned* next_tmp_regno)
{
  int min_cost = infinite_costs;
  reg_mod* min_start_addr = NULL;
  mod_tracker tracker (*this, used_reg_mods, visited_reg_mods);
  machine_mode acc_mode = Pmode;

  if (reg_use* ru = dyn_cast<reg_use*> (&*el))
    acc_mode = ru->reg ().mode ();

  std::vector<reg_mod*> start_addrs;
  start_addresses ().get_relevant_addresses (end_addr,
                                             std::back_inserter (start_addrs));

  for (std::vector<reg_mod*>::iterator addrs = start_addrs.begin ();
       addrs != start_addrs.end (); ++addrs)
    {
      std::map<addr_reg, reg_mod*>::iterator visited_addr =
        visited_reg_mods.find ((*addrs)->reg ());
      if (visited_addr == visited_reg_mods.end ())
        continue;

      mod_addr_result result =
        try_insert_address_mods (*addrs, end_addr, min_disp, max_disp,
                                 addr_type, acc_mode, el, tracker,
                                 used_reg_mods, visited_reg_mods, dlg,
                                 next_tmp_regno);
      tracker.reset_changes ();
      // If REG is not an any_reg placeholder (e.g. in the case of the
      // GBR + disp alternative), the final address needs to be in REG.
      if (result.cost < min_cost && reg.matches (result.final_addr->reg ()))
        {
          min_cost = result.cost;
          min_start_addr = *addrs;
        }
    }

  // If the end address is a constant address, try loading it into
  // the reg directly.
  if (end_addr.regs_empty ())
    {
      reg_mod* const_load = as_a<reg_mod*> (&*insert_element (
	make_ref_counted<reg_mod> ((rtx_insn*)NULL, (*next_tmp_regno)++,
                                   acc_mode, NULL_RTX,
				   make_const_addr (end_addr.disp ()),
				   make_const_addr (end_addr.disp ())),
	begin ()));

      int cost = try_insert_address_mods (const_load, end_addr,
                                          min_disp, max_disp,
                                          addr_type, acc_mode, el,
                                          tracker, used_reg_mods,
                                          visited_reg_mods, dlg,
                                          next_tmp_regno).cost;
      if (cost < infinite_costs)
        cost += dlg.addr_reg_mod_cost (const_load->reg ().reg_rtx (),
                                       tmp_rtx<CONST_INT> (end_addr.disp ()),
                                       *this, begin ());

      tracker.reset_changes ();
      if (cost < min_cost)
        {
          min_cost = cost;
          min_start_addr = const_load;

          // If the costs are reduced, this const reg might be used in the
          // final sequence, so we can't remove it.  However, it shouldn't
          // be visible when trying other alternatives.
          m_start_addr_list.remove ((reg_mod*)&*begin ());
        }
      // If this doesn't reduce the costs, we can safely remove the new reg-mod.
      else
        remove_element (begin ());
    }

  return std::make_pair (min_cost, min_start_addr);
}

// Generate the address modifications needed to arrive at BASE_END_ADDR and
// INDEX_END_ADDR from BASE/INDEX_START_ADDR when using ALT as the access
// alternative.  Record any changes to the sequence in TRACKER.
bool ams::sequence::
insert_address_mods (alternative_set::const_iterator alt,
                     reg_mod* base_start_addr,
                     reg_mod* index_start_addr,
                     const addr_expr& base_end_addr,
                     const addr_expr& index_end_addr,
                     iterator el, mod_tracker& tracker,
                     std::set<reg_mod*>& used_reg_mods,
                     std::map<addr_reg, reg_mod*>& visited_reg_mods,
                     delegate& dlg, unsigned* next_tmp_regno)
{
  machine_mode acc_mode;
  const addr_expr& ae = el->effective_addr ();

  if (el->is_mem_access ())
    acc_mode = Pmode;
  else if (reg_use* ru = dyn_cast<reg_use*> (&*el))
    acc_mode = ru->reg ().mode ();
  else
    gcc_unreachable ();

  // Insert the modifications needed to arrive at the address
  // in the base reg.
  mod_addr_result base_insert_result =
    try_insert_address_mods (base_start_addr, base_end_addr,
                             alt->address ().disp_min (),
                             alt->address ().disp_max (),
                             alt->address ().type (),
                             acc_mode, el, tracker,
                             used_reg_mods, visited_reg_mods, dlg,
                             next_tmp_regno);

  addr_expr new_addr;
  mod_addr_result index_insert_result;
  if (alt->address ().has_no_index_reg ())
    {
      disp_t disp = ae.disp () - base_insert_result.addr_disp;
      new_addr = non_mod_addr (base_insert_result.final_addr->reg (),
                               invalid_reg, 1, disp);
    }
  else
    {
      // Insert the modifications needed to arrive at the address
      // in the index reg.
      index_insert_result =
        try_insert_address_mods (index_start_addr, index_end_addr,
                                 0, 0,
                                 alt->address ().type (),
                                 acc_mode, el, tracker,
                                 used_reg_mods, visited_reg_mods, dlg,
                                 next_tmp_regno);
      new_addr = non_mod_addr (base_insert_result.final_addr->reg (),
                               index_insert_result.final_addr->reg (), 1, 0);
    }

  if (alt->address ().type () == pre_mod)
    new_addr = pre_mod_addr (new_addr.base_reg (), alt->address ().disp ());
  else if (alt->address ().type () == post_mod)
    new_addr = post_mod_addr (new_addr.base_reg (), alt->address ().disp ());

  if (mem_access* m = dyn_cast<mem_access*> (&*el))
    {
      // Check that the new address is actually valid.
      // Replace the temporary registers with a permanent
      // placeholder reg first.
      addr_expr check_addr = new_addr;
      if (check_addr.base_reg () ==
            base_insert_result.final_addr->tmp_reg ())
        check_addr.set_base_reg (m_substitute_reg);
      if (check_addr.has_index_reg ()
          && check_addr.index_reg () ==
               index_insert_result.final_addr->tmp_reg ())
        check_addr.set_index_reg (m_substitute_reg);
      if (!m->try_replace_addr (check_addr))
        {
          log_msg ("failed to add new addr = ");
          log_addr_expr (new_addr);
          log_msg ("\nfor access\n");
          log_sequence_element (*m);
          log_msg ("\n");
          return false;
        }

      // Update the current address of the mem access with the alternative.
      tracker.addr_changed_els ()
        .push_back (std::make_pair (m, std::make_pair (m->current_addr (),
                                                       alt)));
      m->set_current_addr_and_alt (new_addr, alt);
      m->set_cost (alt->cost ());
      tracker.create_dependency (base_insert_result.final_addr, m);
      if (alt->address ().has_index_reg ())
        tracker.create_dependency (index_insert_result.final_addr, m);
    }
  else if (reg_use* ru = dyn_cast<reg_use*> (&*el))
    {
      gcc_assert (new_addr.has_no_index_reg () && new_addr.has_no_disp ());
      if (ru->reg_ref () != NULL)
        {
          // If the expression in which the reg is used is known, modify the
          // reg that'll be used in the expression.
          tracker.addr_changed_els ().push_back (std::make_pair (
            ru, std::make_pair (ru->current_addr (),
                                (alternative_set::const_iterator)NULL)));
          ru->set_reg (new_addr.base_reg ());
          ru->set_current_addr (new_addr);
          tracker.create_dependency (base_insert_result.final_addr, ru);
        }
      else
        {
          // Otherwise, insert a reg-mod that sets the used reg to
          // the correct value.
          iterator inserted_el = tracker.insert_reg_mod (
            make_ref_counted<reg_mod> ((rtx_insn*)NULL, ru->reg (), NULL_RTX,
                                       new_addr, ru->effective_addr ()),
            el);
          tracker.create_dependency (&*inserted_el, ru);
          tracker.create_dependency (base_insert_result.final_addr,
                                     &*inserted_el);
        }
    }
  return true;
}

// Try to generate the address modifications needed to arrive at END_ADDR
// from START_ADDR. Record any changes to the sequence in TRACKER.  If the
// final address is going to be used in a mem access, DISP_MIN and DISP_MAX
// indicate the displacement range of the access.
// Return the register that stores the final address, the cost of the
// modifications and the constant displacement that the mem access needs to use.
// If it's not possible to arrive at the final address, the returned cost will
// be infinite.
ams::mod_addr_result ams::sequence::
try_insert_address_mods (reg_mod* start_addr, const addr_expr& end_addr,
                         disp_t min_disp, disp_t max_disp,
                         addr_type_t addr_type, machine_mode acc_mode,
                         iterator el, mod_tracker& tracker,
                         std::set<reg_mod*>& used_reg_mods,
                         std::map<addr_reg, reg_mod*>& visited_reg_mods,
                         delegate& dlg, unsigned* next_tmp_regno)
{
  int total_cost = 0;
  int clone_cost = used_reg_mods.find (start_addr) != used_reg_mods.end ()
                   ? dlg.addr_reg_clone_cost (start_addr->reg ().reg_rtx (),
                                              *this, el)
                   : 0;

  // If the register holding the start address has alerady been overwritten
  // by something else, emit a reg copy after the insn where it got its
  // previous value and use the copied reg as the start address.
  std::map<addr_reg, reg_mod*>::iterator visited_addr =
    visited_reg_mods.find (start_addr->reg ());
  if (visited_addr != visited_reg_mods.end ()
      && visited_addr->second != start_addr)
    {
      start_addr = insert_addr_mod (start_addr, acc_mode,
                                    start_addr->reg ().reg_rtx (),
                                    start_addr->current_addr (),
                                    start_addr->effective_addr (),
                                    el, tracker, used_reg_mods, dlg,
                                    next_tmp_regno, true);
      start_addr->adjust_cost (clone_cost);
      clone_cost = 0;
      total_cost += start_addr->cost ();
    }

  // Canonicalize the start and end addresses by converting
  // addresses of the form base+disp into index*1+disp.
  addr_expr c_start_addr = start_addr->effective_addr ().is_invalid ()
			   ? make_reg_addr (start_addr->reg ())
			   : start_addr->effective_addr ();
  addr_expr c_end_addr = end_addr;

  if (c_start_addr.has_no_index_reg ())
    c_start_addr = non_mod_addr (invalid_reg, c_start_addr.base_reg (), 1,
				 c_start_addr.disp ());
  if (c_end_addr.has_no_index_reg ())
    c_end_addr = non_mod_addr (invalid_reg, c_end_addr.base_reg (), 1,
			       c_end_addr.disp ());

  // If one of the addresses has the form base+index*1, it
  // might be better to switch its base and index reg.
  if (c_start_addr.index_reg () == c_end_addr.base_reg ())
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
      && c_start_addr.base_reg () != c_end_addr.base_reg ())
    return mod_addr_result (infinite_costs);

  // Same for index regs, unless we can get to the end address
  // by subtracting.
  if (c_start_addr.index_reg () != c_end_addr.index_reg ())
    {
      if (!(c_start_addr.has_no_base_reg ()
            && c_end_addr.has_index_reg ()
            && c_start_addr.index_reg () == c_end_addr.base_reg ()
            && c_start_addr.scale () == 1
            && c_end_addr.scale () == -1))
        return mod_addr_result (infinite_costs);
    }

  // The start address' regs need to have the same machine mode as the access.
  if (c_start_addr.has_base_reg ()
      && c_start_addr.base_reg ().mode () != acc_mode)
    return mod_addr_result (infinite_costs);
  if (c_start_addr.has_index_reg ()
      && c_start_addr.index_reg ().mode () != acc_mode)
    return mod_addr_result (infinite_costs);


  // Add scaling.
  if (c_start_addr.has_index_reg ()
      && c_start_addr.index_reg () == c_end_addr.index_reg ()
      && c_start_addr.scale () != c_end_addr.scale ())
    {
      // We can't scale if the address has a base reg.
      if (c_start_addr.has_base_reg ())
        return mod_addr_result (infinite_costs);

      // We can only scale by integers.
      gcc_assert (c_start_addr.scale () != 0);
      std::div_t sr = std::div (c_end_addr.scale (), c_start_addr.scale ());

      if (sr.rem != 0)
        return mod_addr_result (infinite_costs);

      scale_t scale = sr.quot;

      // The scaled displacement shouldn't overflow.
      if (sext_hwi (c_start_addr.disp ()*scale, GET_MODE_PRECISION (Pmode)) !=
          c_start_addr.disp ()*scale)
        return mod_addr_result (infinite_costs);

      start_addr = insert_addr_mod (start_addr, acc_mode,
                                    tmp_rtx<MULT> (acc_mode,
                                                   start_addr->reg ().reg_rtx (),
                                                   tmp_rtx<CONST_INT> (scale)),
                                    non_mod_addr (invalid_reg,
                                                  start_addr->reg (),
                                                  scale, 0),
                                    non_mod_addr (invalid_reg,
                                                  c_start_addr.index_reg (),
                                                  c_end_addr.scale (),
                                                  c_start_addr.disp ()*scale),
                                    el, tracker,
                                    used_reg_mods, dlg, next_tmp_regno);
      c_start_addr = start_addr->effective_addr ();
      start_addr->adjust_cost (clone_cost);
      clone_cost = 0;
      total_cost += start_addr->cost ();
    }

  // Try subtracting regs.
  if (c_start_addr.has_no_base_reg ()
      && c_end_addr.has_index_reg ()
      && c_start_addr.index_reg () == c_end_addr.base_reg ()
      && c_start_addr.scale () == 1
      && c_end_addr.scale () == -1)
    {
      reg_mod* index_reg_addr
        = find_start_addr_for_reg (c_end_addr.index_reg (),
                                   used_reg_mods, &visited_reg_mods);

      bool prev_index_reg = false;
      if (index_reg_addr == NULL)
        {
          // If no suitable index reg is found, check if there's a register
          // whose previous value could be used.
          prev_index_reg = true;
          index_reg_addr = find_start_addr_for_reg (c_end_addr.index_reg (),
                                                    used_reg_mods, NULL);
          if (index_reg_addr == NULL)
            {
              // If there are no suitable previous index regs either, give up.
              tracker.reset_changes ();
              return mod_addr_result (infinite_costs);
            }
        }

      if (index_reg_addr == NULL)
        {
          tracker.reset_changes ();
          return mod_addr_result (infinite_costs);
        }
      disp_t index_disp = index_reg_addr->effective_addr ().is_valid () ?
        index_reg_addr->effective_addr ().disp () : 0;

      bool index_reg_used
        = used_reg_mods.find (index_reg_addr) != used_reg_mods.end ();

      reg_mod* used_rm;

      // If the index reg's value has been changed, emit a reg copy
      // after the insn where it got its previous value and use the
      // copied reg instead.
      if (prev_index_reg)
        {
          rtx reg_rtx = c_end_addr.index_reg ().reg_rtx ();
          used_rm = insert_addr_mod (index_reg_addr, acc_mode, reg_rtx,
                                     index_reg_addr->current_addr (),
                                     index_reg_addr->effective_addr (),
                                     el, tracker, used_reg_mods, dlg,
                                     next_tmp_regno, true);
          used_rm->adjust_cost (dlg.addr_reg_clone_cost (reg_rtx, *this, el));
          total_cost += used_rm->cost ();
        }
      else
        used_rm = index_reg_addr;

      reg_mod* new_addr
        = insert_addr_mod (used_rm, acc_mode,
                           tmp_rtx<PLUS> (acc_mode,
                                          start_addr->reg ().reg_rtx (),
                                          used_rm->reg ().reg_rtx ()),
                           non_mod_addr (start_addr->reg (),
                                         used_rm->reg (),
                                         -1, 0),
                           non_mod_addr (c_start_addr.index_reg (),
                                         c_end_addr.index_reg (),
                                         -1, c_start_addr.disp ()-index_disp),
                           el, tracker, used_reg_mods, dlg, next_tmp_regno);
      tracker.create_dependency (start_addr, new_addr);
      start_addr = new_addr;
      c_start_addr = start_addr->effective_addr ();
      start_addr->adjust_cost (clone_cost);
      clone_cost = 0;

      if (index_reg_used)
        {
          // Take into account the cloning costs of the index reg.
          int extra_cost = dlg.addr_reg_clone_cost (
            index_reg_addr->reg ().reg_rtx (), *this, el);
          start_addr->adjust_cost (extra_cost);
        }

      total_cost += start_addr->cost ();
    }

  // Add missing base reg.
  if (c_start_addr.has_no_base_reg () && c_end_addr.has_base_reg ())
    {
      reg_mod* base_reg_addr
        = find_start_addr_for_reg (c_end_addr.base_reg (),
                                   used_reg_mods, &visited_reg_mods);
      bool prev_base_reg = false;
      if (base_reg_addr == NULL)
        {
          // If no suitable base reg is found, check if there's a register
          // whose previous value could be used.
          prev_base_reg = true;
          base_reg_addr = find_start_addr_for_reg (c_end_addr.base_reg (),
                                                   used_reg_mods, NULL);
          if (base_reg_addr == NULL)
            {
              // If there are no suitable previous base regs either, give up.
              tracker.reset_changes ();
              return mod_addr_result (infinite_costs);
            }
        }
      disp_t base_disp = base_reg_addr->effective_addr ().is_valid () ?
        base_reg_addr->effective_addr ().disp () : 0;

      bool base_reg_used
        = used_reg_mods.find (base_reg_addr) != used_reg_mods.end ();

      reg_mod* used_rm;

      // If the base reg's value has been changed, emit a reg copy
      // after the insn where it got its previous value and use the
      // copied reg instead.
      if (prev_base_reg)
        {
          rtx reg_rtx = c_end_addr.base_reg ().reg_rtx ();
          used_rm = insert_addr_mod (base_reg_addr, acc_mode, reg_rtx,
                                     base_reg_addr->current_addr (),
                                     base_reg_addr->effective_addr (),
                                     el, tracker, used_reg_mods, dlg,
                                     next_tmp_regno, true);
          used_rm->adjust_cost (dlg.addr_reg_clone_cost (reg_rtx, *this, el));
          total_cost += used_rm->cost ();
        }
      else
        used_rm = base_reg_addr;

      reg_mod* new_addr
        = insert_addr_mod (base_reg_addr, acc_mode,
                           tmp_rtx<PLUS> (acc_mode,
                                          used_rm->reg ().reg_rtx (),
                                          start_addr->reg ().reg_rtx ()),
                           non_mod_addr (used_rm->reg (),
                                         start_addr->reg (), 1, 0),
                           non_mod_addr (c_end_addr.base_reg (),
                                         c_start_addr.index_reg (),
                                         c_start_addr.scale (),
                                         c_start_addr.disp () + base_disp),
                           el, tracker, used_reg_mods, dlg, next_tmp_regno);
      tracker.create_dependency (start_addr, new_addr);
      start_addr = new_addr;
      c_start_addr = start_addr->effective_addr ();
      start_addr->adjust_cost (clone_cost);
      clone_cost = 0;

      if (base_reg_used)
        {
          // Take into account the cloning costs of the base reg.
          int extra_cost = dlg.addr_reg_clone_cost (
            base_reg_addr->reg ().reg_rtx (), *this, el);
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
                                    tmp_rtx<PLUS> (acc_mode,
                                                   start_addr->reg ().reg_rtx (),
                                                   tmp_rtx<CONST_INT> (disp)),
                                    non_mod_addr (start_addr->reg (),
                                                  invalid_reg, 1, disp),
                                    non_mod_addr (c_end_addr.base_reg (),
                                                  c_start_addr.index_reg (),
                                                  c_start_addr.scale (),
                                                  c_start_addr.disp () + disp),
                                    el, tracker,
                                    used_reg_mods, dlg, next_tmp_regno);
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
  if (addr_type != non_mod || c_end_addr.regs_empty ())
    {
      const addr_reg& pre_mod_reg = start_addr->reg ();
      start_addr
        = insert_addr_mod (start_addr, acc_mode,
                           pre_mod_reg.reg_rtx (),
                           make_reg_addr (pre_mod_reg),
                           non_mod_addr (c_end_addr.base_reg (),
                                         c_start_addr.index_reg (),
                                         c_start_addr.scale (),
                                         c_start_addr.disp () + auto_mod_disp),
                           el, tracker, used_reg_mods, dlg, next_tmp_regno);

      if (mem_access* m = dyn_cast<mem_access*> (&*el))
        start_addr->set_auto_mod_acc (m);
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
ams::reg_mod* ams::sequence::
insert_addr_mod (reg_mod* used_rm, machine_mode acc_mode,
                 rtx curr_addr_rtx, const addr_expr& curr_addr,
                 const addr_expr& effective_addr,
                 iterator el, mod_tracker& tracker,
                 std::set<reg_mod*>& used_reg_mods,
                 delegate& dlg, unsigned* next_tmp_regno, bool insert_after)
{
  if (used_reg_mods.find (used_rm) == used_reg_mods.end ())
    tracker.use_reg_mod (used_rm);

  iterator i = tracker.insert_reg_mod (
	make_ref_counted<reg_mod> ((rtx_insn*)NULL, (*next_tmp_regno)++,
                                   acc_mode, NULL_RTX, curr_addr,
                                   effective_addr),
        insert_after ? stdx::next (el) : el);
  reg_mod* ii = as_a<reg_mod*> (&*i);

  tracker.create_dependency (used_rm, ii);
  ii->set_cost (dlg.addr_reg_mod_cost (ii->reg ().reg_rtx (), curr_addr_rtx,
                                       *this, el));
  return ii;
}

// Find a starting address whose effective address is the single base reg REG.
// If there are multiple such addresses, try to return one that wasn't used
// before (so that there's no cloning cost when using it).
// Return NULL if no such address was found.
// If VISITED_REG_MODS is not NULL, search only in the last visited values of
// the address regs.
ams::reg_mod* ams::sequence::
find_start_addr_for_reg (const addr_reg& reg, std::set<reg_mod*>& used_reg_mods,
                         std::map<addr_reg, reg_mod*>* visited_reg_mods)
{
  std::list<reg_mod*> start_addrs;
  addr_expr end_addr = make_reg_addr (reg);
  start_addresses ().get_relevant_addresses (end_addr,
                                             std::back_inserter (start_addrs));
  reg_mod* found_addr = NULL;

  for (trv_iterator<deref<start_addr_list::iterator> >
	addrs (start_addrs.begin ()), addrs_end (start_addrs.end ());
	addrs != addrs_end; ++addrs)
    {
      if (visited_reg_mods)
        {
          std::map<addr_reg, reg_mod*>::iterator visited_addr =
            visited_reg_mods->find (addrs->reg ());
          if (visited_addr == visited_reg_mods->end ()
              || visited_addr->second != &*addrs )
            continue;
        }

      const addr_expr &ae = addrs->effective_addr ().is_invalid ()
                            ? make_reg_addr (addrs->reg ())
                            : addrs->effective_addr ();
      if (ae.has_no_index_reg () && ae.base_reg () == reg)
        {
          found_addr = &*addrs;
          if (used_reg_mods.find (found_addr) == used_reg_mods.end ())
            break;
        }
    }

  return found_addr;
}

// Search for elements that can't be optimized by AMS and mark them so.
// Return the number of new unoptimizable elements found.
unsigned ams::sequence::
find_unoptimizable_elements (void)
{
  unsigned found = 0;
  for (iterator el = begin (); el != end (); ++el)
    {
      // Don't optimize those accesses that use regs with
      // a different machine mode.
      machine_mode acc_mode;
      if (el->is_mem_access ())
        acc_mode = Pmode;
      else if (reg_mod* rm = dyn_cast<reg_mod*> (&*el))
        acc_mode = rm->reg ().mode ();
      else if (reg_use* ru = dyn_cast<reg_use*> (&*el))
        acc_mode = ru->reg ().mode ();
      else
        continue;

      for (sequence_element::dependency_set::iterator deps =
             el->dependencies ().begin ();
           deps != el->dependencies ().end (); ++deps)
        {
          if (reg_mod* rm = dyn_cast<reg_mod*> (*deps))
            {
              if (rm->reg ().mode () != acc_mode)
                {
                  if (el->optimization_enabled ())
                    {
                      el->set_optimization_disabled ();
                      ++found;
                    }
                  for (sequence_element::dependency_set::iterator dep_els =
                         el->dependent_els ().begin ();
                       dep_els != el->dependent_els ().end (); ++dep_els)
                    if ((*dep_els)->optimization_enabled ())
                      {
                        (*dep_els)->set_optimization_disabled ();
                        ++found;
                      }
                  break;
                }
            }
        }
    }
  return found;
}

// Used for keeping track of register copying reg-mods.
class ams::reg_copy
{
public:
  reg_copy (void) {}
  reg_copy (addr_reg s, addr_reg d, sequence::iterator e)
    : src (s), dest (d), el (e), reg_modified (false), can_be_removed (true),
      use_count (0)
  {
  }
  addr_reg src, dest;
  sequence::iterator el;
  bool reg_modified;
  bool can_be_removed;
  int use_count;
};

// Try to eliminate unnecessary reg -> reg copies.
// If a sequence element uses a copied reg and neither the copy nor the
// original reg gets modified up to that point, use the original reg
// instead.  If all instances of the copy reg can be removed this way,
// remove the copying reg-mod too.
void
ams::sequence::eliminate_reg_copies (void)
{
  typedef std::map<addr_reg, reg_copy> reg_copy_map;
  reg_copy_map reg_copies;
  rtx_insn* prev_insn = start_insn ();

  for (iterator el = begin (); el != end (); ++el)
    {
      // Skip reg-mods that set the reg to itself.
      if (reg_mod* rm = dyn_cast<reg_mod*> (&*el))
        {
          const addr_expr& addr = rm->current_addr ();
          if (addr.is_invalid ()
              || (addr.has_no_index_reg () && addr.has_no_disp ()
                  && addr.base_reg () == rm->reg ()))
            continue;
        }
      log_sequence_element (*el);
      log_msg ("\n");

      rtx_insn* curr_insn = NULL;
      for (iterator it = el; it != end (); ++it)
        if (it->insn ())
          {
            curr_insn = it->insn ();
            break;
          }

      // Check if any reg copy got modified in the insns between the current
      // and previous elements.
      for (rtx_insn* i = prev_insn; i != curr_insn;
           i = next_nonnote_insn_bb (i))
        {
          for (reg_copy_map::iterator it = reg_copies.begin ();
               it != reg_copies.end (); ++it)
            {
              reg_copy& copy = it->second;
              if (!copy.reg_modified
                  && (reg_set_p (copy.src.reg_rtx (), i)
                      || reg_set_p (copy.dest.reg_rtx (), i)))
                copy.reg_modified = true;
            }
        }
      prev_insn = curr_insn;

      addr_expr addr = el->current_addr ();
      reg_copy* new_copy = NULL;

      if (reg_mod* rm = dyn_cast<reg_mod*> (&*el))
        {
          // Check if the current reg-mod modifies a reg copy.
          reg_copy_map::iterator copy_in_map = reg_copies.find (rm->reg ());
          if (copy_in_map != reg_copies.end ())
            copy_in_map->second.reg_modified = true;

          // If this reg-mod is a reg <- reg copy, add it to the
          // copies list.
          if (addr.is_valid () && addr.has_no_index_reg ()
              && addr.has_no_disp () && addr.has_base_reg ())
            {
              reg_copies[rm->reg ()] =
                reg_copy (addr.base_reg (), rm->reg (), el);
              new_copy = &reg_copies[rm->reg ()];
            }
        }

      if (addr.is_invalid ())
        continue;

      // If the current element's base or index reg is a copied reg that
      // wasn't modified (and neither was the original reg), replace it
      // with the original reg.
      for (addr_expr::regs_iterator ri = addr.regs_begin ();
           ri != addr.regs_end (); ++ri)
        {
          reg_copy_map::iterator copy_in_map = reg_copies.find (*ri);
          if (copy_in_map != reg_copies.end ())
            {
              ++copy_in_map->second.use_count;
              reg_copy& copy = copy_in_map->second;
              if (copy.reg_modified)
                copy.can_be_removed = false;
              else
                {
                  *ri = copy_in_map->second.src;

                  // If the element is a reg-copy, also update the
                  // corresponding reg_copy struct.
                  if (new_copy != NULL)
                    new_copy->src = *ri;
                }
            }
        }
      log_msg ("new addr: ");
      log_addr_expr (addr);
      log_msg ("\n");
      el->set_current_addr (addr);
      if (reg_use* ru = dyn_cast<reg_use*> (&*el))
        ru->set_reg (addr.base_reg ());
    }

  // Remove all copies from the sequence that aren't used anymore.
  // Only remove those copies that were used somewhere.
  for (reg_copy_map::iterator it = reg_copies.begin ();
       it != reg_copies.end (); ++it)
    {
      reg_copy& copy = it->second;

      if (copy.can_be_removed && copy.use_count > 0)
        // FIXME: Update the dependencies in case a later sub-pass wants
        // to use them.
        remove_element (copy.el);
    }
}

// Update the original insn stream with the changes in this sequence.
void
ams::sequence::update_insn_stream (void)
{
  bool insn_sequence_started = false;

  for (iterator els = begin (); els != end (); ++els)
    {
      if (els->insn ())
        {
          if (insn_sequence_started)
            {
              rtx_insn* new_insns = get_insns ();
              end_sequence ();
              insn_sequence_started = false;

              log_msg ("emitting new insns = \n");
              log_rtx (new_insns);
              log_msg ("\nbefore insn\n");
              log_insn (els->insn ());
              log_msg ("\n");
              emit_insn_before (new_insns, els->insn ());
            }
        }

      if (!els->optimization_enabled ())
        {
          log_msg ("element didn't get optimized, skipping\n");
          continue;
        }
      insn_sequence_started = els->generate_new_insns (insn_sequence_started);
    }

  // Emit remaining address modifying insns after the last insn in the
  // sequence's BB.
  if (insn_sequence_started)
    {
      rtx_insn* last_insn = BB_END (bb ());
      bool emit_before = control_flow_insn_p (last_insn);

      rtx_insn* new_insns = get_insns ();
      end_sequence ();

      log_msg ("emitting new insns = \n");
      log_rtx (new_insns);
      if (emit_before)
        log_msg ("\nbefore insn\n");
      else
        log_msg ("\nafter insn\n");
      log_insn (last_insn);
      log_msg ("\n");
      if (emit_before)
        emit_insn_before (new_insns, last_insn);
      else
        emit_insn_after (new_insns, last_insn);
    }
}

// The recursive part of find_addr_reg_uses. Find all references to REG
// in X and add them to OUT. CHECK_EVERY_RTX indicates whether all
// sub-rtxes of X should be traversed.
template <typename OutputIterator> void
ams::sequence::find_addr_reg_uses_1 (rtx reg, rtx& x, OutputIterator out,
                                     bool check_every_rtx)
{
  switch (GET_CODE (x))
    {
    case REG:
      if (REGNO (reg) == REGNO (x))
          *out++ = &x;
      break;

    case MEM:
      // regs inside MEM rtx-es should be stored as mem-accesses.
      return;

    case PARALLEL:
    case UNSPEC:
    case UNSPEC_VOLATILE:
      for (int i = 0; i < XVECLEN (x, 0); i++)
        find_addr_reg_uses_1 (reg, XVECEXP (x, 0, i), out, check_every_rtx);
      break;

    case SET:
      // If an address reg is modified, this should be a reg-mod instead
      // of a reg-use.
      if (m_addr_regs.find (SET_DEST (x)) != m_addr_regs.end ())
        return;

      find_addr_reg_uses_1 (reg, SET_SRC (x), out, true);
      break;

    default:
      if (UNARY_P (x) || BINARY_P (x))
        {
          // If the reg is inside a (plus reg (const_int ...)) rtx,
          // add the whole rtx instead of just the reg.
          addr_expr use_expr = rtx_to_addr_expr (x);
          if (use_expr.is_valid () && use_expr.has_no_index_reg ()
              && use_expr.has_base_reg () && use_expr.has_disp ()
              && use_expr.base_reg () == reg)
            {
              *out++ = &x;
              break;
            }

	  for (int i = 0; i < GET_RTX_LENGTH (GET_CODE (x)); i++)
	    find_addr_reg_uses_1 (reg, XEXP (x, i), out, check_every_rtx);
        }
      else if (check_every_rtx)
        {
          subrtx_ptr_iterator::array_type array;
          FOR_EACH_SUBRTX_PTR (it, array, &x, NONCONST)
            {
              if (REG_P (**it) && REGNO (reg) ==  REGNO (**it))
                *out++ = *it;
            }
        }
      break;
    }
}

// The first insn in the access sequence.
rtx_insn*
ams::sequence::start_insn (void) const
{
  for (const_iterator e = begin (); e != end (); ++e)
    {
      if (e->insn ())
        return e->insn ();
    }
  gcc_unreachable ();
}

// Insert a new element into the sequence.  Return an iterator pointing
// to the newly inserted element.
ams::sequence::iterator
ams::sequence::insert_element (const ref_counting_ptr<sequence_element>& el,
                                   iterator insert_before)
{
  iterator i (m_els.insert (insert_before.base (), el));

  if (el->id () == sequence_element::invalid_id)
    el->set_id ((*m_next_id)++);

  el->sequences ().insert (this);

  // Update the insn -> element map.
  if (el->insn ())
    {
      m_insn_el_map.insert (std::make_pair (el->insn (), i));
      m_glob_insn_el_map.insert (std::make_pair (el->insn (), &*i));
    }

  // Update the address reg and the start address list.
  if (reg_mod* rm = dyn_cast<reg_mod*> (&*el))
    {
      // Only permanent registers are placed into the
      // address regs list.
      if (rm->reg () != rm->tmp_reg ())
        {
          ++m_addr_regs[rm->reg ()];
          for (addr_expr::regs_const_iterator ri =
                 rm->effective_addr ().regs_begin ();
               ri != rm->effective_addr ().regs_end (); ++ri)
            ++m_addr_regs[*ri];
        }
      m_start_addr_list.add (rm);
    }

  return i;
}

// If EL is unique, insert it into the sequence and return an iterator
// pointing to it.  If it already has a duplicate in the sequence, don't
// insert it and return an iterator to the already inserted duplicate instead.
// The place of the element is determined by its insn.
ams::sequence::iterator
ams::sequence::insert_unique (const ref_counting_ptr<sequence_element>& el)
{
  if (m_els.empty ())
    return insert_element (el, end ());

  if (!el->insn ())
    {
      // Reg-uses without an insn go to the sequence's end.
      if (el->type () == type_reg_use)
        {
          // Check for duplicates.
          for (reverse_iterator els = rbegin ();
	       els != rend () && !els->insn (); ++els)
            {
              if (*el == *els)
                return iterator (stdx::next (els.base ().base ()));
            }
          return insert_element (el, end ());
        }
      // Other insn-less elements go to the sequence's start.
      else
        {
          // Check for duplicates.
          for (iterator els = begin (); els != end () && !els->insn (); ++els)
	    if (*el == *els)
	      return els;
/*
      // FIXME: this should be the same as above, shouldn't it?
      // start_insn_element returns the first element that's got an insn,
      // so we can use that as an end iterator.  It's a bit easier to grasp.
      const_iterator first_insn_i = start_insn_element ();
      iterator els = std::find_if (elements ().begin (), first_insn_i,
				   sequence_element::equals (*el));
      if (els != first_insn_i)
	return els;
*/
          return insert_element (el, begin ());
        }
    }

  // Check for duplicates.
  std::pair<insn_map::iterator, insn_map::iterator>
    els_in_insn = elements_in_insn (el->insn ());
  for (insn_map::iterator i = els_in_insn.first; i != els_in_insn.second; ++i)
    if (*el == *i->second)
      return i->second;

  // If the new element isn't a reg-mod, insert it before the first
  // reg-mod belonging to the same insn.
  if (el->type () != type_reg_mod)
    {
      for (insn_map::iterator i = els_in_insn.first;
           i != els_in_insn.second; ++i)
        {
          iterator insert_before = i->second;
          if (insert_before->type () == type_reg_mod
              && (insert_before == begin ()
                  || stdx::prev (insert_before)->type () != type_reg_mod
                  || stdx::prev (insert_before)->insn () != el->insn ()))
            return insert_element (el, insert_before);
        }
    }

  // Otherwise, insert it after the last element from the same insn.
  for (insn_map::iterator i = els_in_insn.first; i != els_in_insn.second; ++i)
    {
      iterator insert_after = i->second;
      if (stdx::next (insert_after) == end ()
	  || stdx::next (insert_after)->insn () != insert_after->insn ())
        return insert_element (el, stdx::next (insert_after));
    }

  // If there are no existing elements sharing the same insn,
  // insert the new element before the next insn's elements.
  for (rtx_insn* i = NEXT_INSN (el->insn ()); ; i = NEXT_INSN (i))
    {
      els_in_insn = elements_in_insn (i);
      if (els_in_insn.first == els_in_insn.second)
        {
          // If there are no elements after this insn, insert it before
          // the insn-less reg-uses.
          if (i == NULL)
            {
              for (reverse_iterator els = rbegin (); els != rend (); ++els)
		if (els->insn () || els->type () != type_reg_use)
		  return insert_element (el, iterator (els.base ().base ()));

              return insert_element (el, begin ());
            }
          continue;
        }

      for (insn_map::iterator els = els_in_insn.first;
           els != els_in_insn.second; ++els)
        {
          iterator insert_before = els->second;
          if (insert_before == begin ()
              || stdx::prev (insert_before)->insn () != insert_before->insn ())
            return insert_element (el, insert_before);
        }
      gcc_unreachable ();
    }

  gcc_unreachable ();
}

// Remove an element from the sequence.  Return an iterator pointing
// to the next element.
ams::sequence::iterator
ams::sequence::remove_element (iterator el, bool clear_deps)
{
  // Update the insn -> element map.
  if (el->insn ())
    {
      std::pair<insn_map::iterator, insn_map::iterator> range =
        m_insn_el_map.equal_range (el->insn ());
      for (insn_map::iterator it = range.first; it != range.second; ++it)
	if (it->second == el)
	  {
	    m_insn_el_map.erase (it);
	    break;
	  }
      std::pair<glob_insn_map::iterator, glob_insn_map::iterator> glob_range =
        m_glob_insn_el_map.equal_range (el->insn ());
      for (glob_insn_map::iterator it = glob_range.first;
           it != glob_range.second; ++it)
	if (it->second == &*el)
	  {
	    m_glob_insn_el_map.erase (it);
	    break;
	  }
    }

  // Update the address reg and the start address list.
  if (reg_mod* rm = dyn_cast<reg_mod*> (&*el))
    {
      if (rm->reg () != rm->tmp_reg ())
        {
          addr_reg_map::iterator addr_reg = m_addr_regs.find (rm->reg ());
          --addr_reg->second;
          if (addr_reg->second == 0)
            m_addr_regs.erase (addr_reg);
        }

      m_start_addr_list.remove (rm);
    }

  // Update the element's dependencies.
  if (clear_deps)
    {
      for (sequence_element::dependency_set::iterator deps =
             el->dependencies ().begin ();
           deps != el->dependencies ().end (); ++deps)
        (*deps)->remove_dependent_el (&*el);

      for (sequence_element::dependency_set::iterator dep_els =
             el->dependent_els ().begin ();
           dep_els != el->dependent_els ().end (); ++dep_els)
        (*dep_els)->remove_dependency (&*el);
    }

  return iterator (m_els.erase (el.base ()));
}

// Revert the sequence to a previous state found in PREV_SEQUENCES.
void
ams::sequence::revert (std::map<sequence*, sequence>& prev_sequences)
{
  std::map<sequence*, sequence>::iterator prev_seq =
                                   prev_sequences.find (this);
  gcc_assert (prev_seq != prev_sequences.end ());
  *this = prev_seq->second;
  prev_sequences.erase (prev_seq);

  // Restore the dependencies that might have been removed
  // when an element got removed from the sequence.
  for (iterator el = begin (); el != end (); ++el)
    {
      for (sequence_element::dependency_set::iterator deps =
             el->dependencies ().begin ();
           deps != el->dependencies ().end (); ++deps)
        (*deps)->add_dependent_el (&*el);
      for (sequence_element::dependency_set::iterator dep_els =
             el->dependent_els ().begin ();
           dep_els != el->dependent_els ().end (); ++dep_els)
        (*dep_els)->add_dependency (&*el);
    }
}

bool
ams::sequence::contains (const sequence_element* el) const
{
  gcc_assert (el->insn () != NULL);

  std::pair<insn_map::const_iterator, insn_map::const_iterator> els_in_insn =
    elements_in_insn (el->insn ());
  for (insn_map::const_iterator els = els_in_insn.first;
       els != els_in_insn.second; ++els)
    if (&*els->second == el)
      return true;

  return false;
}


// The total cost of the accesses in the sequence.
int
ams::sequence::cost (void) const
{
  int cost = 0;
  for (const_iterator i = begin (); i != end () && cost != infinite_costs; ++i)
    cost += i->cost ();
  return cost;
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
ams::sequence::calculate_adjacency_info (void)
{
  typedef filter_iterator<iterator, element_to_optimize> iter;

  for (iter m = begin<element_to_optimize> (),
         mend = end<element_to_optimize> (); m != mend; )
    {
      iter inc_end = std::adjacent_find (m, mend,
                                         sequence_element::not_adjacent_inc);
      if (inc_end != mend)
        ++inc_end;

      const int inc_len = std::distance (m, inc_end);
      const sequence_element* first_el = &*m;
      iter last_el = inc_end;
      --last_el;

      for (int i = 0; i < inc_len; ++i)
	{
	  m->set_inc_chain (adjacent_chain_info (i, inc_len, first_el,
						 &*last_el));
	  ++m;
	}
    }

  for (iter m = begin<element_to_optimize> (),
         mend = end<element_to_optimize> (); m != mend; )
    {
      iter dec_end = std::adjacent_find (m, mend,
                                         sequence_element::not_adjacent_dec);
      if (dec_end != mend)
        ++dec_end;

      const int dec_len = std::distance (m, dec_end);
      const sequence_element* first_el = &*m;
      iter last_el = dec_end;
      --last_el;

      for (int i = 0; i < dec_len; ++i)
	{
	  m->set_dec_chain (adjacent_chain_info (i, dec_len, first_el,
						 &*last_el));
	  ++m;
	}
    }
}

// Re-calculate the sequence's cost.
void
ams::sequence::update_cost (delegate& d)
{
  for (iterator els = begin (); els != end (); ++els)
    els->update_cost (d, *this, els);
}

// Check whether the cost of the sequence is already minimal and
// can't be improved further, i.e. if all memory accesses use the
// cheapest alternative and there are no reg-mods with nonzero cost.
bool
ams::sequence::cost_already_minimal (void) const
{
  for (const_iterator els = begin (); els != end (); ++els)
    {
      if (const mem_access* m = dyn_cast<const mem_access*> (&*els))
	{
	  for (alternative_set::const_iterator a = m->alternatives ().begin ();
	      a != m->alternatives ().end (); ++a)
	    if (a->cost () < m->cost ())
	      return false;
	}
      else if (els->cost () > 0)
	return false;
    }
  return true;
}

// Update the alternatives of the sequence's accesses.
void
ams::sequence::update_access_alternatives (delegate& d,
                                               bool force_validation,
                                               bool disable_validation,
                                               bool adjust_costs)
{
  for (mem_acc_iter m (begin<mem_match> ()), m_end (end<mem_match> ());
       m != m_end; ++m)
    m->update_access_alternatives (*this, m.base (), d, force_validation,
				   disable_validation);

  if (!adjust_costs)
    return;

  for (mem_acc_iter m (begin<mem_match> ()), m_end (end<mem_match> ());
       m != m_end; ++m)
    for (alternative_set::iterator alt = m->alternatives ().begin ();
         alt != m->alternatives ().end (); ++alt)
      d.adjust_alternative_costs (*alt, *this, m.base ());
}

// Update the alternatives of the access.
void
ams::mem_access::update_access_alternatives (const sequence& seq,
                                                 sequence::const_iterator it,
                                                 delegate& d,
                                                 bool force_validation,
                                                 bool disable_validation)
{
  bool val_alts = alternative_validation_enabled ();

  alternatives ().clear ();

  if (effective_addr ().is_invalid ())
    return;

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

      // Alternatives might have reg placeholders such as any_reg.
      // When validating the change in the insn we need to have real pseudos.
      // To avoid creating a lot of pseudos, use this one.
      tmp_rtx<REG> tmp_reg_rtx (Pmode, LAST_VIRTUAL_REGISTER + 1);
      addr_reg tmp_reg (tmp_reg_rtx);

      addr_expr tmp_addr;

      for (iter alt = iter (alternatives ().begin (),
			    alternatives ().end ()),
	   alt_end = iter (alternatives ().end (),
			   alternatives ().end ()); alt != alt_end; ++alt)
	{
	  if (alt->address ().has_no_base_reg ())
	    log_invalidate_cont ("has no base reg");

	  tmp_addr = alt->address ();
	  if (tmp_addr.base_reg () == any_reg)
            tmp_addr.set_base_reg (tmp_reg);
	  if (tmp_addr.index_reg () == any_reg)
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
      set_optimization_disabled ();
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
      set_optimization_disabled ();
    }
  m_current_alt = alt_match;
}

bool
ams::mem_access::matches_alternative (const ams::alternative& alt) const
{
  const addr_expr& ae = current_addr ();
  const addr_expr& alt_ae = alt.address ();

  if (ae.is_invalid ())
    return false;

  if (ae.type () != alt_ae.type ())
    return false;

  if (ae.has_base_reg () != alt_ae.has_base_reg ())
    return false;
  if (ae.has_index_reg () != alt_ae.has_index_reg ())
    return false;

  if (ae.has_base_reg () && alt_ae.has_base_reg ()
      && !ae.base_reg ().matches (alt_ae.base_reg ()))
    return false;

  if (ae.disp () < alt_ae.disp_min () || ae.disp () > alt_ae.disp_max ())
    return false;

  if (ae.has_index_reg ()
      && (ae.scale () < alt_ae.scale_min ()
          || ae.scale () > alt_ae.scale_max ()
          || !ae.index_reg ().matches (alt_ae.index_reg ())))
    return false;

  return true;
}

// Check if DISP can be used as constant displacement in any of the address
// alternatives of the access.
bool
ams::mem_access::displacement_fits_alternative (disp_t disp) const
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
ams::reg_use::set_reg_ref (rtx new_reg)
{
  return validate_change (insn (), m_reg_ref, new_reg, false);
}

bool
ams::mem_access::generate_new_insns (bool insn_sequence_started)
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

  check_add_incdec_notes (insn ());
  return insn_sequence_started;
}

bool
ams::reg_use::generate_new_insns (bool insn_sequence_started)
{
  if (reg_ref () == NULL)
    {
      log_msg ("reg-use is unspecified, skipping\n");
      return insn_sequence_started;
    }

  gcc_assert (set_reg_ref (reg ().reg_rtx ()));
  return insn_sequence_started;
}

bool
ams::reg_mod::generate_new_insns (bool insn_sequence_started)
{
  if (insn () != NULL)
    {
      log_msg ("reg-mod already has an insn, skipping\n");
      return insn_sequence_started;
    }

  if (current_addr ().has_base_reg () && current_addr ().has_no_index_reg ()
      && current_addr ().base_reg () == reg ())
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
  if (current_addr ().regs_empty ())
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
          rtx index = subtract ? current_addr ().index_reg ().reg_rtx ()
            : expand_mult (current_addr ().index_reg ().reg_rtx (),
                           current_addr ().scale ());

          if (current_addr ().has_no_base_reg ())
            new_val = index;
          else if (subtract)
            new_val = expand_minus (current_addr ().base_reg ().reg_rtx (),
                                    index);
          else
            new_val = expand_plus (current_addr ().base_reg ().reg_rtx (),
                                   index);
          log_msg ("reg mod new val (2) = ");
          log_rtx (new_val);
          log_msg ("\n");
        }
      else
        {
          new_val = current_addr ().base_reg ().reg_rtx ();
          log_msg ("reg mod new val (3) = ");
          log_rtx (new_val);
          log_msg ("\n");
        }

      new_val = expand_plus (new_val, current_addr ().disp ());
    }

  set_insn (emit_move_insn (reg ().reg_rtx (), new_val));
  return insn_sequence_started;
}

// Find the value that REG was last set to, starting the search from
// START_INSN.  Return that value along with the insn in which REG gets
// modified.  If the value of REG cannot be determined, return NULL.
ams::find_reg_value_result
ams::find_reg_value (rtx reg, rtx_insn* start_insn,
                     sequence::glob_insn_map& insn_el_map)
{
  // Go back through the insn list until we find the last instruction
  // that modified the register.
  rtx_insn* i;
  for (i = start_insn; i != NULL_RTX; i = prev_nonnote_insn_bb (i))
    {
      if (BARRIER_P (i)
	  || (NOTE_P (i) && NOTE_KIND (i) == NOTE_INSN_FUNCTION_BEG))
	return find_reg_value_result (addr_reg (reg), NULL_RTX, i);

      if (!INSN_P (i) || DEBUG_INSN_P (i))
	continue;

      std::pair<sequence::glob_insn_map::iterator,
                sequence::glob_insn_map::iterator> els_in_insn =
        insn_el_map.equal_range (i);

      std::pair<rtx, bool> r = find_reg_value_1 (reg, i);

      if (!r.second)
        {
          // Check if there's already a reg-mod in the sequence that
          // modifies REG.
          for (sequence::glob_insn_map::iterator els = els_in_insn.first;
               els != els_in_insn.second; ++els)
            {
              for (sequence_element::dependency_set::iterator deps =
                     els->second->dependencies ().begin ();
                   deps != els->second->dependencies ().end (); ++deps)
                {
                  if (reg_mod* rm = dyn_cast<reg_mod*> (*deps))
                    {
                      if (rm->reg () == reg)
                        return find_reg_value_result (rm);
                    }
                }
            }
          continue;
        }

      if (r.first == NULL)
        {
          if (find_regno_note (i, REG_INC, REGNO (reg)) != NULL)
            {
              // Search for auto-mod memory accesses in the current
              // insn that modify REG.
              for (sequence::glob_insn_map::iterator els = els_in_insn.first;
                   els != els_in_insn.second; ++els)
                {
                  if (mem_access* acc =
                      dyn_cast<mem_access*> (&*els->second))
                    {
                      rtx mem_addr = acc->current_addr_rtx ();
                      rtx mem_reg = XEXP (mem_addr, 0);

                      if (GET_RTX_CLASS (GET_CODE (mem_addr)) == RTX_AUTOINC
                          && REG_P (mem_reg) && REGNO (mem_reg) == REGNO (reg))
                        return find_reg_value_result (addr_reg (mem_reg),
                                                      mem_addr, i, acc);
                    }
                }

              // If no access was found, search for the auto-mod
              // RTX inside the insn.
              subrtx_var_iterator::array_type array;
              FOR_EACH_SUBRTX_VAR (it, array, PATTERN (i), NONCONST)
                {
                  if (MEM_P (*it))
                    {
                      rtx mem = *it;
                      rtx mem_addr = XEXP (mem, 0);
                      if (GET_RTX_CLASS (GET_CODE (mem_addr)) == RTX_AUTOINC)
                        {
                          rtx mem_reg = XEXP (mem_addr, 0);
                          if (REG_P (mem_reg) && REGNO (mem_reg) == REGNO (reg))
                            return find_reg_value_result (
                              addr_reg (mem_reg), mem_addr, i, GET_MODE (mem));
                        }
                    }
                }
              gcc_unreachable ();
            }
          else
            {
              // The reg is modified in some unspecified way, e.g. a clobber.
              return find_reg_value_result (addr_reg (reg), NULL_RTX, i);
            }
        }
      else
        {
          if (GET_CODE (r.first) == SET)
            return find_reg_value_result (addr_reg (SET_DEST (r.first)),
                                          SET_SRC (r.first), i);
          else
            return find_reg_value_result (addr_reg (reg), NULL_RTX, i);
        }
    }

  return find_reg_value_result (addr_reg (reg), reg, i);
}

// The recursive part of find_reg_value. If REG is modified in INSN,
// return true and the SET pattern that modifies it. Otherwise, return
// false.
std::pair<rtx, bool>
ams::find_reg_value_1 (rtx reg, const_rtx insn)
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

  rtx r = const_cast<rtx> (set_of (reg, insn));
  if (r != NULL && REGNO (SET_DEST (r)) == REGNO (reg))
    return std::make_pair (r, true);

  if (INSN_P (insn)
      && (FIND_REG_INC_NOTE (insn, reg)
          || (CALL_P (insn)
              && ((REG_P (reg)
                   && REGNO (reg) < FIRST_PSEUDO_REGISTER
                   && overlaps_hard_reg_set_p (regs_invalidated_by_call,
                                               GET_MODE (reg), REGNO (reg)))
                  || find_reg_fusage (insn, CLOBBER, reg)))))
    return std::make_pair (NULL_RTX, true);

  return std::make_pair (NULL_RTX, false);
}

bool
ams::mem_load::try_replace_addr (const ams::addr_expr& new_addr)
{
  rtx prev_rtx = XEXP (*m_mem_ref, 0);

  XEXP (*m_mem_ref, 0) = new_addr.to_rtx ();

  int new_insn_code = recog (PATTERN (insn ()), insn (), NULL);

  XEXP (*m_mem_ref, 0) = prev_rtx;
  return new_insn_code >= 0;
}

bool
ams::mem_load::replace_addr (const ams::addr_expr& new_addr)
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
ams::mem_store::try_replace_addr (const ams::addr_expr& new_addr)
{
  // FIXME: same as mem_load::replace_addr.
  // move to base class? (see mem_store::replace_addr)

  rtx prev_rtx = XEXP (*m_mem_ref, 0);

  XEXP (*m_mem_ref, 0) = new_addr.to_rtx ();

  int new_insn_code = recog (PATTERN (insn ()), insn (), NULL);

  XEXP (*m_mem_ref, 0) = prev_rtx;
  return new_insn_code >= 0;
}

bool
ams::mem_store::replace_addr (const ams::addr_expr& new_addr)
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
ams::mem_operand::try_replace_addr (const ams::addr_expr& new_addr)
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
ams::mem_operand::replace_addr (const ams::addr_expr& new_addr)
{
  rtx new_rtx = new_addr.to_rtx ();
    start_sequence ();
  for (static_vector<rtx*, 16>::iterator it = m_mem_refs.begin ();
       it != m_mem_refs.end (); ++it)
    validate_change (insn (), *it, replace_equiv_address (**it, new_rtx), true);

  if (!apply_change_group ())
    {
      end_sequence ();
      return false;
    }

  rtx_insn* new_insns = get_insns ();
  end_sequence ();

  if (!mem_access::allow_new_insns && new_insns != NULL)
    {
      log_msg ("validate_change produced new insns: \n");
      log_rtx (new_insns);
      abort ();
    }

  if (new_insns != NULL)
    emit_insn_before (new_insns, insn ());

  return true;
}

bool ams::mem_access::
operator == (const sequence_element& other) const
{
  return sequence_element::operator == (other)
    && effective_addr () == effective_addr ()
    && current_addr_rtx () == ((const mem_access&)other).current_addr_rtx ()
    && current_addr () == ((const mem_access&)other).current_addr ();
}

bool ams::reg_mod::
operator == (const sequence_element& other) const
{
  return sequence_element::operator == (other)
    && reg () == ((const reg_mod&)other).reg ()
    && value () == ((const reg_mod&)other).value ()
    && current_addr () == ((const reg_mod&)other).current_addr ();
}

bool ams::reg_barrier::
operator == (const sequence_element& other) const
{
  return sequence_element::operator == (other)
    && reg () == ((const ams::reg_barrier&)other).reg ();
}

bool ams::reg_use::
operator == (const sequence_element& other) const
{
  return sequence_element::operator == (other)
    && reg () == ((const reg_use&)other).reg ()
    && current_addr () == ((const reg_use&)other).current_addr ();
}

// Return a non_mod_addr if it can be created with the given scale and
// displacement.  Otherwise, return an invalid address.
ams::addr_expr
ams::check_make_non_mod_addr (addr_reg base_reg, addr_reg index_reg,
                              HOST_WIDE_INT scale, HOST_WIDE_INT disp)
{
  if (((base_reg.reg_rtx () || index_reg.reg_rtx ())
       && sext_hwi (disp, GET_MODE_PRECISION (Pmode)) != disp)
      || sext_hwi (scale, GET_MODE_PRECISION (Pmode)) != scale)
    return addr_expr ();

  return non_mod_addr (base_reg, index_reg, scale, disp);
}

// Extract an addr_expr of the form (base_reg + index_reg * scale + disp)
// from the rtx X.
// If EL is not null, trace back the effective addresses of the
// registers in X (starting from EL) and insert a reg mod into SEQ.
// for every address modifying insn that was used.
// If CURR_INSN is not null, trace back the reg values starting from
// CURR_INSN, but don't add reg-mods to the sequence.
ams::addr_expr
ams::rtx_to_addr_expr (rtx x, machine_mode mem_mode,
                       ams::sequence* seq,
                       ams::sequence_element* el,
                       rtx_insn* curr_insn, basic_block curr_bb)
{
  const bool trace_back_addr = seq != NULL && (el != NULL || curr_insn != NULL);

  if (x == NULL_RTX)
    return addr_expr ();

  addr_expr op0;
  addr_expr op1;
  HOST_WIDE_INT disp;
  HOST_WIDE_INT scale;
  addr_reg base_reg, index_reg;

  rtx_code code = GET_CODE (x);

  // If X is an arithmetic operation, first create ADDR_EXPR structs
  // from its operands. These will later be combined into a single ADDR_EXPR.
  if (code == PLUS || code == MINUS || code == MULT || code == ASHIFT)
    {
      op0 = rtx_to_addr_expr (XEXP (x, 0), mem_mode, seq, el,
                              curr_insn, curr_bb);
      op1 = rtx_to_addr_expr (XEXP (x, 1), mem_mode, seq, el,
                              curr_insn, curr_bb);
      if (op0.is_invalid () || op1.is_invalid ())
        return addr_expr ();
    }
  else if (code == NEG)
    {
      op1 = rtx_to_addr_expr (XEXP (x, 0), mem_mode, seq, el,
                              curr_insn, curr_bb);
      if (op1.is_invalid ())
        return addr_expr ();
    }

  else if (GET_RTX_CLASS (code) == RTX_AUTOINC)
    {
      addr_type_t mod_type;
      bool apply_post_disp =
        !trace_back_addr || el == NULL || !el->is_mem_access ();

      switch (code)
        {
        case POST_DEC:
          disp = apply_post_disp ? -GET_MODE_SIZE (mem_mode) : 0;
          mod_type = post_mod;
          break;
        case POST_INC:
          disp = apply_post_disp ? GET_MODE_SIZE (mem_mode) : 0;
          mod_type = post_mod;
          break;
        case PRE_DEC:
          disp = -GET_MODE_SIZE (mem_mode);
          mod_type = pre_mod;
          break;
        case PRE_INC:
          disp = GET_MODE_SIZE (mem_mode);
          mod_type = pre_mod;
          break;
        case POST_MODIFY:
          {
            addr_expr a = rtx_to_addr_expr (XEXP (x, apply_post_disp ? 1 : 0),
                                            mem_mode, seq, el,
                                            curr_insn, curr_bb);
	    return a.is_invalid () ? addr_expr ()
				   : post_mod_addr (a.base_reg (), a.disp ());
          }
        case PRE_MODIFY:
          {
            addr_expr a = rtx_to_addr_expr (XEXP (x, 1), mem_mode, seq,
                                            el, curr_insn, curr_bb);
	    return a.is_invalid () ? addr_expr ()
				   : pre_mod_addr (a.base_reg (), a.disp ());
          }

        default:
          return addr_expr ();
        }

      op1 = rtx_to_addr_expr (XEXP (x, 0), mem_mode, seq, el,
                              curr_insn, curr_bb);
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
	  find_reg_value_result prev_val =
            find_reg_value (x,
                            el ? prev_nonnote_insn_bb (el->insn ()) : curr_insn,
                            seq->g_insn_el_map ());

          // If the found reg modification already has a sequence element,
          // use that element's addresses.
          if (prev_val.rm != NULL)
            {
              if (el != NULL)
                {
                  el->add_dependency (prev_val.rm);
                  prev_val.rm->add_dependent_el (el);
                  if (prev_val.rm->effective_addr ().is_invalid ())
                    return make_reg_addr (addr_reg (x, prev_val.rm->insn ()));
                  return prev_val.rm->effective_addr ();
                }
              else if (prev_val.rm->insn () == NULL)
                return prev_val.rm->effective_addr ();
            }

          rtx value = prev_val.value;
          rtx_insn* mod_insn = prev_val.insn;

          // Stop expanding the reg if the reg can't be expanded any further.
          if (value != NULL_RTX && REG_P (value) && REGNO (value) == REGNO (x))
            {
              // If the current BB has only one predecessor BB, trace back
              // the reg's effective address through that BB.
              rtx_insn* insn = BB_HEAD (curr_bb);
              addr_expr reg_effective_addr = make_reg_addr (addr_reg (x, insn));
              if (single_pred_p (curr_bb))
                {
                  basic_block prev_bb =
                    single_pred (curr_bb);
                  reg_effective_addr =
                    rtx_to_addr_expr (
                      x, prev_val.is_auto_mod ? prev_val.acc_mode : mem_mode,
                      seq, BB_END (prev_bb), prev_bb);

                  // Use the unexpanded reg if the traced-back value is
                  // too complex.
                  if (reg_effective_addr.is_invalid () && el != NULL)
                    reg_effective_addr = make_reg_addr (addr_reg (x, insn));
                }
              if (el != NULL)
                {
                  // Add to the sequence's start a reg mod that sets the reg
                  // to itself. This will be used by the address modification
                  // generator as a starting address.
                  sequence_element* new_reg_mod = &*seq->insert_unique (
                        make_ref_counted<reg_mod> ((rtx_insn*)NULL, x, x,
                                                   make_reg_addr (addr_reg (x)),
                                                   reg_effective_addr));
                  el->add_dependency (new_reg_mod);
                  new_reg_mod->add_dependent_el (el);
                }
              return reg_effective_addr;
            }

	  addr_expr reg_curr_addr = prev_val.is_auto_mod ? make_reg_addr (x)
                                   : rtx_to_addr_expr (value, mem_mode);

          reg_mod* new_reg_mod = NULL;

          if (el != NULL)
            {
              // Insert the modifying insn into the sequence as a reg mod.
              new_reg_mod = as_a<reg_mod*> (&*seq->insert_unique (
                    make_ref_counted<reg_mod> (mod_insn, prev_val.reg, value,
                                               reg_curr_addr)));

              el->add_dependency (new_reg_mod);
              new_reg_mod->add_dependent_el (el);
              new_reg_mod->set_auto_mod_acc (prev_val.acc);
            }

	  // Expand the register's value further.
	  addr_expr reg_effective_addr = rtx_to_addr_expr (
		value, prev_val.is_auto_mod ? prev_val.acc_mode : mem_mode,
		seq, new_reg_mod, prev_nonnote_insn_bb (mod_insn), curr_bb);

          if (el != NULL)
            {
              if (reg_curr_addr.is_invalid ()
                  || reg_effective_addr.is_invalid ())
                new_reg_mod->set_optimization_disabled ();

              // If the expression is something AMS can't handle, use the
              // original reg instead.
              if (reg_effective_addr.is_invalid ())
                reg_effective_addr = make_reg_addr (addr_reg (x, mod_insn));

              seq->start_addresses ().remove (new_reg_mod);
              new_reg_mod->set_effective_addr (reg_effective_addr);
              seq->start_addresses ().add (new_reg_mod);
            }

          return reg_effective_addr;
        }
      return make_reg_addr (addr_reg (x));

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
      index_reg = invalid_reg;
      scale = 0;

      // If the same reg is used in both addresses, try to
      // merge them into one reg.
      if (op0.base_reg () == op1.base_reg ())
        {
	  if (op0.has_no_index_reg ())
            {
              op1 = check_make_non_mod_addr (invalid_reg, op1.index_reg (),
                                             op1.scale (), op1.disp ());
              op0 = check_make_non_mod_addr (invalid_reg, op0.base_reg (),
                                             2, op0.disp ());
            }
          else if (op1.has_no_index_reg ())
            {
              op0 = check_make_non_mod_addr (invalid_reg, op0.index_reg (),
                                             op0.scale (), op0.disp ());
              op1 = check_make_non_mod_addr (invalid_reg, op1.base_reg (),
                                             2, op1.disp ());
              if (op1.is_invalid ())
                break;
            }
        }
      if (op0.base_reg () == op1.index_reg ())
        {
          op0 = check_make_non_mod_addr (invalid_reg, op0.index_reg (),
                                         op0.scale (), op0.disp ());

          op1 = check_make_non_mod_addr (op1.base_reg (), op1.index_reg (),
                                         op1.scale () + 1, op1.disp ());
          if (op1.is_invalid ())
            break;
        }
      if (op1.base_reg () == op0.index_reg ())
        {
          op1 = check_make_non_mod_addr (invalid_reg, op1.index_reg (),
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
          op1 = check_make_non_mod_addr (op1.base_reg (), invalid_reg,
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
      if (index_reg == invalid_reg)
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
          op1 = check_make_non_mod_addr (invalid_reg, invalid_reg, 0, mul);
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

      return check_make_non_mod_addr (invalid_reg, index_reg,
                                      scale, op0.disp () * op1.disp ());

    default:
      // Any other kind of expression is too complex to be represented by an
      // addr_expr. For these expressions, we still have go through the
      // sub-expressions in order to find the dependencies.
      if (trace_back_addr && (UNARY_P (x) || ARITHMETIC_P (x)))
        {
          for (int i = 0; i < GET_RTX_LENGTH (code); i++)
            if (!MEM_P (XEXP (x, i)))
              rtx_to_addr_expr (XEXP (x, i), mem_mode, seq, el,
                                curr_insn, curr_bb);
        }
      break;
    }
  return addr_expr ();
}

unsigned int
ams::execute (function* fun)
{
  // running this pass after register allocation doesn't work yet.
  // all we can do is some analysis and log dumps.
  if (!can_create_pseudo_p () && dump_file == NULL)
    return 0;

  log_msg ("sh-ams pass\n");
  log_options (m_options);
  log_msg ("\n\n");
  mem_access::allow_new_insns = m_options.allow_mem_addr_change_new_insns;

//  df_set_flags (DF_DEFER_INSN_RESCAN); // needed?

  df_note_add_problem ();
  df_analyze ();

  std::list<sequence> sequences;

  // A map that shows which sequence elements an insn contains.
  sequence::glob_insn_map insn_el_map;

  // Stores the ID of the next element that gets inserted into a sequence.
  unsigned next_element_id = 0;

  log_msg ("extracting access sequences\n");
  basic_block bb;
  FOR_EACH_BB_FN (bb, fun)
    {
      rtx_insn* i;

      log_msg ("BB #%d:\n", bb->index);
      log_msg ("finding mem accesses\n");

      // Create a new sequence from the mem accesses in this BB.
      sequences.push_back (sequence (bb, insn_el_map, &next_element_id));
      sequence& seq = sequences.back ();

      // Add the mem accesses from this BB to the sequence.
      FOR_BB_INSNS (bb, i)
        {
          if (!INSN_P (i) || !NONDEBUG_INSN_P (i))
            continue;

          seq.find_mem_accesses (i);
         }

      for (mem_acc_iter m (seq.begin<mem_match> ()),
	     m_end (seq.end<mem_match> ()); m != m_end; ++m)
        {
          m->set_effective_addr (rtx_to_addr_expr (m->current_addr_rtx (),
                                                   m->mach_mode (), &seq, &*m));
          if (m->effective_addr ().is_invalid ())
            m->set_optimization_disabled ();
        }
    }

  std::list<ref_counting_ptr<sequence_element> > original_reg_mods;
  log_msg ("\nprocessing extracted sequences\n");
  for (std::list<sequence>::iterator it = sequences.begin ();
       it != sequences.end (); ++it)
    {
      sequence& seq = *it;

      if (seq.empty () || seq.has_no_insns ())
        continue;

      log_msg ("find_addr_reg_mods\n");
      seq.find_addr_reg_mods ();

      // Add the sequence's reg-mods to the original reg-mod list.
      for (reg_mod_iter rm (seq.begin<reg_mod_match> ()),
             rm_end (seq.end<reg_mod_match> ()); rm != rm_end; ++rm)
        original_reg_mods.push_back (ref_counting_ptr<sequence_element> (&*rm));

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
    }

  if (m_options.split_sequences)
    {
      log_msg ("splitting sequences\n");
      for (std::list<sequence>::iterator it = sequences.begin ();
           it != sequences.end ();)
        {
          sequence& seq = *it;

          if (seq.empty () || seq.has_no_insns ())
            {
              ++it;
              continue;
            }

          log_sequence (seq, false);
          log_msg ("\n\n");
          log_msg ("split_access_sequence\n");
          it = sequence::split (it, sequences);
        }
    }

  std::set<sequence*> seqs_to_skip;
  log_msg ("\nprocessing split sequences\n");
  for (std::list<sequence>::iterator it = sequences.begin ();
       it != sequences.end (); ++it)
    {
      sequence& seq = *it;

      log_sequence (seq, false);
      log_msg ("\n\n");

      if (seq.empty () || seq.has_no_insns ())
        {
          log_msg ("skipping empty sequence\n");
          continue;
        }

      if (seq.begin<mem_match> () == seq.end<mem_match> ())
        {
          log_msg ("skipping sequence as it contains no memory accesses\n");

          // Mark all reg-uses of this sequence unoptimizable.
	  std::for_each (seq.begin<reg_use_match> (), seq.end<reg_use_match> (),
			 std::mem_fun_ref (&sequence_element
					    ::set_optimization_disabled));
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
            {
              seqs_to_skip.insert (&seq);
              std::for_each (seq.begin (), seq.end (), std::mem_fun_ref (
                &sequence_element::set_optimization_disabled));
              continue;
            }

	  log_msg ("continuing anyway\n");
        }
    }

  log_msg ("marking unoptimizable elements\n");
  unsigned found;
  do
    {
      found = 0;
      for (std::list<sequence>::iterator it = sequences.begin ();
           it != sequences.end (); ++it)
        {
          sequence& seq = *it;

          log_msg ("find_unoptimizable_elements\n");
          found += seq.find_unoptimizable_elements ();
          log_sequence (seq, false);
          log_msg ("\n\n");
        }
    }
  while (found > 0);

  // running this pass after register allocation doesn't work yet.
  // stop here before making any modifications.
  // after register allocation, the things AMS can do are somewhat limited.
  // things that seem safe to do:
  //   - replacing addresses with the re-calculated effective address in
  //     order to eliminate reg-mods.
  //   - removing said reg-mods if they aren't referenced by anything else.
  //   - introducing reg-mods that modify an address register "in-place"
  //     i.e. without requiring a new register, e.g. "reg += const"
  //
  // some things to watch out for after register allocation:
  //   - stack/frame pointer modifications should be kept.  it's OK to merge
  //     an stack pointer reg-mod with a auto-mod load/store, but the effective
  //     reg-mod must be kept.
  if (!can_create_pseudo_p ())
    {
      seqs_to_skip.clear ();
      sequences.clear ();
      m_delegate.clear_custom_data ();
      return 0;
    }

  std::map<sequence*, sequence> prev_sequences;

  log_msg ("generating new address modifications\n");
  for (std::list<sequence>::iterator it = sequences.begin ();
       it != sequences.end (); ++it)
    {
      sequence& seq = *it;

      if (seqs_to_skip.find (&seq) != seqs_to_skip.end ())
        continue;

      int original_cost = seq.cost ();

      log_sequence (seq, true);
      log_msg ("\n\n");

      // Copy the sequence in case we'll want to revert the changes.
      sequence copy (seq);
      copy.set_original_seq (&seq);
      prev_sequences.insert (std::make_pair (&seq, copy));

      log_msg ("gen_address_mod\n");
      if (!seq.gen_address_mod (m_delegate, m_options.base_lookahead_count))
        {
          log_msg ("gen_address_mod failed,  not modifying\n");
          seqs_to_skip.insert (&seq);
          seq.revert (prev_sequences);
          continue;
        }

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
              seq.revert (prev_sequences);
            }
	  else
	    log_msg ("  modifying anyway\n");
	}
    }

  log_msg ("\nremoving unused reg-mod insns\n");
  std::multimap<rtx_insn*, sequence*> insns_to_delete;
  for (trv_iterator<deref<
	std::list<ref_counting_ptr<sequence_element> >::iterator> >
       i (original_reg_mods.begin ()), i_end (original_reg_mods.end ());
       i != i_end; )
    {
      if (i->insn () == NULL)
        {
          ++i;
          continue;
        }

      // A reg-mod is unused if it's only present in the pre-optimization
      // sequences.
      bool found = false;
      for (std::set<sequence*>::iterator it = i->sequences ().begin ();
           it != i->sequences ().end (); ++it)
        {
          sequence& el_seq = **it;
          if (el_seq.original_seq () == NULL && el_seq.contains (&*i))
            {
              found = true;
              break;
            }
        }
      if (found)
        {
          ++i;
          continue;
        }

      log_sequence_element (*i);
      log_msg ("\n");

      // Keep the reg-mod's insn if there's a sequence that doesn't get updated.
      if (std::find_if (i->sequences ().begin (), i->sequences ().end (),
			element_is_in (seqs_to_skip))
          != i->sequences ().end ())
        {
          log_msg ("reg-mod is used by a sequence that won't be updated\n");
          log_msg ("keeping insn\n");

          // In this case, all other sequences that used this reg-mod
          // can't be updated either.
          for (std::set<sequence*>::iterator it = i->sequences ().begin ();
               it != i->sequences ().end (); ++it)
            {
              sequence& el_seq = **it;
              if (el_seq.original_seq () == NULL
                  && seqs_to_skip.find (&el_seq) == seqs_to_skip.end ())
                {
                  if (dump_file != NULL)
                    {
                      log_msg ("sequence ");
                      dump_addr (dump_file, "", (const void*)&el_seq);
                      log_msg (" won't be modified either\n");
                    }
                  seqs_to_skip.insert (&el_seq);
                  el_seq.revert (prev_sequences);
                }
            }
        }
      else if (i->insn ())
        {
          if (control_flow_insn_p (i->insn ()))
            {
              log_msg ("reg-mod's insn is a jump or call\n");
              log_msg ("keeping insn\n");
              goto next;
            }

          // Also keep the insn if it has other sequence elements in it.
          std::pair<sequence::glob_insn_map::iterator,
                    sequence::glob_insn_map::iterator> els_in_insn =
            insn_el_map.equal_range (i->insn ());
          for (sequence::glob_insn_map::iterator els = els_in_insn.first;
               els != els_in_insn.second; ++els)
            {
              if (els->second != &*i
                  // For unspecified reg-uses it doesn't matter
                  // whether the insn exists, so we can remove it.
                  && (els->second->type () != type_reg_use
                      || ((reg_use*)&*els->second)->reg_ref () != NULL))
                {
                  log_msg ("reg-mod's insn has other elements\n");
                  log_msg ("keeping insn\n");
                  goto next;
                }
            }
          for (std::set<sequence*>::iterator seqs = i->sequences ().begin ();
               seqs != i->sequences ().end (); ++seqs)
            if ((*seqs)->original_seq () == NULL)
              insns_to_delete.insert (std::make_pair (i->insn (), *seqs));
        }
    next:
      i = make_of_type (i, original_reg_mods.erase (i));
    }

  // Remove the unused reg-mods' insns only if all of their
  // sequences will get updated.
  std::multimap<rtx_insn*, sequence*>::iterator prev = insns_to_delete.begin ();
  while (1)
    {
      unsigned insert_count = 0;
      for (std::multimap<rtx_insn*, sequence*>::iterator it =
             insns_to_delete.begin (); it != insns_to_delete.end ();)
        {
          rtx_insn* i = it->first;
          sequence* seq = it->second;

          if (i != prev->first)
            prev = it;

          // If one sequence isn't updated, all other sequences
          // that used this reg-mod can't be updated either.
          if (seqs_to_skip.find (seq) != seqs_to_skip.end ())
            for (it = prev; it != insns_to_delete.end () && it->first == i;
                 ++it)
              {
                seq = it->second;
                if (seqs_to_skip.find (seq) == seqs_to_skip.end ())
                  {
                    seqs_to_skip.insert (seq);
                    seq->revert (prev_sequences);
                    ++insert_count;
                  }
              }
          else
            ++it;
        }
      // Repeat until no new sequences got added to SEQS_TO_SKIP.
      if (insert_count == 0)
        break;
    }
  for (std::multimap<rtx_insn*, sequence*>::iterator it =
         insns_to_delete.begin (); it != insns_to_delete.end ();)
    {
      rtx_insn* i = it->first;
      sequence* seq = it->second;

      if (seqs_to_skip.find (seq) == seqs_to_skip.end ())
        set_insn_deleted (i);
      while (it != insns_to_delete.end () && it->first == i)
        ++it;
    }

  prev_sequences.clear ();

  log_msg ("\nupdating sequence insns\n");
  for (std::list<sequence>::iterator it = sequences.begin ();
       it != sequences.end (); ++it)
    {
      sequence& seq = *it;
      if (seqs_to_skip.find (&seq) != seqs_to_skip.end ())
        continue;

      if (m_options.remove_reg_copies)
        {
          log_sequence (seq, false);
          log_msg ("\nremoving unnecessary reg copies\n");
          seq.eliminate_reg_copies ();
        }

      log_sequence (seq, false);
      log_msg ("\nupdating insns\n");
      seq.update_insn_stream ();
      log_msg ("\n\n");
    }

  seqs_to_skip.clear ();
  sequences.clear ();


  df_note_add_problem ();
  df_chain_add_problem (DF_DU_CHAIN + DF_UD_CHAIN);
  df_analyze ();

  // Eliminate reg-reg copies that AMS might have introduced.
  // FIXME: Pass a list of reg-reg copies to analyze to avoid walking
  // over all the insns.
  // FIXME: On SH this seems to cause more R0 spill failures, thus disabled
  // and not fully tested.
  // propagate_reg_reg_copies (fun);

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
	      check_add_incdec_notes (i);
	    }
	}
    }

  m_delegate.clear_custom_data ();
  log_return (0, "\n\n");
}

static int
non_side_effect_defs_count (rtx reg)
{
  int count = 0;

  for (df_ref d = DF_REG_DEF_CHAIN (REGNO (reg)); d != NULL;
       d = DF_REF_NEXT_REG (d))
    if (!DF_REF_IS_ARTIFICIAL (d)
	&& !DF_REF_FLAGS_IS_SET (d, DF_REF_PRE_POST_MODIFY))
      count += 1;

  return count;
}

struct df_ref_insn_compare_less
{
  bool operator () (df_ref a, df_ref b) const
  {
    return DF_REF_INSN (a) < DF_REF_INSN (b);
  }
};

struct df_ref_insn_compare_equal
{
  bool operator () (df_ref a, df_ref b) const
  {
    return DF_REF_INSN (a) == DF_REF_INSN (b);
  }
};

static bool
replace_reg (rtx old_reg, rtx new_reg, rtx_insn* insn)
{
  // First replace and validate all rtx'es in the insn pattern.
  if (validate_replace_rtx_part_nosimplify (old_reg, new_reg, &PATTERN (insn),
					    insn))
    {
      // And if that worked, replace the remaining rtx'es in insn notes etc.
      replace_rtx (insn, old_reg, new_reg, true);
      return true;
    }
  else
    return false;
}

void
ams::propagate_reg_reg_copies (function* fun)
{
  log_msg ("propagate_reg_reg_copies\n");

  std::vector<df_ref> reg_uses;

  basic_block bb;
  FOR_EACH_BB_FN (bb, fun)
    {
      rtx_insn* i;
      FOR_BB_INSNS (bb, i)
	{
	  if (!INSN_P (i) || !NONDEBUG_INSN_P (i))
	    continue;

	  // Look for insns that look like this:
	  //	(set (reg:Pmode aaa) (reg:Pmode bbb))
	  //	(expr_list:REG_DEAD (reg:Pmode bbb) (nil))

	  // However, ignore sets to hard-regs, assuming that there's a good
	  // reason why those are hard-regs, like function return values
	  // or arguments for special lib functions.  We could also look for
	  // some following insn that uses the hardreg to be sure...
	  // Also ignore sets of hard-reg sources, as those might propagate
	  // function arg values into the function body which sometimes is
	  // not so good.
	  rtx set = single_set (i);
	  if (set == NULL)
	    continue;

	  rtx set_src = SET_SRC (set);
	  rtx set_dst = SET_DEST (set);

	  if (REG_P (set_src) && REG_P (set_dst) && GET_MODE (set_src) == Pmode
	      && find_regno_note (i, REG_DEAD, REGNO (set_src)) != NULL
	      && !HARD_REGISTER_P (set_dst)
	      && !HARD_REGISTER_P (set_src)
	      && !REG_FUNCTION_VALUE_P (set_dst)
	      && non_side_effect_defs_count (set_dst) == 1)
	    {
	      log_msg ("found reg-reg copy insn:\n");
	      log_insn (i);

	      // Replace the set_dst reg with the set_src reg in each insn
	      // where set_dst is used.  Because the reg can be present
	      // in multiple places of the same insn, we use a change
	      // group for each insn.
	      reg_uses.clear ();

	      for (df_ref d = DF_REG_USE_CHAIN (REGNO (set_dst)); d != NULL;
		   d = DF_REF_NEXT_REG (d))
		reg_uses.push_back (d);

	      // FIXME: DF probably already has something for walking the
	      // insns that contain reg uses, but I can't spot it now ...
	      std::sort (reg_uses.begin (), reg_uses.end (),
			 df_ref_insn_compare_less ());

	      std::vector<df_ref>::iterator using_insn_end =
		std::unique (reg_uses.begin (), reg_uses.end (),
			     df_ref_insn_compare_equal ());

	      int ng_count = 0;

	      for (std::vector<df_ref>::iterator using_insn = reg_uses.begin ();
		   using_insn != using_insn_end; ++using_insn)
		if (!replace_reg (set_dst, set_src, DF_REF_INSN (*using_insn)))
		  ++ng_count;

	      if (ng_count == 0)
		set_insn_deleted (i);

	      log_msg ("\n");
	    }
	}
    }
}
