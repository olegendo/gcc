#ifndef includegoard_gcc_sh_static_rtx_includeguard
#define includegoard_gcc_sh_static_rtx_includeguard

#include "rtl.h"

// the RTX_CODE_SIZE macro uses the rtx_code_size array, which can't be
// used as a template parameter.  here generate the same table with traits.

template <rtx_code Code> struct rtx_size_traits;


#define DEF_RTL_EXPR(ENUM, NAME, FORMAT, CLASS)				\
template<> struct rtx_size_traits<ENUM>					\
{									\
  enum									\
  {									\
    data_size = ((ENUM) == CONST_INT || (ENUM) == CONST_DOUBLE		\
	  || (ENUM) == CONST_FIXED || (ENUM) == CONST_WIDE_INT)		\
	 ? (sizeof FORMAT - 1) * sizeof (HOST_WIDE_INT)			\
	 : (ENUM) == REG						\
	 ? sizeof (reg_info)						\
	 : (sizeof FORMAT - 1) * sizeof (rtunion),			\
									\
    header_size = RTX_HDR_SIZE						\
  };									\
};

#include "rtl.def"
#undef DEF_RTL_EXPR


template <rtx_code Code> class tmp_rtx
{
public:
  tmp_rtx (machine_mode mode = VOIDmode)
  {
    ctor (mode);
  }

  template <typename A0> tmp_rtx (machine_mode mode, const A0& a0)
  {
    ctor (mode);
    XEXP (&m_rtx, 0) = const_cast<rtx_def*> ((const rtx_def*)a0);
  }

  template <typename A0, typename A1>
  tmp_rtx (machine_mode mode, const A0& a0, const A1& a1)
  {
    ctor (mode);
    XEXP (&m_rtx, 0) = const_cast<rtx_def*> ((const rtx_def*)a0);
    XEXP (&m_rtx, 1) = const_cast<rtx_def*> ((const rtx_def*)a1);
  }

  template <typename A0, typename A1, typename A2>
  tmp_rtx (machine_mode mode, const A0& a0, const A1& a1, const A2& a2)
  {
    ctor (mode);
    XEXP (&m_rtx, 0) = const_cast<rtx_def*> ((const rtx_def*)a0);
    XEXP (&m_rtx, 1) = const_cast<rtx_def*> ((const rtx_def*)a1);
    XEXP (&m_rtx, 2) = const_cast<rtx_def*> ((const rtx_def*)a2);
  }

  operator rtx_def* (void) { return &m_rtx; }
  operator const rtx_def* (void) const { return &m_rtx; }

private:
  struct rtx_with_data : public rtx_def
  {
    int data[(rtx_size_traits<Code>::data_size + 1)/sizeof (int)];
  };

  rtx_with_data m_rtx;

  void ctor (machine_mode mode = VOIDmode)
  {
    std::memset (&m_rtx, 0, RTX_HDR_SIZE);
    PUT_CODE (&m_rtx, Code);
    PUT_MODE_RAW (&m_rtx, mode);
  }
};

// ----------------------------------------------------------------------------
// specialization for CONST_INT

template<> class tmp_rtx<CONST_INT>
{
public:
  tmp_rtx (HOST_WIDE_INT arg)
  {
    std::memset (&m_rtx, 0, RTX_HDR_SIZE);
    PUT_CODE (&m_rtx, CONST_INT);
    PUT_MODE_RAW (&m_rtx, VOIDmode);
    XWINT (&m_rtx, 0) = arg;
  }

  operator rtx_def* (void) { return &m_rtx; }
  operator const rtx_def* (void) const { return &m_rtx; }

private:
  rtx_def m_rtx;
};

// ----------------------------------------------------------------------------
// specialization for REG

template<> class tmp_rtx<REG>
{
public:
  tmp_rtx (machine_mode mode, unsigned int regno)
  {
    std::memset (&m_rtx, 0, RTX_HDR_SIZE);
    PUT_CODE (&m_rtx, REG);
    set_mode_and_regno (&m_rtx, mode, regno);
    REG_ATTRS (&m_rtx) = NULL;
    ORIGINAL_REGNO (&m_rtx) = regno;
  }

  operator rtx_def* (void) { return &m_rtx; }
  operator const rtx_def* (void) const { return &m_rtx; }

private:
  rtx_def m_rtx;
};
#endif // includegoard_gcc_sh_static_rtx_includeguard
