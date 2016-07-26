
#ifndef includeguard_gcc_sh_trv_iterator_includeguard
#define includeguard_gcc_sh_trv_iterator_includeguard

#include <iterator>
#include <algorithm>

template <typename Trv>
class trv_iterator : private Trv
{
public:
  typedef typename Trv::iterator base_iterator;
  typedef typename std::iterator_traits<base_iterator>::iterator_category iterator_category;
  typedef typename Trv::value_type value_type;
  typedef typename std::iterator_traits<base_iterator>::difference_type difference_type;
  typedef typename Trv::pointer pointer;
  typedef typename Trv::reference reference;

  trv_iterator (void) { }
  trv_iterator (const Trv& trv) : Trv (trv) { }

  template <typename II> explicit trv_iterator (II i) : m_i (i) { }
  template <typename II, typename III> explicit trv_iterator (II i, III ii) : m_i (i, ii) { }

  template <typename T> operator T (void) const { return m_i; }

  template <typename II>
  operator trv_iterator<II> (void) const
  {
    return trv_iterator<II> (m_i);
  }

  base_iterator base (void) const { return m_i; }

  void swap (trv_iterator& other) { std::swap (m_i, other.m_i); }

  trv_iterator& operator ++ (void) { ++m_i; return *this; }

  trv_iterator operator ++ (int)
  {
    trv_iterator r = *this;
    ++m_i;
    return r;
  }

  trv_iterator& operator -- (void) { --m_i; return *this; }

  trv_iterator operator -- (int)
  {
    trv_iterator r = *this;
    --m_i;
    return r;
  }

  trv_iterator operator + (difference_type n) const { return m_i + n; }
  trv_iterator& operator += (difference_type n) { m_i += n; return *this; }
  trv_iterator operator - (difference_type n) const { return m_i - n; }
  trv_iterator& operator -= (difference_type n) { m_i -= n; return *this; }

  bool operator == (const trv_iterator& rhs) const { return m_i == rhs.m_i; }
  bool operator != (const trv_iterator& rhs) const { return m_i != rhs.m_i; }
  bool operator < (const trv_iterator& rhs) const { return m_i < rhs.m_i; }
  bool operator <= (const trv_iterator& rhs) const { return m_i <= rhs.m_i; }
  bool operator > (const trv_iterator& rhs) const { return m_i > rhs.m_i; }
  bool operator >= (const trv_iterator& rhs) const { return m_i >= rhs.m_i; }

  reference operator * (void) const { return Trv::trv_reference (*m_i); }
  pointer operator -> (void) const { return Trv::trv_pointer (*m_i); }

private:
  base_iterator m_i;
};

namespace std
{
template <typename T> void
swap (trv_iterator<T>& i, trv_iterator<T>& j)
{
  i.swap (j);
}
}

// ---------------------------------------------------------------------------

template <typename Iter, typename T> struct cast
{
  typedef Iter iterator;
  typedef T value_type;
  typedef T* pointer;
  typedef T& reference;

  template <typename U> reference trv_reference (U& u) const
  {
    return (reference)u;
  }

  template <typename U> pointer trv_pointer (U& u) const
  {
    return (pointer)&u;
  }
};

// ---------------------------------------------------------------------------

namespace utils
{

template< bool B, class T = void > struct enable_if { };
template <class T> struct enable_if<true, T> { typedef T type; };

template <unsigned int N> struct dummy_array
{
  char data[N];
  dummy_array (int);
};

template <typename T> class is_iterator
{
  template <typename C> static char test ( dummy_array< sizeof (typename C::iterator_category) > );
  template <typename C> static long test (...);

public:
  enum { value = sizeof (test<T> (0)) == sizeof (char) };
};

template <typename T> struct is_pointer { enum { value = 0 }; };
template <typename T> struct is_pointer<T*> { enum { value = 1 }; };
template <typename T> struct is_pointer<const T*> { enum { value = 1 }; };

template <typename T, typename Enable = void> struct dereferenced_type;

template <typename T>
struct dereferenced_type<T, typename enable_if<!is_iterator<T>::value
					       && !is_pointer<T>::value>::type>
{
  // assuming that T is some kind of smart pointer.
  typedef typename T::element_type type;
};

template <typename T> struct dereferenced_type<T*>
{
  typedef T type;
};

template <typename T> struct dereferenced_type<const T*>
{
  typedef const T type;
};


template <typename T>
struct dereferenced_type<T, typename enable_if<is_iterator<T>::value>::type>
{
  typedef typename std::iterator_traits<T>::value_type type;
};

} // namespace utils


template <
  typename Iter,
  typename VT = typename utils::dereferenced_type<typename Iter::value_type>::type >
struct deref
{
  typedef Iter iterator;
  typedef VT value_type;
  typedef VT* pointer;
  typedef VT& reference;

  template <typename U> reference trv_reference (U& u) const
  {
    return *u;
  }

  template <typename U> pointer trv_pointer (U& u) const
  {
    return &*u;
  }
};

/*
using
template <
  typename Iter,
  typename VT = typename dereferenced_type<typename Iter::value_type>::type >
struct deref_iterator = public trv_iterator<deref_trv<Iter, VT>>;

*/

// ---------------------------------------------------------------------------

template <typename Iter, typename Pair = typename Iter::value_type>
struct pair_1st
{
  typedef Iter iterator;
  typedef typename Pair::first_type value_type;
  typedef value_type* pointer;
  typedef value_type& reference;

  reference trv_reference (Pair& p) const { return p.first; }
  pointer trv_pointer (Pair& p) const { return &p.first; }
};

template <typename Iter, typename Pair = typename Iter::value_type>
struct pair_2nd
{
  typedef Iter iterator;
  typedef typename Pair::second_type value_type;
  typedef value_type* pointer;
  typedef value_type& reference;

  reference trv_reference (Pair& p) const { return p.second; }
  pointer trv_pointer (Pair& p) const { return &p.second; }
};

#endif // includeguard_gcc_sh_trv_iterator_includeguard
