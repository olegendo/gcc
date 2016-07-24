
#ifndef includeguard_gcc_sh_deref_iterator_includeguard
#define includeguard_gcc_sh_deref_iterator_includeguard

#include <iterator>
#include <algorithm>

template <typename T> struct dereferenced_type
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


template <
  typename Iter,
  typename VT = typename dereferenced_type<typename Iter::value_type>::type >
class deref_iterator
{
public:
  typedef typename std::iterator_traits<Iter>::iterator_category iterator_category;
  typedef VT value_type;
  typedef typename std::iterator_traits<Iter>::difference_type difference_type;
  typedef VT* pointer;
  typedef VT& reference;

  deref_iterator (void) { }

  explicit deref_iterator (Iter i) : m_i (i) { }

  template <typename T> operator T (void) const { return m_i; }

  template <typename II, typename DD>
  operator deref_iterator<II, DD> (void) const
  {
    return deref_iterator<II, DD> (m_i);
  }

  Iter base (void) const { return m_i; }

  void swap (deref_iterator& other) { std::swap (m_i, other.m_i); }

  deref_iterator& operator ++ (void) { ++m_i; return *this; }

  deref_iterator operator ++ (int)
  {
    deref_iterator r = *this;
    ++m_i;
    return r;
  }

  deref_iterator& operator -- (void) { --m_i; return *this; }

  deref_iterator operator -- (int)
  {
    deref_iterator r = *this;
    --m_i;
    return r;
  }

  deref_iterator operator + (difference_type n) const { return m_i + n; }
  deref_iterator& operator += (difference_type n) { m_i += n; return *this; }
  deref_iterator operator - (difference_type n) const { return m_i - n; }
  deref_iterator& operator -= (difference_type n) { m_i -= n; return *this; }

  bool operator == (const deref_iterator& rhs) const { return m_i == rhs.m_i; }
  bool operator != (const deref_iterator& rhs) const { return m_i != rhs.m_i; }
  bool operator < (const deref_iterator& rhs) const { return m_i < rhs.m_i; }
  bool operator <= (const deref_iterator& rhs) const { return m_i < rhs.m_i; }
  bool operator > (const deref_iterator& rhs) const { return m_i > rhs.m_i; }
  bool operator >= (const deref_iterator& rhs) const { return m_i >= rhs.m_i; }

  reference operator * (void) const { return (reference)**m_i; }
  pointer operator -> (void) const { return (pointer)&**m_i; }

private:
  Iter m_i;
};

namespace std
{
template <typename T, typename S> void
swap (deref_iterator<T, S>& i, deref_iterator<T, S>& j)
{
  i.swap (j);
}
}

#endif // includeguard_gcc_sh_deref_iterator_includeguard
