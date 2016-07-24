
#ifndef includeguard_gcc_sh_deref_iterator_includeguard
#define includeguard_gcc_sh_deref_iterator_includeguard

#include <iterator>
#include <algorithm>

template <typename Iter, typename DereferencedValueType>
class deref_iterator
{
public:
  typedef typename std::iterator_traits<Iter>::iterator_category iterator_category;
  typedef DereferencedValueType value_type;
  typedef typename std::iterator_traits<Iter>::difference_type difference_type;
  typedef DereferencedValueType* pointer;
  typedef DereferencedValueType& reference;

  deref_iterator (void) { }

  // this allows constructing a const_iterator from Iter.
  template <typename ConstIter> deref_iterator (ConstIter ci) : m_i (ci) { }

  operator Iter (void) const { return m_i; }
  const Iter& base (void) const { return m_i; }

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

  bool operator == (const Iter& rhs) const { return m_i == rhs; }
  bool operator != (const Iter& rhs) const { return m_i != rhs; }

  bool operator < (const deref_iterator& rhs) const { return m_i < rhs.m_i; }
  bool operator < (const Iter& rhs) const { return m_i < rhs; }

  bool operator <= (const deref_iterator& rhs) const { return m_i < rhs.m_i; }
  bool operator <= (const Iter& rhs) const { return m_i < rhs; }

  bool operator > (const deref_iterator& rhs) const { return m_i > rhs.m_i; }
  bool operator > (const Iter& rhs) const { return m_i > rhs; }

  bool operator >= (const deref_iterator& rhs) const { return m_i >= rhs.m_i; }
  bool operator >= (const Iter& rhs) const { return m_i >= rhs; }

  DereferencedValueType& operator * (void) const { return **m_i; }
  DereferencedValueType* operator -> (void) const { return &**m_i; }

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
