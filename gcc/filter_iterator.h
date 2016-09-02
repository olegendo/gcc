
#ifndef includeguard_gcc_sh_filter_iterator_includeguard
#define includeguard_gcc_sh_filter_iterator_includeguard

#include <iterator>
#include <algorithm>
#include <utility>

template <typename Iter, typename Predicate>
class filter_iterator : private Predicate
{
public:
  typedef std::forward_iterator_tag iterator_category;
  typedef typename std::iterator_traits<Iter>::value_type value_type;
  typedef typename std::iterator_traits<Iter>::difference_type difference_type;
  typedef typename std::iterator_traits<Iter>::pointer pointer;
  typedef typename std::iterator_traits<Iter>::reference reference;

  filter_iterator (void) { }

  filter_iterator (Iter i, Iter iend, const Predicate& p = Predicate ())
  : Predicate (p)
  {
    for (; i != iend && !predicate () (*i); ++i);

    m_i = i;
    m_end = iend;
  }

  template <typename II, typename III> explicit filter_iterator (II i, III iend)
  : Predicate ()
  {
    Iter ii (i);
    Iter ii_end (iend);

    for (; ii != ii_end && !predicate () (*ii); ++ii);

    m_i = ii;
    m_end = ii_end;
  }

  template <typename II> explicit
  filter_iterator (const std::pair<II, II>& i_iend)
  : Predicate ()
  {
    Iter ii (i_iend.first);
    Iter ii_end (i_iend.second);

    for (; ii != ii_end && !predicate () (*ii); ++ii);

    m_i = ii;
    m_end = ii_end;
  }
/*
  template <typename II> explicit filter_iterator (II iend)
  : Predicate (), m_i (iend), m_end (iend)
  {
  }
*/
  Predicate& predicate (void) { return *this; }
  const Predicate& predicate (void) const { return *this; }

  template <typename T> operator T (void) const { return m_i; }

  Iter base (void) const { return m_i; }

  void swap (filter_iterator& other)
  {
    std::swap (m_i, other.m_i);
    std::swap (m_end, other.m_end);
  }

  filter_iterator& operator = (Iter i)
  {
    for (; i != m_end && !predicate () (*i); ++i);

    m_i = i;
    return *this;
  }

  filter_iterator& operator ++ (void)
  {
    Iter i = m_i;
    ++i;
    for (; i != m_end && !predicate () (*i); ++i);

    m_i = i;
    return *this;
  }

  filter_iterator operator ++ (int)
  {
    filter_iterator r = *this;
    operator++ ();
    return r;
  }

  filter_iterator& operator -- (void)
  {
    Iter i = m_i;
    --i;
    for (; !predicate () (*i); --i);

    m_i = i;
    return *this;
  }

  filter_iterator operator -- (int)
  {
    filter_iterator r = *this;
    operator-- ();
    return r;
  }

  bool operator == (const filter_iterator& rhs) const { return m_i == rhs.m_i; }
  bool operator != (const filter_iterator& rhs) const { return m_i != rhs.m_i; }

  template <typename I> bool operator == (const I& i) const { return m_i == i; }
  template <typename I> bool operator != (const I& i) const { return m_i != i; }

  reference operator * (void) const { return *m_i; }

  // If Iter is a raw pointer we can't invoke m_i.operator -> on it.
  pointer operator -> (void) const { return &*m_i; }

private:
  Iter m_i;
  Iter m_end;
};

namespace std
{
template <typename T, typename S> void
swap (filter_iterator<T, S>& i, filter_iterator<T, S>& j)
{
  i.swap (j);
}
}

#endif // includeguard_gcc_sh_filter_iterator_includeguard
