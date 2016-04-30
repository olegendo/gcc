
#ifndef includeguard_gcc_sh_filter_iterator_includeguard
#define includeguard_gcc_sh_filter_iterator_includeguard

#include <iterator>
#include <algorithm>

template <typename Iter, typename Predicate>
class filter_iterator
  : public std::iterator<std::forward_iterator_tag,
  			 typename std::iterator_traits<Iter>::value_type,
  			 typename std::iterator_traits<Iter>::difference_type,
  			 typename std::iterator_traits<Iter>::pointer,
			 typename std::iterator_traits<Iter>::reference>,
    private Predicate
{
public:
  filter_iterator (void) { }

  filter_iterator (Iter i, Iter iend, const Predicate& p = Predicate ())
  : Predicate (p)
  {
    for (; i != iend && !predicate () (*i); ++i);

    m_i = i;
    m_end = iend;
  }

  Predicate& predicate (void) { return *this; }
  const Predicate& predicate (void) const { return *this; }

  operator Iter (void) const { return m_i; }

  // FIXME: the base iterator wouldn't be needed if conversions to const
  // iterator and to const iterator of Iter worked.
  const Iter& base_iterator (void) const { return m_i; }

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

  bool operator == (const Iter& rhs) const { return m_i == rhs; }
  bool operator != (const Iter& rhs) const { return m_i != rhs; }

  typename std::iterator_traits<Iter>::reference
  operator * (void) const { return *m_i; }

  // If Iter is a raw pointer we can't invoke m_i.operator -> on it.
  typename std::iterator_traits<Iter>::pointer
  operator -> (void) const { return &*m_i; }

  // FIXME: conversion to const_iterator is not working.

private:
  Iter m_i;
  Iter m_end;
};

#endif // includeguard_gcc_sh_filter_iterator_includeguard
