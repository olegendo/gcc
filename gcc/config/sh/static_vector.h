#ifndef includeguard_gcc_sh_static_vector_includeguard
#define includeguard_gcc_sh_static_vector_includeguard

template <typename value_type, std::size_t max_data_size>
class static_vector
{
 public:
  // copied from std::array
  typedef value_type*			      pointer;
  typedef const value_type*                       const_pointer;
  typedef value_type&                   	      reference;
  typedef const value_type&             	      const_reference;
  typedef value_type*          		      iterator;
  typedef const value_type*			      const_iterator;
  typedef unsigned int                    	      size_type;
  typedef std::ptrdiff_t                   	      difference_type;
  typedef std::reverse_iterator<iterator>	      reverse_iterator;
  typedef std::reverse_iterator<const_iterator>   const_reverse_iterator;

  static_vector (void) : m_size (0) { }

  reference at (size_type pos);
  const_reference at (size_type pos) const;

  reference operator [] (size_type pos) { return m_data[pos]; }
  const_reference operator [] (size_type pos) const { return m_data[pos]; }

  reference front (void) { return m_data[0]; }
  const_reference front (void) const { return m_data[0]; }

  reference back (void) { return m_data[m_size - 1]; }
  const_reference back (void) const { return m_data[m_size - 1]; }

  pointer data (void) { return m_data; }
  const_pointer data (void) const { return m_data; }

  iterator begin (void) { return m_data; }
  const_iterator begin (void) const { return m_data; }
  const_iterator cbegin (void) const { return m_data; }

  iterator end (void) { return m_data + size (); }
  const_iterator end (void) const { return m_data + size (); }
  const_iterator cend (void) const { return m_data + size (); }

  reverse_iterator rbegin (void) { return reverse_iterator (end ()); }

  const_reverse_iterator
    rbegin (void) const { return const_reverse_iterator (end ()); }

  const_reverse_iterator
    crbegin (void) const { return const_reverse_iterator (end ()); }

  reverse_iterator rend (void) { return reverse_iterator (begin ()); }

  const_reverse_iterator
    rend (void) const { return const_reverse_iterator (begin ()); }

  const_reverse_iterator
    crend (void) const { return const_reverse_iterator (begin ()); }

  bool empty (void) const { return size () == 0; }
  size_type size (void) const { return m_size; }
  size_type max_size (void) const { return max_data_size; }
  size_type capacity (void) const { return max_data_size; }

  void clear (void) { m_size = 0; }
  void push_back (const value_type& v);
  void pop_back (void) { --m_size; }

 private:

  size_type m_size;
  value_type m_data[max_data_size];
};

#endif // includeguard_gcc_sh_static_vector_includeguard
