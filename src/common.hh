/*
 * @file common.hh
 * @brief System wide definitions
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/

#ifndef COMMON_H
#define COMMON_H

#include <cassert>
#include <cstdlib>
#include <exception>
#include <utility>
#include <string>
#include <sstream>
#include <iostream>
#include <vector>
#include <stack>
#include <set>

#include <boost/unordered_set.hpp>
#include <boost/unordered_map.hpp>

#include <boost/regex.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_comparison.hpp>

using boost::unordered_map;
using boost::unordered_set;

using boost::regex;
using boost::cmatch;
using boost::regex_match;

using boost::tuple;

using std::pair;
using std::make_pair;

using std::string;
using std::ostringstream;
using std::istream;
using std::ostream;
using std::vector;
using std::stack;
using std::set;

using std::cout;
using std::cerr;
using std::endl;
using std::flush;

/* custom base definitions */
#include <base.hh>

class UnsupportedOperatorException : public Exception {
  virtual const char* what() const throw() {
    return "Unsupported operator";
  }
};

class FileInputException : public Exception {
    virtual const char* what() const throw() {
        ostringstream oss;
        oss << "Can not read file '" << f_filename << "'";
        return oss.str().c_str();
    }

    string f_filename;

public:
    FileInputException(const string &filename)
        : f_filename(filename)
    {}

    virtual ~FileInputException() throw()
    {}
};

struct PtrHash {
  inline long operator() (void* ptr) const
  { return (long)(ptr); }

};

struct PtrEq {
  inline bool operator() (const void* x,
                          const void* y) const
  { return x == y; }
};

// logging support using ezlogger (cfr. http://axter.com/ezlogger/)
#include <logging.hh>

// reserved for numeric and word constant values (this has to match
// cudd reprentation for ADD leaves).
typedef long value_t;

typedef enum {
  BINARY = 2,
  OCTAL = 8,
  DECIMAL = 10,
  HEXADECIMAL = 16
} base_t;

inline char base_char(base_t base)
{
  switch (base) {
  case BINARY: return 'b';
  case OCTAL: return 'o';
  case DECIMAL: return 'd';
  case HEXADECIMAL: return 'h';
  default: assert (0); // unexpected;
  }
}

inline string to_base(value_t value, base_t base)
{
  static const char alphabet[] = "0123456789abcdefgh";
  std::string result;

  while(value) {
    result += alphabet[value % base];
    value /= base;
  }

  return string(result.rbegin(), result.rend());
}

typedef std::string Atom;
typedef Atom* Atom_ptr;

#endif
