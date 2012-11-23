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
#include <list>
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
using std::list;
using std::vector;
using std::stack;
using std::set;

using std::cout;
using std::cerr;
using std::endl;
using std::flush;

#include <cdefs.h>

/* time representation */
typedef unsigned step_t;

/* the base class definition, including a virtual destructor */
class IObject {
public:
    virtual ~IObject()
    {}
};

class Object : public IObject {
};

#include <exception>
class Exception : public std::exception {
public:
    virtual const char* what() const throw() =0;
    virtual ~Exception() throw() {}
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

// logging support using ezlogger (cfr. http://axter.com/ezlogger/)
#include <logging.hh>

// typedef enum {
//   BINARY = 2,
//   OCTAL = 8,
//   DECIMAL = 10,
//   HEXADECIMAL = 16
// } base_t;

// inline char base_char(base_t base)
// {
//   switch (base) {
//   case BINARY: return 'b';
//   case OCTAL: return 'o';
//   case DECIMAL: return 'd';
//   case HEXADECIMAL: return 'h';
//   default: assert (0); // unexpected;
//   }
// }

// inline string to_base(value_t value, base_t base)
// {
//   static const char alphabet[] = "0123456789abcdefgh";
//   std::string result;

//   while(value) {
//     result += alphabet[value % base];
//     value /= base;
//   }

//   return string(result.rbegin(), result.rend());
// }

typedef std::string Atom;
typedef Atom* Atom_ptr;

/* tokens */
extern const char *FALSE_TOKEN;
extern const char *TRUE_TOKEN;
extern const char *BOOL_TOKEN;
extern const char *UNSIGNED_TOKEN;
extern const char *SIGNED_TOKEN;
extern const char *INTEGER_TOKEN;
extern const char *TEMPORAL_TOKEN;
extern const char *MAIN_TOKEN;
#define DEFAULT_BITS 8

#endif
