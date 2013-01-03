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

/* custom C definitions */
#include <cdefs.h>

#include <utility>
using std::pair;
using std::make_pair;

#include <string>
using std::string;
typedef string Atom;
typedef Atom* Atom_ptr;

#include <sstream>
using std::ostringstream;

#include <iostream>
using std::istream;
using std::ostream;
using std::cout;
using std::cerr;
using std::endl;
using std::flush;

#include <list>
using std::list;

#include <vector>
using std::vector;

#include <stack>
using std::stack;

#include <set>
using std::set;

#include <boost/unordered_set.hpp>
using boost::unordered_set;

#include <boost/unordered_map.hpp>
using boost::unordered_map;

#include <boost/regex.hpp>
using boost::regex;
using boost::cmatch;
using boost::regex_match;

#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_comparison.hpp>
using boost::tuple;

/* logging support using ezlogger (cfr. http://axter.com/ezlogger/) */
#include <logging.hh>

#include <exception>
using std::exception;

class Exception : public exception {
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

/* the base class definition, including a virtual destructor */
class IObject {
public:
    virtual ~IObject()
    {}
};

class Object : public IObject {
};

/* internal tokens, defined in common.cc */
extern const char *FALSE_TOKEN;
extern const char *TRUE_TOKEN;
extern const char *BOOL_TOKEN;
extern const char *UNSIGNED_TOKEN;
extern const char *SIGNED_TOKEN;
extern const char *FIXED_TOKEN;
extern const char *INTEGER_TOKEN;
extern const char *TEMPORAL_TOKEN;
extern const char *MAIN_TOKEN;

#endif
