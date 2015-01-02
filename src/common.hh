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
#include <csignal>
#include <cctype>

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
using std::ifstream;

using std::ostream;
using std::ofstream;

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

#include <algorithm>
using std::find;

#include <boost/algorithm/string.hpp>

#include <boost/unordered_set.hpp>
using boost::unordered_set;

#include <boost/unordered_map.hpp>
using boost::unordered_map;

#include <map>
using std::map;

#include <boost/thread.hpp>
using boost::thread;
using boost::thread_interrupted;

#include <boost/thread/mutex.hpp>
using boost::mutex;

#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_comparison.hpp>
using boost::tuple;
using boost::make_tuple;

#include <boost/filesystem.hpp>
using boost::filesystem::path;
using boost::filesystem::directory_iterator;
using boost::filesystem::filesystem_error;

#include <algorithm>
using std::max;

static inline bool _iff(bool a, bool b)
{ return (!(a) || (b)) && ((!b) || (a)); }

static inline bool _xor(bool a, bool b)
{ return (!(a) && (b)) || ((!b) && (a)); }

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

/* environment variables and paths */
extern const char *YASMV_HOME;
extern const char *MICROCODE_PATH;

/* internal tokens, defined in common.cc */
extern const char *FALSE_TOKEN;
extern const char *TRUE_TOKEN;
extern const char *BOOL_TOKEN;

extern const char *UNSIGNED_TOKEN;
extern const char *SIGNED_TOKEN;
extern const char *CONST_TOKEN;
extern const char *INT_TOKEN;
extern const char *FXD_TOKEN;

extern const char *ARRAY_TOKEN;

extern const char *MAIN_TOKEN;

extern const char *DEFAULT_CTX_TOKEN;

/* ANSI colors TODO move into a separate namespace */
extern const char normal[];

extern const char black[];
extern const char red[];
extern const char green[];
extern const char yellow[];
extern const char blue[];
extern const char purple[];
extern const char cyan[];

extern const char light_gray[];
extern const char dark_gray[];
extern const char bold_red[];
extern const char bold_green[];
extern const char bold_yellow[];
extern const char bold_blue[];
extern const char bold_purple[];
extern const char bold_cyan[];
extern const char bold_light_gray[];
extern const char bold_dark_gray[];

extern volatile sig_atomic_t sigint_caught;

/* internal utils */
static inline unsigned pow2(unsigned exp)
{
    value_t res = 1;
    for (unsigned i = exp; i; -- i) {
        res *= 2;
    }
    return res;
}

static inline unsigned msb(unsigned value)
{
    unsigned res = 0;
    while (value >>= 1) {
        ++ res;
    }

    return res;
}
#endif
