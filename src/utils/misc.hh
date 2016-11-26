/**
 * @file misc.hh
 * @brief Generic utils module head file
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#ifndef MISC_H
#define MISC_H

#include <sstream>

static inline const char* oss2cstr(std::ostringstream& oss)
{ return strdup(oss.str().c_str()); }

static inline bool _iff(bool a, bool b)
{ return (!(a) || (b)) && ((!b) || (a)); }

static inline bool _xor(bool a, bool b)
{ return (!(a) && (b)) || ((!b) && (a)); }


#endif /* MISC_H */
