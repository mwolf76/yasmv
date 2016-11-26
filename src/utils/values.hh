/**
 * @file utils/values.hh
 * @brief System-wide definitions.
 *
 * This header file contains common definitions used throughout the
 * whole program.
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

#ifndef UTILS_VALUES_H
#define UTILS_VALUES_H

#include <vector>
typedef std::vector<value_t> ValueVector;

/* shortcuts to to simplify manipulation of the internal values stack */
#define POP_VALUE(op)                              \
    assert(0 < f_values_stack.size());             \
    const value_t op = f_values_stack.back();      \
    f_values_stack.pop_back()

#define PUSH_VALUE(op)                             \
    f_values_stack.push_back(op)

#define DROP_VALUE()                               \
    f_values_stack.pop_back()

#define TOP_VALUE()                                \
    f_values_stack.back()

#endif /* UTILS_VALUES_H */
