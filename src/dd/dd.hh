/**
 * @file dd.hh
 * @brief Decision Diagram class
 *
 * This header file contains declarations required by the
 * implementation of a lightweight decision diagram class or DD. DDs
 * are used to store compilation result in a time-independent fashion,
 * in order to make it easy to instantiate timed expressions and
 * convert them to CNF.
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

#ifndef DECISION_DIAGRAMS_H
#define DECISION_DIAGRAMS_H

#include <climits>
#include <vector>

#include <common.hh>
#include <dd/cudd-2.5.0/obj/cuddObj.hh>

typedef std::vector<ADD> DDVector;

/* -- shortcuts to simplify the manipulation of the internal DD stack ------- */

/** Fetch a single DD */
#define POP_DD(op)                              \
    const ADD op (f_add_stack.back());          \
    f_add_stack.pop_back()

/** Declare a fresh DD */
#define FRESH_DD(var)                           \
    ADD var (make_auto_dd())

/** Push a single DD */
#define PUSH_DD(add)                            \
    f_add_stack.push_back(add)

/** Fetch a DD vector of given width */
#define POP_DV(vec, width)                      \
    DDVector vec;                               \
    for (unsigned i = 0; i < width ; ++ i) {    \
        vec.push_back(f_add_stack.back());      \
        f_add_stack.pop_back();                 \
    }

/** Declare a DD vector of given width */
#define FRESH_DV(vec, width)                    \
    DDVector vec;                               \
    make_auto_ddvect(vec, width);

/** Push a DD vector of given width */
#define PUSH_DV(vec, width)                     \
    /* push DD vector in reversed order */      \
    for (unsigned i = 0; i < width; ++ i)       \
        PUSH_DD(vec[width - i - 1]);

#endif /* DECISION_DIAGRAMS_H */
