/**
 * @file utils/time.hh
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

#ifndef UTILS_TIME_H
#define UTILS_TIME_H

#include <vector>

/** -- shortcurts to simplify the manipulation of the internal time stack -- */
#define TOP_TIME(step)               \
    assert(0 < f_time_stack.size()); \
    const step_t step                \
    {                                \
        f_time_stack.back()          \
    }

#define DROP_TIME() \
    f_time_stack.pop_back()

#define POP_TIME(step) \
    TOP_TIME(step);    \
    DROP_TIME()

#define PUSH_TIME(step) \
    f_time_stack.push_back(step)

namespace utils {

    typedef std::vector<step_t> TimeVector;

};

#endif /* UTILS_TIME_H */
