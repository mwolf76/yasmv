/**
 * @file reach/typedefs.hh
 * @brief SAT-based BMC reachability analysis algorithm.
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
#ifndef REACHABILITY_ALGORITHM_TYPEDEFS_H
#define REACHABILITY_ALGORITHM_TYPEDEFS_H

namespace reach {

    typedef enum {
        REACHABILITY_REACHABLE,
        REACHABILITY_UNREACHABLE,
        REACHABILITY_UNKNOWN,
        REACHABILITY_ERROR,
    } reachability_status_t;

} // namespace reach

#endif /* REACHABILITY_ALGORITHM_TYPEDEFS_H */
