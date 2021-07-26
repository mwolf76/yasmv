/**
 * @file time.hh
 * @brief Time definitions
 *
 * This header file contains common definitions used throughout the
 * whole program.
 *
 * Copyright (C) 2012-2021 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
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

#ifndef TIME_H
#define TIME_H

#include <cassert>
#include <cstdlib>
#include <csignal>
#include <cctype>

typedef unsigned step_t;

const step_t FIRST_STATE { 0 };
const step_t FINAL_STATE { UINT_MAX };

const step_t FROZEN { UINT_MAX >> 1 };

inline bool is_positive(step_t instant)
{ return instant < FROZEN; }

inline bool is_negative(step_t instant)
{ return instant > FROZEN; }

#endif /* TIME_H */
