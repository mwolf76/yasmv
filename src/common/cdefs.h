/*
 * @file cdefs.h
 * @brief System wide C definitions
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
#ifndef CDEFS_H
#define CDEFS_H

#include <limits.h>

/* Reserved for native data type, should match machine word for
   optimal performance. This type will be used for the ADD leaves. */
typedef long value_t;

/* Reserved for ADD ops error checking. */
static const value_t error_value = LONG_MIN;

/* Reserved for time frames representation. */
typedef unsigned step_t;

/* C string pointers */
typedef char* pchar;
typedef const char* pconst_char;

#endif /* CDEFS_H */
