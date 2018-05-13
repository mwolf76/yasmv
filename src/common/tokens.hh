/**
 * @file tokens.hh
 * @brief System-wide definitions, reserved tokens.
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

#ifndef TOKENS_H
#define TOKENS_H

/* internal tokens, defined in common.cc */
extern const char *FALSE_TOKEN;
extern const char *TRUE_TOKEN;
extern const char *BOOL_TOKEN;
extern const char *STRING_TOKEN;

extern const char *UNSIGNED_TOKEN;
extern const char *SIGNED_TOKEN;
extern const char *CONST_TOKEN;
extern const char *INT_TOKEN;

extern const char *ARRAY_TOKEN;

extern const char* EMPTY_TOKEN;

#endif /* TOKENS*/
