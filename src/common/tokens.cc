/*
 * @file common/tokens.cc
 * @brief System wide definitions.
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

#include <common/tokens.hh>

const char *EMPTY_TOKEN = "__nil__";

/* bool consts */
const char *FALSE_TOKEN = "FALSE";
const char *TRUE_TOKEN  = "TRUE";

/* types */
const char *TIME_TOKEN      = "time";
const char *BOOL_TOKEN      = "boolean";
const char *STRING_TOKEN    = "string";
const char *UNSIGNED_TOKEN  = "u";
const char *SIGNED_TOKEN    = "";
const char *CONST_TOKEN     = "const";
const char *INT_TOKEN       = "int";
const char *ARRAY_TOKEN     = "array";
