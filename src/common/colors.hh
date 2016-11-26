/**
 * @file colors.hh
 * @brief System-wide definitions, reserved colors.
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

#ifndef COLORS_H
#define COLORS_H

/* ANSI colors */
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

// /* Witness trace formats */
// extern const char *TRACE_FMT_DEFAULT;
// extern const char *TRACE_FMT_PLAIN;
// extern const char *TRACE_FMT_JSON;
// extern const char *TRACE_FMT_XML;

#endif /* COLORS */
