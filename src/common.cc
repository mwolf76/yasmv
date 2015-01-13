/*
 * @file common.cc
 * @brief System wide definitions
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

#include <common.hh>

/* environment variables and paths */
const char *YASMV_HOME = "YASMV_HOME";
const char *MICROCODE_PATH = "microcode";

/* tokens */
const char *MAIN_TOKEN = "main";

const char *EMPTY_TOKEN = "__empty";

const char *DEFAULT_CTX_TOKEN = "__main";

/* bool consts */
const char *FALSE_TOKEN = "FALSE";
const char *TRUE_TOKEN = "TRUE";

/* types */
const char *BOOL_TOKEN      = "boolean";
const char *UNSIGNED_TOKEN  = "unsigned";
const char *SIGNED_TOKEN    = "signed";
const char *CONST_TOKEN     = "const";
const char *INT_TOKEN       = "int";
const char *FXD_TOKEN       = "fxd";
const char *ARRAY_TOKEN     = "array";

/* color support for *nix systems */
const char ESC  = 0x1b;
const char normal[] = { ESC, '[', '0', ';', '3', '9', 'm', 0 };

const char black[] = { ESC, '[', '0', ';', '3', '0', 'm', 0 };
const char red[] = { ESC, '[', '0', ';', '3', '1', 'm', 0 };
const char green[] = { ESC, '[', '0', ';', '3', '2', 'm', 0 };
const char yellow[] = { ESC, '[', '0', ';', '3', '3', 'm', 0 };
const char blue[] = { ESC, '[', '0', ';', '3', '4', 'm', 0 };
const char purple[] = { ESC, '[', '0', ';', '3', '5', 'm', 0 };
const char cyan[] = { ESC, '[', '0', ';', '3', '6', 'm', 0 };
const char light_gray[] = { ESC, '[', '0', ';', '3', '7', 'm', 0 };
const char dark_gray[] = { ESC, '[', '0', ';', '3', '8', 'm', 0 };

const char bold_red[] = { ESC, '[', '1', ';', '3', '1', 'm', 0 };
const char bold_green[] = { ESC, '[', '1', ';', '3', '2', 'm', 0 };
const char bold_yellow[] = { ESC, '[', '1', ';', '3', '3', 'm', 0 };
const char bold_blue[] = { ESC, '[', '1', ';', '3', '4', 'm', 0 };
const char bold_purple[] = { ESC, '[', '1', ';', '3', '5', 'm', 0 };
const char bold_cyan[] = { ESC, '[', '1', ';', '3', '6', 'm', 0 };
const char bold_light_gray[] = { ESC, '[', '1', ';', '3', '7', 'm', 0 };
const char bold_dark_gray[] = { ESC, '[', '1', ';', '3', '8', 'm', 0 };

volatile sig_atomic_t sigint_caught = 0;
