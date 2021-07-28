/**
 * @file typedefs.hh
 * @brief Propositional logic compiler - module shared typedefs
 *
 * This header file contains the declarations required to implement
 * the compilation of propositional logic expressions.
 *
 * Copyright (C) 2011-2015 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2.1 of
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

#ifndef COMPILER_TYPEDEFS_H
#define COMPILER_TYPEDEFS_H

namespace model {

enum ETimePolarity {
    FORWARD, BACKWARD, NEUTRAL /* can work in both ways, in the compiler it's equivalent to FORWARD */
};

enum ECompilerStatus {
    READY,
    ENCODING,
    COMPILING,
    CHECKING,
    ACTIVATING_ITE_MUXES,
    ACTIVATING_ARRAY_MUXES
};

/* decl only */
ECompilerStatus& operator++(ECompilerStatus& status);

};

#endif /* COMPILER_TYPEDEFS_H */
