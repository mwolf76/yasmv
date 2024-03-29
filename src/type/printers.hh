/**
 * @file type/printers.hh
 * @brief Type system module, printer helpers.
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

#ifndef TYPE_PRINTERS_H
#define TYPE_PRINTERS_H

#include <common/common.hh>

namespace type {

    // ostream helper, uses FQExpr printer (see expr/expr.cc)
    std::ostream& operator<<(std::ostream& os, Type_ptr type);

    // std::ostream helper, uses FQExpr printer (see expr/expr.cc)
    std::ostream& operator<<(std::ostream& os, const Type_ptr type);

}; // namespace type

#endif /* TYPE_PRINTERS_H */
