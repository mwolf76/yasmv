/**
 * @file symb/exceptions.cc
 * @brief Symbol interface, exception classes implementation.
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

#include <symb/exceptions.hh>

#include <cstring>
#include <sstream>

namespace symb {

    static std::string build_unresolved_symbol_error_message(expr::Expr_ptr expr)
    {
        std::ostringstream oss;

        oss
            << "Unresolved symbol: `"
            << expr
            << "`";

        return oss.str();
    }

    UnresolvedSymbol::UnresolvedSymbol(expr::Expr_ptr expr)
        : SymbolException("UnresolvedSymbol",
                          build_unresolved_symbol_error_message(expr))
    {}

}; // namespace symb
