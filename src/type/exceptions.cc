/**
 * @file exceptions.cc
 * @brief Type system's exception classes implementation
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
< *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#include <expr/expr.hh>
#include <type/type.hh>

#include <string>
#include <sstream>

std::string build_bad_type_error_message(Expr_ptr expr, Type_ptr lhs)
{
    std::ostringstream oss;

    oss
        << "operand `"
        << expr << "` has invalid type `"
        << lhs << "`";

    return oss.str();
}

std::string build_bad_type_error_message(Expr_ptr expr, Type_ptr lhs, Type_ptr rhs)
{
    std::ostringstream oss;

    oss
        << "operands `"
        << expr->lhs() << "` and `"
        << expr->rhs() << "` have invalid types `"
        << lhs << "`, `"
        << rhs << "`";

    return oss.str();
}

std::string build_identifier_expected_error_message(Expr_ptr expr)
{
    std::ostringstream oss;

    oss
        << "identifier expected while defining ENUM, got `"
        << expr
        << "` instead";

    return oss.str();
}

std::string build_duplicate_literal_error_message(Expr_ptr expr)
{
    std::ostringstream oss;

    oss
        << "duplicate literal `"
        << expr
        << "` detected";

    return oss.str();
}

std::string build_type_mismatch_error_message(Expr_ptr expr, Type_ptr a, Type_ptr b)
{
    std::ostringstream oss;

    oss
        << "`"
        << a
        << "` and `"
        << b
        << "` do not match in expression `"
        << expr
        << "`"
        << std::endl;

    return oss.str();
}
