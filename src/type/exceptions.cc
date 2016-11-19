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

#include <sstream>
#include <cstring>

#include <type/type.hh>

#include <utils/misc.hh>

BadType::BadType(Expr_ptr expr, Type_ptr lhs)
    : f_expr(expr)
    , f_lhs(lhs -> repr())
    , f_rhs(NULL)
{}

BadType::BadType(Expr_ptr expr, Type_ptr lhs, Type_ptr rhs)
    : f_expr(expr)
    , f_lhs(lhs -> repr())
    , f_rhs(rhs -> repr())
{}

BadType::~BadType() throw()
{}

const char* BadType::what() const throw()
{
    std::ostringstream oss;

    if (! f_rhs)
        oss
            << "TypeError: operand `"
            << f_expr << "` has invalid type `"
            << f_lhs << "`";
    else
        oss
            << "TypeError: operands `"
            << f_expr -> lhs() << "` and `"
            << f_expr -> rhs() << "` have invalid types `"
            << f_lhs << "`, `" << f_rhs << "`";

    return oss2cstr(oss);
}

TypeMismatch::TypeMismatch(Expr_ptr expr, Type_ptr lhs, Type_ptr rhs)
    : f_expr(expr)
    , f_repr_a(lhs -> repr())
    , f_repr_b(rhs -> repr())
{}

TypeMismatch::~TypeMismatch() throw()
{}

const char* TypeMismatch::what() const throw()
{
    std::ostringstream oss;
    oss << "TypeError: `"
        << f_repr_a << "` and `"
        << f_repr_b << "` do not match in expression `"
        << f_expr   << "`"
        << std::endl;

    return oss2cstr(oss);
}

IdentifierExpected::IdentifierExpected(Expr_ptr expr)
    : f_expr(expr)
{}

IdentifierExpected::~IdentifierExpected() throw()
{}

const char* IdentifierExpected::what() const throw()
{
    std::ostringstream oss;
    oss
        << "TypeError: identifier expected while defining ENUM, got `"
        << f_expr << "` instead";

    return oss2cstr(oss);
}

DuplicateLiteral::DuplicateLiteral(Expr_ptr expr)
    : f_expr(expr)
{}

DuplicateLiteral::~DuplicateLiteral() throw()
{}

const char* DuplicateLiteral::what() const throw()
{
    std::ostringstream oss;
    oss
        << "TypeError: duplicate literal `"
        << f_expr << "` detected";

    return oss2cstr(oss);
}
