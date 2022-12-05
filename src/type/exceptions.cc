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

#include <type/classes.hh>
#include <type/exceptions.hh>
#include <type/typedefs.hh>

#include <sstream>
#include <string>

namespace type {

    static std::string format_bad_type(expr::Expr_ptr expr, Type_ptr lhs)
    {
        std::ostringstream oss;

        oss
            << "operand `"
            << expr
            << "` has invalid type `"
            << lhs->repr()
            << "` (@"
            << lhs /* raw pointer */
            << ")";

        return oss.str();
    }

    /** Raised when the inferrer detects a wrong type */
    static std::string format_bad_type(expr::Expr_ptr expr, Type_ptr lhs, Type_ptr rhs)
    {
        std::ostringstream oss;

        oss
            << "operands `"
            << expr->lhs() << "` and `"
            << expr->rhs() << "` have invalid types `"
            << lhs->repr() << "` (@"
            << lhs /* raw pointer */
            << ", `"
            << rhs->repr() << "` (@"
            << rhs << "`" /* raw pointer */
            ;

        return oss.str();
    }

    BadType::BadType(expr::Expr_ptr expr, Type_ptr lhs)
        : TypeException("BadType",
                        format_bad_type(expr, lhs))
    {}

    BadType::BadType(expr::Expr_ptr expr, Type_ptr lhs, Type_ptr rhs)
        : TypeException("BadType",
                        format_bad_type(expr, lhs, rhs))
    {}

    std::string format_identifier_expected(expr::Expr_ptr expr)
    {
        std::ostringstream oss;

        oss
            << "identifier expected while defining ENUM, got `"
            << expr
            << "` instead";

        return oss.str();
    }

    IdentifierExpected::IdentifierExpected(expr::Expr_ptr expr)
        : TypeException("IdentifierExpected",
                        format_identifier_expected(expr))
    {}

    std::string format_duplicate_literal(expr::Expr_ptr expr)
    {
        std::ostringstream oss;

        oss
            << "duplicate literal `"
            << expr
            << "` detected";

        return oss.str();
    }

    DuplicateLiteral::DuplicateLiteral(expr::Expr_ptr expr)
        : TypeException("DuplicateLiteral",
                        format_duplicate_literal(expr))
    {}

    /** Raised when the inferrer detects two mismatching types */
    std::string format_type_mismatch(expr::Expr_ptr expr, Type_ptr a, Type_ptr b)
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

    TypeMismatch::TypeMismatch(expr::Expr_ptr expr, Type_ptr a, Type_ptr b)
        : TypeException("TypeMismatch",
                        format_type_mismatch(expr, a, b))
    {}

    InternalError::InternalError(const std::string& message)
        : TypeException("InternalError", message)
    {}

} // namespace type
