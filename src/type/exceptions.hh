/**
 * @file type/exceptions.hh
 * @brief Type system module header file, exception classes.
 *
 * This header file contains the declarations and type definitions
 * required by YASMINE type system classes.
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

#ifndef TYPE_EXCEPTIONS_H
#define TYPE_EXCEPTIONS_H

/** Exception classes */
class TypeException : public Exception {
public:
    TypeException(const std::string& subtype,
                  const std::string& message="(no message)")
        : Exception("TypeException", subtype, message)
    {}
};

/* helpers */
std::string build_bad_type_error_message(Expr_ptr expr, Type_ptr lhs);
std::string build_bad_type_error_message(Expr_ptr expr, Type_ptr lhs, Type_ptr rhs);
std::string build_identifier_expected_error_message(Expr_ptr expr);
std::string build_duplicate_literal_error_message(Expr_ptr expr);
std::string build_type_mismatch_error_message(Expr_ptr expr, Type_ptr a, Type_ptr b);

/** Raised when the inferrer detects a wrong type */
class BadType : public TypeException {
public:
    BadType(Expr_ptr expr, Type_ptr lhs)
        : TypeException("BadType",
                        build_bad_type_error_message(expr, lhs))
    {}

    BadType(Expr_ptr expr, Type_ptr lhs, Type_ptr rhs)
        : TypeException("BadType",
                        build_bad_type_error_message(expr, lhs, rhs))
    {}

};

class IdentifierExpected : public TypeException {
public:
    IdentifierExpected(Expr_ptr expr)
        : TypeException("IdentifierExpected",
                        build_identifier_expected_error_message(expr))
    {}
};

/** Raised when the inferrer detects a wrong type */
class DuplicateLiteral : public TypeException {
public:
    DuplicateLiteral(Expr_ptr expr)
        : TypeException("DuplicateLiteral",
                        build_duplicate_literal_error_message(expr))
    {}
};

/** Raised when the inferrer detects two mismatching types */

class TypeMismatch : public TypeException {
public:
    TypeMismatch(Expr_ptr expr, Type_ptr a, Type_ptr b)
        : TypeException("TypeMismatch",
                        build_type_mismatch_error_message(expr, a, b))
    {}
};

#endif /* TYPE_EXCEPTIONS_H */

