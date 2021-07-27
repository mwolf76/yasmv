/**
 * @file type/exceptions.hh
 * @brief Type system module header file, exception classes.
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
                  const std::string& message="")
        : Exception("TypeException", subtype, message)
    {}
};

/** Raised when the inferrer detects a wrong type */
class BadType : public TypeException {
public:
    BadType(expr::Expr_ptr expr, Type_ptr lhs);
    BadType(expr::Expr_ptr expr, Type_ptr lhs, Type_ptr rhs);
};

class IdentifierExpected : public TypeException {
public:
    IdentifierExpected(expr::Expr_ptr expr);
};

/** Raised when the inferrer detects a wrong type */
class DuplicateLiteral : public TypeException {
public:
    DuplicateLiteral(expr::Expr_ptr expr);
};

/** Raised when the inferrer detects two mismatching types */

class TypeMismatch : public TypeException {
public:
    TypeMismatch(expr::Expr_ptr expr, Type_ptr a, Type_ptr b);
};

#endif /* TYPE_EXCEPTIONS_H */
