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
    virtual const char* what() const throw() =0;
};

/** Raised when the type checker detects a wrong type */
class BadType : public TypeException {
    Expr_ptr f_expr;
    Expr_ptr f_lhs;
    Expr_ptr f_rhs;

public:
    BadType(Expr_ptr expr, Type_ptr lhs);
    BadType(Expr_ptr expr, Type_ptr lhs, Type_ptr rhs);

    const char* what() const throw();
    ~BadType() throw();
};

/** Raised when the inferrer detects a wrong type */
class IdentifierExpected : public TypeException {
    Expr_ptr f_expr;

public:
    IdentifierExpected(Expr_ptr expr);

    const char* what() const throw();
    ~IdentifierExpected() throw();
};

/** Raised when the inferrer detects a wrong type */
class DuplicateLiteral : public TypeException {
    Expr_ptr f_expr;

public:
    DuplicateLiteral(Expr_ptr expr);

    const char* what() const throw();
    ~DuplicateLiteral() throw();
};

/** Raised when the inferrer detects two mismatching types */
class TypeMismatch : public TypeException {
    Expr_ptr f_expr;
    Expr_ptr f_repr_a;
    Expr_ptr f_repr_b;

public:
    TypeMismatch(Expr_ptr expr, Type_ptr a, Type_ptr b);

    const char* what() const throw();
    ~TypeMismatch() throw();
};

#endif /* TYPE_EXCEPTIONS_H */

