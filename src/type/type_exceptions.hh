/**
 *  @file model_analyzer_exceptions.hh
 *  @brief Model Analyzer system classes (Exception classes)
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
 *
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2.1 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/

#ifndef MODEL_ANALYZER_EXCEPTIONS_H
#define MODEL_ANALYZER_EXCEPTIONS_H

#include <type.hh>

// -- analyzer related exception hierarchy
class AnalyzerException : public Exception {
public:
    virtual const char* what() const throw() =0;
};

class BadContext : public AnalyzerException {
public:
    BadContext(Expr_ptr ctx);
    const char* what() const throw();

private:
    Expr_ptr f_ctx;
};

class BadParams : public AnalyzerException {
public:
    BadParams(Expr_ptr module, int params_num, int actual_num);
    const char* what() const throw();

private:
    Expr_ptr f_moduleName;
    int f_modl_params_num;
    int f_inst_params_num;
};

class UnresolvedSymbol : public AnalyzerException {
    Expr_ptr f_ctx;
    Expr_ptr f_expr;

public:
    UnresolvedSymbol(Expr_ptr ctx, Expr_ptr expr);
    const char* what() const throw();
};

/** Raised when a the inferrer detects a wrong type */
class BadType : public AnalyzerException {
    Expr_ptr f_repr;
    TypeList f_allowed;

public:
    BadType(Expr_ptr type, TypeList &allowed);

    const char* what() const throw();
    ~BadType() throw();
};

/** Raised when the inferrer detects two types which do not properly match as expected */
class TypeMismatch : public AnalyzerException {
    Expr_ptr f_repr_a;
    Expr_ptr f_repr_b;

public:
    TypeMismatch(Expr_ptr repr_a, Expr_ptr repr_b);

    const char* what() const throw();
    ~TypeMismatch() throw();
};

class ResolutionException
    : public AnalyzerException {

public:
    ResolutionException(Expr_ptr expr);
    const char* what() const throw();

private:
    Expr_ptr f_expr;
};

#endif
