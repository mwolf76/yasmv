/**
 *  @file type_exceptions.cc
 *  @brief Type system classes (Exception classes)
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

#include <type_exceptions.hh>
BadContext::BadContext(Expr_ptr ctx)
    : f_ctx(ctx)
{}

const char* BadContext::what() const throw()
{
    ostringstream oss;

    oss << "Bad Context: " << f_ctx;
    return oss.str().c_str();
}

BadParams::BadParams(Expr_ptr module, int params_num, int actual_num)
    : f_moduleName(module)
    , f_modl_params_num(params_num)
    , f_inst_params_num(actual_num)
{}

const char* BadParams::what() const throw()
{
    ostringstream oss;

    oss << "BadParams: " << f_moduleName
        << " expected " << f_modl_params_num
        << " got " << f_inst_params_num;
    return oss.str().c_str();
}

UnresolvedSymbol::UnresolvedSymbol(Expr_ptr ctx, Expr_ptr expr)
    : f_ctx(ctx)
    , f_expr(expr)
{}

const char* UnresolvedSymbol::what() const throw()
{
    ostringstream oss;

    oss << "Unresolved symbol: " << f_ctx << "::" << f_expr;
    return oss.str().c_str();
}

// exactly one type allowed
BadType::BadType(Expr_ptr got, Expr_ptr allowed, Expr_ptr body)
    : f_got(got)
    , f_allowed()
    , f_body(body)
{
    f_allowed.push_back(allowed);
}

// multiple types allowed shortcut
BadType::BadType(Expr_ptr got, ExprVector allowed, Expr_ptr body)
    : f_got(got)
    , f_allowed(allowed)
    , f_body(body)
{}

BadType::~BadType() throw()
{}

const char* BadType::what() const throw()
{
    ostringstream oss;

    oss << "BadType: operand has type " << f_got
        << " in " << f_body;

    oss << ", allowed: ";
    ExprVector::const_iterator eye = f_allowed.begin();
    do {
        oss << (*eye); eye ++;
        if (eye != f_allowed.end()) oss << ", ";
    } while (eye != f_allowed.end());
    oss << ".";

    return oss.str().c_str();
}

ResolutionException::ResolutionException(Expr_ptr expr)
    : f_expr(expr)
{}

const char* ResolutionException::what() const throw()
{
    ostringstream oss;

    oss << "UnresolvedSymbol: " << f_expr;
    return oss.str().c_str();
}
