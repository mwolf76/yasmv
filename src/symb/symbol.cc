/**
 *  @file symbol.cc
 *  @brief Symbol classes
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

#include <symbol.hh>
#include <model.hh>

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


bool ISymbol::is_variable(void) const
{
    return NULL != dynamic_cast <const IVariable_ptr>
        (const_cast <const ISymbol_ptr> (this));
}

IVariable& ISymbol::as_variable(void) const
{
    IVariable_ptr res = dynamic_cast <const IVariable_ptr>
        (const_cast <const ISymbol_ptr> (this));
    assert (res);
    return (*res);
}

bool ISymbol::is_temporary(void) const
{
    return NULL != dynamic_cast <const ITemporary_ptr>
        (const_cast <const ISymbol_ptr> (this));
}

ITemporary& ISymbol::as_temporary(void) const
{
    ITemporary_ptr res = dynamic_cast <const ITemporary_ptr>
        (const_cast <const ISymbol_ptr> (this));
    assert (res);
    return (*res);
}

bool ISymbol::is_define(void) const
{
    return NULL != dynamic_cast <const IDefine_ptr>
        (const_cast <const ISymbol_ptr> (this));
}

IDefine& ISymbol::as_define(void) const
{
    IDefine_ptr res = dynamic_cast <const IDefine_ptr>
        (const_cast <const ISymbol_ptr> (this));
    assert (res);
    return (*res);
}

bool ISymbol::is_const() const
{
    return NULL != dynamic_cast <const IConstant_ptr>
        (const_cast <const ISymbol_ptr> (this));
}

IConstant& ISymbol::as_const(void) const
{
    IConstant_ptr res = dynamic_cast <const IConstant_ptr>
        (const_cast <const ISymbol_ptr> (this));
    assert (res);
    return (*res);
}

bool ISymbol::is_literal() const
{
    return NULL != dynamic_cast <const ILiteral_ptr>
        (const_cast <const ISymbol_ptr> (this));
}

ILiteral& ISymbol::as_literal(void) const
{
    ILiteral_ptr res = dynamic_cast <const ILiteral_ptr>
        (const_cast <const ISymbol_ptr> (this));
    assert (res);
    return (*res);
}

bool ISymbol::is_enum() const
{
    return NULL != dynamic_cast <const IEnum_ptr>
        (const_cast <const ISymbol_ptr> (this));
}

IEnum& ISymbol::as_enum() const
{
    IEnum_ptr res = dynamic_cast <const IEnum_ptr>
        (const_cast <const ISymbol_ptr> (this));
    assert (res);
    return (*res);
}

