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
#include <sstream>
#include <cstring>

#include <symb/symbol.hh>

UnresolvedSymbol::UnresolvedSymbol(Expr_ptr expr)
    : f_expr(expr)
{}

const char* UnresolvedSymbol::what() const throw()
{
    std::ostringstream oss;
    oss
        << "Unresolved symbol: `"
        << f_expr<< "`";

    return strdup(oss.str().c_str());
}

bool Symbol::is_variable(void) const
{
    return NULL != dynamic_cast <const Variable_ptr>
        (const_cast <const Symbol_ptr> (this));
}

Variable& Symbol::as_variable(void) const
{
    Variable_ptr res = dynamic_cast <const Variable_ptr>
        (const_cast <const Symbol_ptr> (this));
    assert (res);
    return (*res);
}

bool Symbol::is_parameter(void) const
{
    return NULL != dynamic_cast <const Parameter_ptr>
        (const_cast <const Symbol_ptr> (this));
}

Parameter& Symbol::as_parameter(void) const
{
    Parameter_ptr res = dynamic_cast <const Parameter_ptr>
        (const_cast <const Symbol_ptr> (this));
    assert (res);
    return (*res);
}

bool Symbol::is_define(void) const
{
    return NULL != dynamic_cast <const Define_ptr>
        (const_cast <const Symbol_ptr> (this));
}

Define& Symbol::as_define(void) const
{
    Define_ptr res = dynamic_cast <const Define_ptr>
        (const_cast <const Symbol_ptr> (this));
    assert (res);
    return (*res);
}

bool Symbol::is_const() const
{
    return NULL != dynamic_cast <const Constant_ptr>
        (const_cast <const Symbol_ptr> (this));
}

Constant& Symbol::as_const(void) const
{
    Constant_ptr res = dynamic_cast <const Constant_ptr>
        (const_cast <const Symbol_ptr> (this));
    assert (res);
    return (*res);
}

bool Symbol::is_literal() const
{
    return NULL != dynamic_cast <const Literal_ptr>
        (const_cast <const Symbol_ptr> (this));
}

Literal& Symbol::as_literal(void) const
{
    Literal_ptr res = dynamic_cast <const Literal_ptr>
        (const_cast <const Symbol_ptr> (this));
    assert (res);
    return (*res);
}

bool Symbol::is_hidden() const
{ return f_hidden; }

void Symbol::set_hidden(bool value)
{ f_hidden = value; }
