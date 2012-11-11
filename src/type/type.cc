/**
 *  @file type.cc
 *  @brief Type system classes
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

#include <type.hh>

BooleanType::BooleanType(TypeMgr& owner)
    : Type(owner)
{
    f_repr = f_owner.em().make_boolean_type();
}

IntegerType::IntegerType(TypeMgr& owner) // abstract
    : Type(owner)
{
    f_repr = f_owner.em().make_integer_type();
}

AlgebraicType::AlgebraicType(TypeMgr& owner, unsigned width, bool is_signed, ADD *dds)
    : Type(owner)
    , f_width(width)
    , f_signed(is_signed)
    , f_dds(dds)
{
    f_repr = f_signed
        ? f_owner.em().make_signed_type(width)
        : f_owner.em().make_unsigned_type(width)
        ;
}

EnumType::EnumType(TypeMgr& owner, ExprSet& literals)
    : Type(owner)
    , f_literals(literals)
{
    f_repr = f_owner.em().make_enum_type(f_literals);
    ExprSet::iterator i;

    for (i = literals.begin(); i != literals.end(); ++ i) {
        Expr_ptr expr = *i;
        assert(ExprMgr::INSTANCE().is_identifier(expr)); // debug only
    }
}

Instance::Instance(TypeMgr& owner, Expr_ptr identifier)
    : Type(owner)
    , f_identifier(identifier)
{
    // use empty params node to distinguish type from identifier
    // (i.e. it's foo() instead of foo).
    f_repr = f_owner.em().make_params(identifier, NULL);
}

// ostream helper, uses FQExpr printer (see expr/expr.cc)
ostream& operator<<(ostream& os, Type_ptr type)
{ return os << type->repr(); }
