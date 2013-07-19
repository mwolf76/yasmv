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
#include <type_mgr.hh>

BooleanType::BooleanType(TypeMgr& owner)
    : Type(owner)
{
    f_repr = f_owner.em().make_boolean_type();
}

IntConstType::IntConstType(TypeMgr& owner)
    : Type(owner)
{
    f_repr = f_owner.em().make_int_const_type();
}

AlgebraicType::AlgebraicType(TypeMgr& owner, ADD *dds)
    : Type(owner)
    , f_dds(dds)
{}

SignedAlgebraicType::SignedAlgebraicType(TypeMgr& owner,
                                         unsigned width,
                                         ADD *dds)
    : AlgebraicType(owner, dds)
    , f_width(width)
{
    f_repr = f_owner.em().make_signed_int_type(width);
}

UnsignedAlgebraicType::UnsignedAlgebraicType(TypeMgr& owner,
                                             unsigned width,
                                             ADD *dds)
    : AlgebraicType(owner, dds)
    , f_width(width)
{
    f_repr = f_owner.em().make_unsigned_int_type(width);
}

ArrayType::ArrayType(TypeMgr& owner, Type_ptr of, unsigned size)
    : Type(owner)
    , f_of(of)
    , f_size(size)
{
    f_repr = f_owner.em().make_subscript( of->repr(),
                                          f_owner.em().make_iconst( size));
}

RangeType::RangeType(TypeMgr& owner, Type_ptr of)
    : Type(owner)
    , f_of(of)
{
    f_repr = f_owner.em().make_abstract_range_type ( of->repr() );
}

SetType::SetType(TypeMgr& owner, Type_ptr of)
    : Type(owner)
    , f_of(of)
{
    f_repr = f_owner.em().make_abstract_set_type( of->repr() );
}

EnumType::EnumType(TypeMgr& owner, ExprSet& literals)
    : Type(owner)
    , f_literals(literals)
{
    f_repr = f_owner.em().make_set_type(f_literals);
    ExprSet::iterator i;

    for (i = literals.begin(); i != literals.end(); ++ i) {
        Expr_ptr expr = *i;
        assert(ExprMgr::INSTANCE().is_identifier(expr)); // debug only
    }
}

// ostream helper, uses FQExpr printer (see expr/expr.cc)
ostream& operator<<(ostream& os, Type_ptr type)
{ return os << type->repr(); }
