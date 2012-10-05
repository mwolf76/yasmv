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

TemporalType::TemporalType(TypeMgr& owner)
    : Type(owner)
{
    f_repr = f_owner.em().make_temporal_type();
}

IntegerType::IntegerType(TypeMgr& owner) // abstract
    : Type(owner)
    // , f_abstract(true)
{
    f_repr = f_signed
        ? f_owner.em().make_signed_type(f_size)
        : f_owner.em().make_unsigned_type(f_size)
        ;
}

IntegerType::IntegerType(TypeMgr& owner, unsigned size, bool is_signed)
    : Type(owner)
    , f_size(size)
    , f_signed(is_signed)
{
    if (0 == f_size) {
        // special case for consts
        f_repr = f_owner.em().make_integer_type();
    }
    else {
        assert(0 < f_size);
        f_repr = f_signed
            ? f_owner.em().make_signed_type(f_size)
            : f_owner.em().make_unsigned_type(f_size)
            ;
    }
}


IntRangeType::IntRangeType(TypeMgr& owner, const Expr_ptr min, const Expr_ptr max)
    : Type(owner)
{
    ExprMgr& em = f_owner.em();

    ExprType min_symbtype  = min->f_symb;
    assert (ICONST == min_symbtype ||
            HCONST == min_symbtype ||
            OCONST == min_symbtype );
    f_min = min->value();

    ExprType max_symbtype  = max->f_symb;
    assert (ICONST == max_symbtype ||
            HCONST == max_symbtype ||
            OCONST == max_symbtype );
    f_max = max->value();

    f_repr = em.make_range_type(em.make_iconst(f_min),
                                em.make_iconst(f_max));
}

EnumType::EnumType(TypeMgr& owner, ExprSet literals)
    : Type(owner)
    , f_literals(literals)
{
    // TODO: kill cast
    f_repr = f_owner.em().make_enum_type(const_cast<ExprSet_ptr> (&f_literals));
}

Instance::Instance(TypeMgr& owner, Expr* identifier, ExprVector& params)
    : Type(owner)
    , f_identifier(identifier)
    , f_params(params)
{
}



bool EnumType::has_symbs() const
{
    bool res = false;
    ExprMgr& em = ExprMgr::INSTANCE();

    for (ExprSet::iterator eye = f_literals.begin();
         (!res) && (eye != f_literals.end()); eye ++) {

        res |= em.is_identifier(*eye);
    }

    return res;
}

bool EnumType::has_numbers() const
{
    bool res = false;
    ExprMgr& em = ExprMgr::INSTANCE();

    for (ExprSet::iterator eye = f_literals.begin();
         (!res) && (eye != f_literals.end()); eye ++) {

        res |= em.is_numeric(*eye);
    }

    return res;
}

// ostream helper
ostream& operator<<(ostream& os, Type_ptr type_ptr)
{ return os << type_ptr->get_repr(); }
