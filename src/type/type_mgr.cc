/**
 *  @file type_mgr.cc
 *  @brief Type system classes (TypeMgr)
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

// static initialization
TypeMgr_ptr TypeMgr::f_instance = NULL;

TypeMgr::TypeMgr()
    : f_register()
    , f_map()
    , f_em(ExprMgr::INSTANCE())
{
    // register predefined types
    register_type( FQExpr( f_em.make_boolean_type() ),
                   new BooleanType(*this));

    register_type( FQExpr( f_em.make_integer_type() ),
                   new IntegerType(*this));
}

const Type_ptr TypeMgr::find_unsigned(unsigned bits)
{
    FQExpr descr(f_em.make_unsigned_type(bits));
    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new FiniteIntegerType(*this, bits, false);
    register_type(descr, res);
    return res;
}

const Type_ptr TypeMgr::find_signed(unsigned bits)
{
    FQExpr descr(f_em.make_signed_type(bits));
    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new FiniteIntegerType(*this, bits, true);  // signed
    register_type(descr, res);
    return res;
}

const Type_ptr TypeMgr::find_range(const Expr_ptr from, const Expr_ptr to)
{
    FQExpr descr(f_em.make_range_type(from, to));
    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new IntRangeType(*this, from, to);
    register_type(descr, res);
    return res;
}

const Type_ptr TypeMgr::find_enum(Expr_ptr ctx, ExprSet& lits)
{
    /* IMPORTANT: lits ordering has to be canonical for enum types to
       work as expected! Otherwise same set of lits with different
       ordering could be mistakingly seen as a different type. */
    FQExpr descr(f_em.make_enum_type(lits));
    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new EnumType(*this, lits);
    register_type(descr, res);
    return res;
}

const Type_ptr TypeMgr::find_instance(Expr_ptr identifier)
{
    assert(0);
    return NULL;
}

    // {
    //   Type_ptr inst = new Instance(identifier);
    //   TypeHit hit = f_register.insert( make_pair( FQExpr(identifier), inst));

    //   if (hit.second) {
    //     logger << "Added instance of module '"
    //            << identifier
    //            << "' to type register"
    //            << endl;
    //   }

    //   TypeMap::p = &(*hit.first);
    //   return p->second;
    // }

bool TypeMgr::is_boolean(const Type_ptr tp) const
{
    return NULL != dynamic_cast <const BooleanType_ptr> (tp);
}

BooleanType_ptr TypeMgr::as_boolean(const Type_ptr tp) const
{
    BooleanType_ptr res = dynamic_cast <const BooleanType_ptr> (tp);
    assert(res);

    return res;
}

bool TypeMgr::is_integer(const Type_ptr tp) const
{
    return is_int_range(tp) || is_int_enum(tp)  ||
        (NULL != dynamic_cast<const IntegerType_ptr>(tp));
}

IntegerType_ptr TypeMgr::as_integer(const Type_ptr tp) const
{
    IntegerType_ptr res = dynamic_cast<const IntegerType_ptr>(tp);
    assert(res);

    return res;
}

bool TypeMgr::is_int_range(const Type_ptr tp) const
{
    return NULL != dynamic_cast <const IntRangeType_ptr> (tp);
}

IntRangeType_ptr TypeMgr::as_int_range(const Type_ptr tp) const
{
    IntRangeType_ptr res = dynamic_cast <IntRangeType_ptr> (tp);
    assert(res);

    return res;
}

bool TypeMgr::is_enum(const Type_ptr tp) const
{
    return NULL != dynamic_cast <const EnumType_ptr> (tp);
}

bool TypeMgr::is_int_enum(const Type_ptr tp) const
{
    EnumType_ptr tmp;
    return (! (tmp = dynamic_cast <const EnumType_ptr> (tp)))
        ? false
        : ! tmp->has_symbs();
}

EnumType_ptr TypeMgr::as_enum(const Type_ptr tp) const
{
    EnumType_ptr res = dynamic_cast<EnumType_ptr> (tp);
    assert(res);

    return res;
}

bool TypeMgr::is_int_finite(const Type_ptr tp) const
{
    return (NULL != dynamic_cast <FiniteIntegerType*> (tp));
}

FiniteIntegerType_ptr TypeMgr::as_int_finite(const Type_ptr tp) const
{
    FiniteIntegerType_ptr res = dynamic_cast <const FiniteIntegerType_ptr> (tp);
    assert(res);

    return res;
}

bool TypeMgr::is_instance(const Type_ptr tp) const
{
    return (NULL != dynamic_cast <Instance_ptr> (tp));
}

Instance_ptr TypeMgr::as_instance(const Type_ptr tp) const
{
    Instance_ptr res = dynamic_cast <Instance_ptr> (tp);
    assert(res);

    return res;
}

void TypeMgr::register_type(const FQExpr fqexpr, Type_ptr vtype)
{
    assert ((NULL != vtype) && (! lookup_type(fqexpr)));
    DEBUG << "Registering new type: " << fqexpr << endl;

    f_register [ fqexpr ] = vtype;
}
