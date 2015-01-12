/**
 *  @file type_mgr.cc
 *  @brief Type system classes (TypeMgr)
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
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
 *
 *
 **/
#include <opts.hh>

#include <type.hh>
#include <type_mgr.hh>
#include <type_resolver.hh>

// static initialization
TypeMgr_ptr TypeMgr::f_instance = NULL;

TypeMgr::TypeMgr()
    : f_register()
    , f_em(ExprMgr::INSTANCE())
    , f_resolver(* new TypeResolver(* this))
{
}

const ScalarType_ptr TypeMgr::find_boolean()
{
    Expr_ptr descr(f_em.make_boolean_type());
    ScalarType_ptr res = dynamic_cast<ScalarType_ptr>(lookup_type(descr));
    if (res)
        return res;

    res = new BooleanType( *this);
    register_type(descr, res);

    return res;
}

const Type_ptr TypeMgr::find_type_by_def(const Expr_ptr expr)
{
    assert( f_em.is_type(expr));

    if (f_em.is_unsigned_int( expr->lhs()))
        return find_unsigned( expr->rhs()->value());

    else if (f_em.is_signed_int( expr->lhs()))
        return find_signed( expr->rhs()->value());

    else
        assert (false); /* unexpected */

    return NULL;
}

const ScalarType_ptr TypeMgr::find_int_const(unsigned bits)
{
    Expr_ptr descr(f_em.make_const_int_type(bits));
    ScalarType_ptr res = dynamic_cast<ScalarType_ptr> (lookup_type(descr));
    if (res)
        return res;

    // new type, needs to be registered before returning
    res = new ConstIntType( *this, bits);

    register_type(descr, res);
    return res;
}

const ScalarType_ptr TypeMgr::find_unsigned(unsigned bits)
{
    Expr_ptr descr(f_em.make_unsigned_int_type(bits));
    ScalarType_ptr res = dynamic_cast<ScalarType_ptr> (lookup_type(descr));
    if (res)
        return res;

    // new type, needs to be registered before returning
    res = new UnsignedAlgebraicType( *this, bits);

    register_type(descr, res);
    return res;
}

const ScalarType_ptr TypeMgr::find_unsigned(unsigned magnitude, unsigned fractional)
{
    Expr_ptr descr(f_em.make_unsigned_fxd_type(magnitude, fractional));
    ScalarType_ptr res = dynamic_cast<ScalarType_ptr> (lookup_type(descr));
    if (res)
        return res;

    // new type, needs to be registered before returning
    res = new UnsignedFxdAlgebraicType( *this, magnitude, fractional);

    register_type(descr, res);
    return res;
}


const ArrayType_ptr TypeMgr::find_unsigned_array(unsigned digits, unsigned size)
{
    Expr_ptr descr(f_em.make_subscript( f_em.make_unsigned_int_type(digits),
                                        f_em.make_const(size)));

    ArrayType_ptr res = dynamic_cast<ArrayType_ptr> (lookup_type(descr));
    if (res)
        return res;

    // new type, needs to be registered before returning
    res = new ArrayType( *this, find_unsigned(digits), size);

    register_type(descr, res);
    return res;
}

const ArrayType_ptr TypeMgr::find_unsigned_array(unsigned magnitude,
                                                 unsigned fractional,
                                                 unsigned size)
{
    Expr_ptr descr(f_em.make_subscript( f_em.make_unsigned_fxd_type(magnitude, fractional),
                                        f_em.make_const(size)));
    ArrayType_ptr res = dynamic_cast<ArrayType_ptr> (lookup_type(descr));
    if (res)
        return res;

    // new type, needs to be registered before returning
    res = new ArrayType( *this, find_unsigned(magnitude, fractional), size);

    register_type(descr, res);
    return res;
}


const ScalarType_ptr TypeMgr::find_signed(unsigned bits)
{
    Expr_ptr descr(f_em.make_signed_int_type(bits));
    ScalarType_ptr res = dynamic_cast<ScalarType_ptr> (lookup_type(descr));
    if (res)
        return res;

    // new type, needs to be registered before returning
    res = new SignedAlgebraicType(*this, bits);

    register_type(descr, res);
    return res;
}

const ScalarType_ptr TypeMgr::find_signed(unsigned magnitude, unsigned fractional)
{
    Expr_ptr descr(f_em.make_signed_fxd_type(magnitude, fractional));
    ScalarType_ptr res = dynamic_cast<ScalarType_ptr> (lookup_type(descr));
    if (res)
        return res;

    // new type, needs to be registered before returning
    res = new SignedFxdAlgebraicType(*this, magnitude, fractional);

    register_type(descr, res);
    return res;
}


const ArrayType_ptr TypeMgr::find_signed_array(unsigned digits, unsigned size)
{
    Expr_ptr descr(f_em.make_subscript( f_em.make_signed_int_type(digits),
                                        f_em.make_const(size)));
    ArrayType_ptr res = dynamic_cast<ArrayType_ptr> (lookup_type(descr));
    if (res)
        return res;

    // new type, needs to be registered before returning
    res = new ArrayType( *this, find_signed(digits), size);

    register_type(descr, res);
    return res;
}

const ArrayType_ptr TypeMgr::find_signed_array(unsigned magnitude,
                                               unsigned fractional,
                                               unsigned size)
{
    Expr_ptr descr(f_em.make_subscript( f_em.make_signed_fxd_type(magnitude, fractional),
                                        f_em.make_const(size)));
    ArrayType_ptr res = dynamic_cast<ArrayType_ptr> (lookup_type(descr));
    if (res)
        return res;

    // new type, needs to be registered before returning
    res = new ArrayType( *this, find_signed(magnitude, fractional), size);

    register_type(descr, res);
    return res;
}

const ScalarType_ptr TypeMgr::find_enum(ExprSet& lits)
{
    Expr_ptr repr (em().make_enum_type(lits));
    ScalarType_ptr res = dynamic_cast<ScalarType_ptr> (lookup_type( repr ));

    if (! res) {
        // new type, needs to be registered before returning
        res = new EnumType( *this, lits );
        register_type(repr, res);

        ExprSet::const_iterator i;
        for (i = lits.begin(); lits.end() != i; ++ i) {
            const Expr_ptr& expr(*i);
            Literal* literal = new Literal(expr, res);
            f_lits.insert(std::make_pair<Expr_ptr, Literal_ptr>
                          (expr, literal));
        }
    }
    return res;
}

/* unary variant */
Type_ptr TypeMgr::result_type(Expr_ptr expr, Type_ptr lhs)
{ return lhs; /* nop */ }

/* binary variant */
Type_ptr TypeMgr::result_type(Expr_ptr expr, Type_ptr lhs, Type_ptr rhs)
{
    ExprMgr& em = f_em;

    if (em.is_binary_arithmetical(expr))
        return arithmetical_result_type(lhs, rhs);

    else if (em.is_binary_logical(expr))
        return logical_result_type(lhs, rhs);

    else if (em.is_binary_relational(expr) ||
             em.is_binary_enumerative(expr))
        return relational_result_type(lhs, rhs);

    else if (em.is_cast(expr))
        return cast_result_type(lhs, rhs);

    else
        assert (false); /* unexpected */
}

/* ternary variant */
Type_ptr TypeMgr::result_type(Expr_ptr expr, Type_ptr cnd,
                              Type_ptr lhs, Type_ptr rhs)
{
    if (f_em.is_ite(expr) && cnd->is_boolean())
        return ite_result_type(lhs, rhs);

    return NULL;
}

Type_ptr TypeMgr::ite_result_type(Type_ptr lhs, Type_ptr rhs)
{
    if (lhs -> is_algebraic() &&
        rhs -> is_algebraic() &&
        lhs -> width() == rhs -> width())
        return lhs;

    return NULL;
}

Type_ptr TypeMgr::arithmetical_result_type(Type_ptr lhs, Type_ptr rhs)
{
    if (lhs -> is_algebraic() && rhs -> is_algebraic() &&
        lhs -> width() == rhs -> width())
        return rhs;

    return NULL;
}

Type_ptr TypeMgr::relational_result_type(Type_ptr lhs, Type_ptr rhs)
{
    if (lhs -> is_algebraic() && rhs -> is_algebraic() &&
        lhs -> width() == rhs -> width())
        return find_boolean();

    return NULL;
}

Type_ptr TypeMgr::logical_result_type(Type_ptr lhs, Type_ptr rhs)
{
    // both ops booleans -> boolean
    if (lhs -> is_boolean() && rhs -> is_boolean())
        return find_boolean();

    return NULL;
}

Type_ptr TypeMgr::cast_result_type(Type_ptr lhs, Type_ptr rhs)
{
    // same type, it's ok although useless
    if (lhs == rhs)
        return lhs;

    /* algebraic -> boolean? */
    if (lhs -> is_boolean() &&
        rhs -> is_algebraic())
        return lhs;

    /* boolean -> algebraic? */
    if (lhs -> is_algebraic() &&
        rhs -> is_boolean())
        return lhs;

    /* algebraic -> algebraic (of different signedness/width)? */
    if (lhs -> is_algebraic() &&
        rhs -> is_algebraic())
        return lhs;

    return NULL;
}

