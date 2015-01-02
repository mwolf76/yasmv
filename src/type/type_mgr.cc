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
    /* register predefined types */
    register_type( f_em.make_boolean_type(),
                   new BooleanType(*this));

    register_type( f_em.make_constant_type(),
                   new ConstantType(*this));

    // (un)signed integers { 4, 8, 16, 32, 64 } bits wide
    for (int i = 2; i <= 16; i *= 2) {
        register_type( f_em.make_unsigned_int_type(i),
                       new UnsignedAlgebraicType(*this, i, NULL));

        register_type( f_em.make_signed_int_type(i),
                       new SignedAlgebraicType(*this, i, NULL));
    }
}

const Type_ptr TypeMgr::find_type_by_def(const Expr_ptr expr)
{
    mutex::scoped_lock lock(f_register_mutex);
    assert( f_em.is_type(expr));

    if (f_em.is_unsigned_int( expr->lhs())) {
        return find_unsigned( expr->rhs()->value());
    }
    else if (f_em.is_signed_int( expr->lhs())) {
        return find_signed( expr->rhs()->value());
    }
    else assert (false); /* unexpected */
    return NULL;
}

const ScalarType_ptr TypeMgr::find_unsigned(unsigned bits)
{
    mutex::scoped_lock lock(f_register_mutex);

    Expr_ptr descr(f_em.make_unsigned_int_type(bits));
    ScalarType_ptr res = dynamic_cast<ScalarType_ptr> (lookup_type(descr));
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new UnsignedAlgebraicType( *this, bits);
    register_type(descr, res);
    return res;
}

const ScalarType_ptr TypeMgr::find_unsigned(unsigned magnitude, unsigned fractional)
{
    mutex::scoped_lock lock(f_register_mutex);

    Expr_ptr descr(f_em.make_unsigned_fxd_type(magnitude, fractional));
    ScalarType_ptr res = dynamic_cast<ScalarType_ptr> (lookup_type(descr));
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new UnsignedFxdAlgebraicType( *this, magnitude, fractional);
    register_type(descr, res);
    return res;
}


const ArrayType_ptr TypeMgr::find_unsigned_array(unsigned digits, unsigned size)
{
    mutex::scoped_lock lock(f_register_mutex);

    Expr_ptr descr(f_em.make_subscript( f_em.make_unsigned_int_type(digits),
                                        f_em.make_const(size)));

    ArrayType_ptr res = dynamic_cast<ArrayType_ptr> (lookup_type(descr));
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new ArrayType( *this,
                         find_unsigned(digits), size);
    register_type(descr, res);
    return res;
}

const ArrayType_ptr TypeMgr::find_unsigned_array(unsigned magnitude,
                                                 unsigned fractional,
                                                 unsigned size)
{
    mutex::scoped_lock lock(f_register_mutex);

    Expr_ptr descr(f_em.make_subscript( f_em.make_unsigned_fxd_type(magnitude, fractional),
                                        f_em.make_const(size)));
    ArrayType_ptr res = dynamic_cast<ArrayType_ptr> (lookup_type(descr));
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new ArrayType( *this,
                         find_unsigned(magnitude, fractional), size);
    register_type(descr, res);
    return res;
}


const ScalarType_ptr TypeMgr::find_signed(unsigned bits)
{
    mutex::scoped_lock lock(f_register_mutex);

    Expr_ptr descr(f_em.make_signed_int_type(bits));
    ScalarType_ptr res = dynamic_cast<ScalarType_ptr> (lookup_type(descr));
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new SignedAlgebraicType(*this, bits);
    register_type(descr, res);
    return res;
}

const ScalarType_ptr TypeMgr::find_signed(unsigned magnitude, unsigned fractional)
{
    mutex::scoped_lock lock(f_register_mutex);

    Expr_ptr descr(f_em.make_signed_fxd_type(magnitude, fractional));
    ScalarType_ptr res = dynamic_cast<ScalarType_ptr> (lookup_type(descr));
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new SignedFxdAlgebraicType(*this, magnitude, fractional);
    register_type(descr, res);
    return res;
}


const ArrayType_ptr TypeMgr::find_signed_array(unsigned digits, unsigned size)
{
    mutex::scoped_lock lock(f_register_mutex);

    Expr_ptr descr(f_em.make_subscript( f_em.make_signed_int_type(digits),
                                        f_em.make_const(size)));
    ArrayType_ptr res = dynamic_cast<ArrayType_ptr> (lookup_type(descr));
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new ArrayType( *this,
                         find_signed(digits), size);
    register_type(descr, res);
    return res;
}

const ArrayType_ptr TypeMgr::find_signed_array(unsigned magnitude,
                                               unsigned fractional,
                                               unsigned size)
{
    mutex::scoped_lock lock(f_register_mutex);

    Expr_ptr descr(f_em.make_subscript( f_em.make_signed_fxd_type(magnitude, fractional),
                                        f_em.make_const(size)));
    ArrayType_ptr res = dynamic_cast<ArrayType_ptr> (lookup_type(descr));
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new ArrayType( *this,
                         find_signed(magnitude, fractional), size);
    register_type(descr, res);
    return res;
}

const ArrayType_ptr TypeMgr::find_array_type( ScalarType_ptr of )
{
    mutex::scoped_lock lock(f_register_mutex);

    Expr_ptr descr(f_em.make_abstract_array_type( of->repr() ));

    ArrayType_ptr res = dynamic_cast<ArrayType_ptr> (lookup_type(descr));
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new ArrayType( *this, of );

    register_type(descr, res);
    return res;
}

void TypeMgr::register_enum(Expr_ptr ctx, Expr_ptr name, ExprSet& lits)
{
    mutex::scoped_lock lock(f_register_mutex);

    /*
       IMPORTANT: lits ordering has to be canonical for enum types to
       work as expected! Otherwise same set of lits with different
       ordering could be mistakingly seen as a different type.
    */
    Expr_ptr fullname = ExprMgr::INSTANCE().make_dot( ctx, name );

    if (NULL != lookup_type(fullname)) {
        assert(0); // TODO: better error handling
    }

    EnumType_ptr tp = new EnumType( *this, lits );

    // Define the ENUM
    IEnum_ptr enm = new Enum(ctx, name, tp);
    f_enums.insert( make_pair<FQExpr,
                    IEnum_ptr>( FQExpr( ctx, name), enm));

    // Literals are all maintained together by the type mgr. This
    // greatly simplifies the resolver.
    for (ExprSet::iterator eye = lits.begin(); eye != lits.end(); ++ eye) {
        Expr_ptr lit = *eye;

        f_lits.insert( make_pair<FQExpr,
                                 ILiteral_ptr>(FQExpr( ctx, lit),
                                               new Literal(enm, lit)));
    }

    // new type, needs to be registered before returning
    register_type(fullname, tp);
}

const ScalarType_ptr TypeMgr::find_enum(Expr_ptr ctx, Expr_ptr name)
{
    mutex::scoped_lock lock(f_register_mutex);

    ScalarType_ptr res =
        dynamic_cast<ScalarType_ptr> (lookup_type(ExprMgr::INSTANCE().make_dot(ctx, name)));

    assert( NULL != res ); // TODO error handling

    return res;
}

/* unary variant */
Type_ptr TypeMgr::result_type(Expr_ptr expr, Type_ptr lhs)
{ return lhs; /* nop */ }

/* binary variant */
Type_ptr TypeMgr::result_type(Expr_ptr expr, Type_ptr lhs, Type_ptr rhs)
{
    ExprMgr& em = f_em;

    if (em.is_binary_arithmetical(expr)) {
        return arithmetical_result_type(lhs, rhs);
    }
    else if (em.is_binary_logical(expr)) {
        return logical_result_type(lhs, rhs);
    }
    else if (em.is_binary_relational(expr) ||
             em.is_binary_enumerative(expr)){
        return find_boolean();
    }
    else if (em.is_cast(expr)) {
        return cast_result_type(lhs, rhs);
    }
    else {
        assert (false); /* unexpected */
    }
}

/* ternary variant */
Type_ptr TypeMgr::result_type(Expr_ptr expr, Type_ptr cnd,
                              Type_ptr lhs, Type_ptr rhs)
{
    ExprMgr& em = f_em;

    assert(cnd->is_boolean());
    if (em.is_ite(expr)) {
        return ite_result_type(lhs, rhs);
    }
    else assert (false); // unexpected
}

Type_ptr TypeMgr::arithmetical_result_type(Type_ptr lhs, Type_ptr rhs)
{
    if (lhs -> is_algebraic() &&
        rhs -> is_algebraic()) {

        // both ops int const -> int const
        if (lhs->is_constant() &&
            rhs->is_constant()) {
            return lhs;
        }
        assert( !lhs -> is_constant() ||
                !rhs -> is_constant() );

        if (lhs -> is_constant()) {
            return rhs;
        }
        else if (rhs -> is_constant()) {
            return lhs;
        }
        else if (lhs == rhs) {
            return lhs;
        }
    }

    return NULL;
}

Type_ptr TypeMgr::logical_result_type(Type_ptr lhs, Type_ptr rhs)
{
    // both ops booleans -> boolean
    if (lhs -> is_boolean() &&
        rhs -> is_boolean()) {
        return find_boolean();
    }

    return arithmetical_result_type(lhs, rhs);
}

Type_ptr TypeMgr::cast_result_type(Type_ptr lhs, Type_ptr rhs)
{
    // same type, it's ok although useless
    if (lhs == rhs) return lhs;

    /* algebraic -> boolean? */
    if (lhs -> is_boolean() &&
        rhs -> is_algebraic()) {
        return lhs;
    }

    /* boolean -> algebraic? */
    if (lhs -> is_algebraic() &&
        rhs -> is_boolean()) {
        return lhs;
    }

    /* algebraic -> algebraic (of different signedness/width)? */
    if (lhs -> is_algebraic() &&
        rhs -> is_algebraic()) {
        return lhs;
    }

    return NULL;
}


Type_ptr TypeMgr::ite_result_type(Type_ptr lhs, Type_ptr rhs)
{
    // both booleans -> boolean
    if (lhs -> is_boolean() &&
        rhs -> is_boolean())
        return rhs;

    // both (same) enums -> enum
    if (lhs -> is_enum() &&
        rhs -> is_enum() &&
        (lhs == rhs))
        return rhs;

    return arithmetical_result_type(lhs, rhs);
}

