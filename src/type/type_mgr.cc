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

#include <type_exceptions.hh>

// static initialization
TypeMgr_ptr TypeMgr::f_instance = NULL;

TypeMgr::TypeMgr()
    : f_register()
    , f_em(ExprMgr::INSTANCE())
{
    // register predefined types
    register_type( f_em.make_boolean_type(),
                   new BooleanType(*this));

    register_type( f_em.make_int_const_type(),
                   new IntConstType(*this));

    register_type( f_em.make_fxd_const_type(),
                   new FxdConstType(*this));
}

const Type_ptr TypeMgr::find_unsigned(unsigned digits)
{
    Expr_ptr descr(f_em.make_unsigned_int_type(digits));
    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new UnsignedAlgebraicType( *this, digits);
    register_type(descr, res);
    return res;
}

const Type_ptr TypeMgr::find_default_unsigned()
{
    /* TODO: move this somewhere */
    return find_unsigned(8);
}

const Type_ptr TypeMgr::find_default_unsigned_fixed()
{
    /* TODO: move this somewhere */
    return find_unsigned_fixed(6, 2);
}


const Type_ptr TypeMgr::find_unsigned_array(unsigned digits, unsigned size)
{
    Expr_ptr descr(f_em.make_subscript( f_em.make_unsigned_int_type(digits),
                                        f_em.make_iconst(size)));
    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new ArrayType( *this,
                         find_unsigned(digits), size);
    register_type(descr, res);
    return res;
}

const Type_ptr TypeMgr::find_signed(unsigned digits)
{
    Expr_ptr descr(f_em.make_signed_int_type(digits));
    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new SignedAlgebraicType( *this, digits);
    register_type(descr, res);
    return res;
}

const Type_ptr TypeMgr::find_signed_array(unsigned digits, unsigned size)
{
    Expr_ptr descr(f_em.make_subscript( f_em.make_signed_int_type(digits),
                                        f_em.make_iconst(size)));
    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new ArrayType( *this,
                         find_signed(digits), size);
    register_type(descr, res);
    return res;
}

const Type_ptr TypeMgr::find_signed_fixed(unsigned int_digits, unsigned fract_digits)
{
    Expr_ptr descr(f_em.make_signed_fxd_type(int_digits, fract_digits));
    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new SignedFixedAlgebraicType( *this, int_digits, fract_digits);
    register_type(descr, res);
    return res;
}

const Type_ptr TypeMgr::find_unsigned_fixed(unsigned int_digits, unsigned fract_digits)
{
    Expr_ptr descr(f_em.make_unsigned_fxd_type(int_digits, fract_digits));
    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new UnsignedFixedAlgebraicType( *this, int_digits, fract_digits);
    register_type(descr, res);
    return res;
}


const Type_ptr TypeMgr::find_signed_fixed_array(unsigned int_digits,
                                                unsigned fract_digits,
                                                unsigned size)
{
    Expr_ptr descr(f_em.make_subscript( f_em.make_signed_fxd_type(int_digits,
                                                                  fract_digits),
                                        f_em.make_iconst(size)));
    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new ArrayType( *this,
                         find_signed_fixed(int_digits, fract_digits), size);
    register_type(descr, res);
    return res;
}


const Type_ptr TypeMgr::find_unsigned_fixed_array(unsigned int_digits,
                                                unsigned fract_digits,
                                                unsigned size)
{
    Expr_ptr descr(f_em.make_subscript( f_em.make_unsigned_fxd_type(int_digits,
                                                                  fract_digits),
                                        f_em.make_iconst(size)));
    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new ArrayType( *this,
                         find_unsigned_fixed(int_digits, fract_digits), size);
    register_type(descr, res);
    return res;
}


const Type_ptr TypeMgr::find_enum(ExprSet& lits)
{
    /*
       IMPORTANT: lits ordering has to be canonical for enum types to
       work as expected! Otherwise same set of lits with different
       ordering could be mistakingly seen as a different type.
    */

    Expr_ptr descr(f_em.make_enum_type(lits));
    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new EnumType(*this, lits);
    register_type(descr, res);
    return res;
}

const Type_ptr TypeMgr::find_instance(Expr_ptr identifier)
{
    Expr_ptr descr(f_em.make_params(identifier, NULL));
    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new Instance(*this, identifier);
    register_type(descr, res);
    return res;
}

BooleanType_ptr TypeMgr::as_boolean(const Type_ptr tp) const
{
    BooleanType_ptr res = dynamic_cast <const BooleanType_ptr> (tp);
    assert(res);

    return res;
}

EnumType_ptr TypeMgr::as_enum(const Type_ptr tp) const
{
    EnumType_ptr res = dynamic_cast<EnumType_ptr> (tp);
    assert(res);

    return res;
}

AlgebraicType_ptr TypeMgr::as_algebraic(const Type_ptr tp) const
{
    AlgebraicType_ptr res = dynamic_cast
        <const AlgebraicType_ptr> (tp);
    assert(res);

    return res;
}

SignedAlgebraicType_ptr TypeMgr::as_signed_algebraic(const Type_ptr tp) const
{
    SignedAlgebraicType_ptr res = dynamic_cast
        <const SignedAlgebraicType_ptr> (tp);
    assert(res);

    return res;
}

UnsignedAlgebraicType_ptr TypeMgr::as_unsigned_algebraic(const Type_ptr tp) const
{
    UnsignedAlgebraicType_ptr res = dynamic_cast
        <const UnsignedAlgebraicType_ptr> (tp);
    assert(res);

    return res;
}

SignedFixedAlgebraicType_ptr TypeMgr::as_signed_fixed_algebraic(const Type_ptr tp) const
{
    SignedFixedAlgebraicType_ptr res = dynamic_cast
        <const SignedFixedAlgebraicType_ptr> (tp);
    assert(res);

    return res;
}

UnsignedFixedAlgebraicType_ptr TypeMgr::as_unsigned_fixed_algebraic(const Type_ptr tp) const
{
    UnsignedFixedAlgebraicType_ptr res = dynamic_cast
        <const UnsignedFixedAlgebraicType_ptr> (tp);
    assert(res);

    return res;
}

Instance_ptr TypeMgr::as_instance(const Type_ptr tp) const
{
    Instance_ptr res = dynamic_cast <Instance_ptr> (tp);
    assert(res);

    return res;
}

ArrayType_ptr TypeMgr::as_array(const Type_ptr tp) const
{
    ArrayType_ptr res = dynamic_cast<ArrayType_ptr> (tp);
    assert(res);

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
        return bitwise_result_type(lhs, rhs);
    }
    else if (em.is_binary_relational(expr)) {
        return find_boolean();
    }
    else assert (false); // unexpected
}


/* ternary variant */
Type_ptr TypeMgr::result_type(Expr_ptr expr, Type_ptr cnd,
                              Type_ptr lhs, Type_ptr rhs)
{
    ExprMgr& em = f_em;

    if (em.is_ite(expr)) {
        return ite_result_type(lhs, rhs);
    }
    else assert (false); // unexpected
}

Type_ptr TypeMgr::arithmetical_result_type(Type_ptr lhs, Type_ptr rhs)
{
    // both ops integers -> integer
    if (is_int_const(lhs) && (is_int_const(rhs))) {
        return find_int_const();
    }

    // at least one fxd, the other int or fxd -> fxd
    if ((is_int_const(lhs) && (is_fxd_const(rhs))) ||
        (is_fxd_const(lhs) && (is_int_const(rhs))) ||
        (is_fxd_const(lhs) && (is_fxd_const(rhs)))) {
        return find_fxd_const();
    }

    // at least one algebraic
    if (is_algebraic(lhs) || is_algebraic(rhs)) {

        if ( is_boolean(lhs) || is_enum(lhs) || is_array(lhs) ||
             is_boolean(rhs) || is_enum(rhs) || is_array(rhs)) {

            throw TypeMismatch(lhs->repr(),
                               rhs->repr());
        }

        bool is_fixed = \
            is_fxd_algebraic(lhs) ||
            is_fxd_algebraic(rhs) ;

        bool is_signed = \
            is_signed_algebraic(lhs) ||
            is_signed_algebraic(rhs) ;

        unsigned width = max( calculate_width(lhs),
                              calculate_width(rhs));

        unsigned fract = max( calculate_fract(lhs),
                              calculate_fract(rhs));

        assert (fract <= width); /* sanity */

        /* ! fixed && ! signed --> unsigned int */
        if (!is_fixed && !is_signed) return find_unsigned(width);

        /* ! fixed &&   signed --> signed int */
        if (!is_fixed &&  is_signed) return find_signed(width);

        /*   fixed && ! signed --> unsigned fixed */
        if ( is_fixed && !is_signed) return find_unsigned_fixed(width - fract, fract);

        /*   fixed &&   signed --> signed fixed */
        if ( is_fixed &&  is_signed) return find_signed_fixed(width - fract, fract);

    } /* is_algebraic */

    throw TypeMismatch(lhs->repr(),
                       rhs->repr());

    assert( false ); /* unexpected */
    return NULL;
}

Type_ptr TypeMgr::bitwise_result_type(Type_ptr lhs, Type_ptr rhs)
{
    // both ops integers -> integer
    if (is_int_const(lhs) && (is_int_const(rhs))) {
        return find_int_const();
    }

    // at least one fxd, the other int or fxd -> fxd
    if ((is_int_const(lhs) && (is_fxd_const(rhs))) ||
        (is_fxd_const(lhs) && (is_int_const(rhs))) ||
        (is_fxd_const(lhs) && (is_fxd_const(rhs)))) {
        return find_fxd_const();
    }

    // at least one algebraic
    if (is_algebraic(lhs) || is_algebraic(rhs)) {

        if ( is_boolean(lhs) || is_enum(lhs) || is_array(lhs) ||
             is_boolean(rhs) || is_enum(rhs) || is_array(rhs)) {

            throw TypeMismatch(lhs->repr(),
                               rhs->repr());
        }

        bool is_fixed = \
            is_fxd_algebraic(lhs) ||
            is_fxd_algebraic(rhs) ;

        bool is_signed = \
            is_signed_algebraic(lhs) ||
            is_signed_algebraic(rhs) ;

        unsigned width = max( calculate_width(lhs),
                              calculate_width(rhs));

        unsigned fract = max( calculate_fract(lhs),
                              calculate_fract(rhs));

        assert (fract <= width); /* sanity */

        /* ! fixed && ! signed --> unsigned int */
        if (!is_fixed && !is_signed) return find_unsigned(width);

        /* ! fixed &&   signed --> signed int */
        if (!is_fixed &&  is_signed) return find_signed(width);

        /*   fixed && ! signed --> unsigned fixed */
        if ( is_fixed && !is_signed) return find_unsigned_fixed(width - fract, fract);

        /*   fixed &&   signed --> signed fixed */
        if ( is_fixed &&  is_signed) return find_signed_fixed(width - fract, fract);

    } /* is_algebraic */

    throw TypeMismatch(lhs->repr(),
                       rhs->repr());

    assert( false ); /* unexpected */
    return NULL;
}

Type_ptr TypeMgr::ite_result_type(Type_ptr lhs, Type_ptr rhs)
{
    /* monoliths */
    if (is_boolean(lhs) && is_boolean(rhs))
        return rhs;

    if (is_enum(lhs) && is_enum(rhs) && (lhs == rhs))
        return rhs;

    /* algebraics */
    if (is_int_const(lhs) && is_int_const(rhs))
        return find_default_unsigned();

    if ((is_int_const(lhs) && is_fxd_const(rhs)) ||
        (is_fxd_const(lhs) && is_int_const(rhs)) ||
        (is_fxd_const(lhs) && is_fxd_const(rhs)))
        return find_default_unsigned_fixed();

    // at least one algebraic
    if (is_algebraic(lhs) || is_algebraic(rhs)) {

        if ( is_boolean(lhs) || is_enum(lhs) || is_array(lhs) ||
             is_boolean(rhs) || is_enum(rhs) || is_array(rhs)) {

            throw TypeMismatch(lhs->repr(),
                               rhs->repr());
        }

        bool is_fixed = \
            is_fxd_algebraic(lhs) ||
            is_fxd_algebraic(rhs) ;

        bool is_signed = \
            is_signed_algebraic(lhs) ||
            is_signed_algebraic(rhs) ;

        unsigned width = max( calculate_width(lhs),
                              calculate_width(rhs));

        unsigned fract = max( calculate_fract(lhs),
                              calculate_fract(rhs));

        assert (fract <= width); /* sanity */

        /* ! fixed && ! signed --> unsigned int */
        if (!is_fixed && !is_signed) return find_unsigned(width);

        /* ! fixed &&   signed --> signed int */
        if (!is_fixed &&  is_signed) return find_signed(width);

        /*   fixed && ! signed --> unsigned fixed */
        if ( is_fixed && !is_signed) return find_unsigned_fixed(width - fract, fract);

        /*   fixed &&   signed --> signed fixed */
        if ( is_fixed &&  is_signed) return find_signed_fixed(width - fract, fract);

    } /* is_algebraic */

    throw TypeMismatch(lhs->repr(),
                       rhs->repr());

    assert (false); // unexpected
    return NULL;
}

/* low level service */
void TypeMgr::register_type(const Expr_ptr expr, Type_ptr vtype)
{
    assert ((NULL != expr) && (NULL != vtype) && (! lookup_type(expr)));
    DEBUG << "Registering new type: " << expr << endl;

    f_register [ expr ] = vtype;
}

unsigned TypeMgr::calculate_width(Type_ptr type) const
{
    if (is_int_const(type) ||
        is_fxd_const(type) ||
        is_enum(type)) {
        return 1; /* monolithic */
    }
    else if (is_signed_algebraic(type)) {
        return as_signed_algebraic(type)->width();
    }
    else if (is_unsigned_algebraic(type)) {
        return as_unsigned_algebraic(type)->width();
    }
    else if (is_signed_fixed_algebraic(type)) {
        return \
            as_signed_fixed_algebraic(type)->width() +
            as_signed_fixed_algebraic(type)->fract() ;
    }
    else if (is_unsigned_fixed_algebraic(type)) {
        return \
            as_unsigned_fixed_algebraic(type)->width() +
            as_unsigned_fixed_algebraic(type)->fract() ;
    }

    assert(false); /* unexpected */
    return 0;
}

unsigned TypeMgr::calculate_fract(Type_ptr type) const
{
    if (is_int_const(type) ||
        is_fxd_const(type) ||
        is_enum(type)) {
        return 0; /* monolithic */
    }
    else if (is_signed_algebraic(type)) {
        return 0;
    }
    else if (is_unsigned_algebraic(type)) {
        return 0;
    }
    else if (is_signed_fixed_algebraic(type)) {
        return as_signed_fixed_algebraic(type)->fract() ;
    }
    else if (is_unsigned_fixed_algebraic(type)) {
        return as_unsigned_fixed_algebraic(type)->fract() ;
    }

    assert(false); /* unexpected */
    return 0;
}
