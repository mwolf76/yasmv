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

#include <type_resolver.hh>

const int DEFAULT_INTTYPE_SIZE = 8;

// static initialization
TypeMgr_ptr TypeMgr::f_instance = NULL;

TypeMgr::TypeMgr()
    : f_register()
    , f_em(ExprMgr::INSTANCE())
    , f_resolver(* new TypeResolver(* this))
{
    f_at = new AnyType(*this);
    register_type( f_em.make_any_type(), f_at);

    f_bt = new BooleanType(*this);
    register_type( f_em.make_boolean_type(), f_bt);
    f_propositionals.insert(f_bt);

    f_ict = new IntConstType(*this);
    register_type( f_em.make_int_const_type(), f_ict);
    f_arithmeticals.insert(f_ict);

    f_uat = new UnsignedAlgebraicType(*this);
    register_type (f_em.make_abstract_unsigned_int_type(), f_uat);
    f_arithmeticals.insert(f_uat);

    f_uaat = new ArrayType(*this, f_uat);
    register_type(f_em.make_abstract_array_type( f_uat->repr()), f_uaat );
    f_arrays.insert(f_uaat);

    f_sat = new SignedAlgebraicType(*this);
    register_type (f_em.make_abstract_signed_int_type(), f_sat);
    f_arithmeticals.insert(f_sat);

    f_saat = new ArrayType(*this, f_sat);
    register_type(f_em.make_abstract_array_type( f_sat->repr()), f_saat );
    f_arrays.insert(f_saat);
}

bool TypeMgr::check_type(Type_ptr tp, TypeSet &allowed)
{
    assert(NULL != tp);

    // perfect matching, no further fuss
    if (allowed.end() != allowed.find(tp))
        return true;

    // it was not found, all compatible abstract are already there -> fail
    if (tp->is_abstract())
        return false;

    if (is_unsigned_algebraic(tp))
        return allowed.end() != allowed.find( f_uat );

    if (is_signed_algebraic(tp))
        return allowed.end() != allowed.find( f_sat );

    return false;
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
{ return find_unsigned(DEFAULT_INTTYPE_SIZE); }

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

const Type_ptr TypeMgr::find_default_signed()
{ return find_signed(DEFAULT_INTTYPE_SIZE); }

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

const Type_ptr TypeMgr::find_array_type( Type_ptr of )
{
    Expr_ptr descr(f_em.make_abstract_array_type( of->repr() ));

    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new ArrayType( *this, of );

    register_type(descr, res);
    return res;
}

const Type_ptr TypeMgr::find_range_type( Type_ptr of )
{
    Expr_ptr descr(f_em.make_abstract_range_type( of->repr() ));

    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new RangeType( *this, of );

    register_type(descr, res);
    return res;
}

const Type_ptr TypeMgr::find_set_type  ( Type_ptr of )
{
    Expr_ptr descr(f_em.make_abstract_set_type( of->repr() ));

    Type_ptr res = lookup_type(descr);
    if (NULL != res) return res;

    // new type, needs to be registered before returning
    res = new SetType( *this, of );

    register_type(descr, res);
    return res;
}

void TypeMgr::add_enum(Expr_ptr ctx, Expr_ptr name, ExprSet& lits)
{
    /*
       IMPORTANT: lits ordering has to be canonical for enum types to
       work as expected! Otherwise same set of lits with different
       ordering could be mistakingly seen as a different type.
    */
    Expr_ptr fullname = ExprMgr::INSTANCE().make_dot( ctx, name );

    if (NULL != lookup_type(fullname)) {
        assert(0); // tODO: better error handling
    }

    EnumType_ptr tp = new EnumType( *this, lits );

    // Define the ENUM
    IEnum_ptr enm = new Enum(ctx, name, tp);
    f_enums.insert( make_pair<FQExpr,
                    IEnum_ptr>( FQExpr( ctx, name), enm));

    // Literals are all maintained together by the type mgr. This
    // greatly simplifies the resolver.
    for (ExprSet::iterator eye = lits.begin(); eye != lits.end(); ++ eye) {
        f_lits.insert( make_pair<FQExpr,
                                 ILiteral_ptr>(FQExpr( fullname, *eye),
                                               new Literal(enm, *eye)));
    }

    // new type, needs to be registered before returning
    register_type(fullname, tp);
}

const Type_ptr TypeMgr::find_enum(Expr_ptr ctx, Expr_ptr name)
{
    Type_ptr res = lookup_type(ExprMgr::INSTANCE().make_dot(ctx, name));
    assert( NULL != res ); // TODO error handling

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

ArrayType_ptr TypeMgr::as_array(const Type_ptr tp) const
{
    ArrayType_ptr res = dynamic_cast<ArrayType_ptr> (tp);
    assert(res);

    return res;
}

RangeType_ptr TypeMgr::as_range(const Type_ptr tp) const
{
    RangeType_ptr res = dynamic_cast<RangeType_ptr> (tp);
    assert(res);

    return res;
}

SetType_ptr TypeMgr::as_set(const Type_ptr tp) const
{
    SetType_ptr res = dynamic_cast<SetType_ptr> (tp);
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
        return logical_result_type(lhs, rhs);
    }
    else if (em.is_binary_relational(expr) ||
             em.is_binary_enumerative(expr)){
        return find_boolean();
    }
    else assert (false); // unexpected
}

/* ternary variant */
Type_ptr TypeMgr::result_type(Expr_ptr expr, Type_ptr cnd,
                              Type_ptr lhs, Type_ptr rhs)
{
    ExprMgr& em = f_em;

    assert(is_boolean(cnd));
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

    // at least one algebraic -> algebraic
    if (is_algebraic(lhs) || is_algebraic(rhs)) {

        if ( is_boolean(lhs) || is_enum(lhs) || is_array(lhs) ||
             is_boolean(rhs) || is_enum(rhs) || is_array(rhs)) {

            throw TypeMismatch(lhs->repr(),
                               rhs->repr());
        }

        bool is_signed = \
            is_signed_algebraic(lhs) ||
            is_signed_algebraic(rhs) ;

        unsigned width = max( calculate_width(lhs),
                              calculate_width(rhs));

        return (!is_signed)
            ? find_unsigned(width)
            : find_signed(width)
            ;
    }

    throw TypeMismatch(lhs->repr(),
                       rhs->repr());

    assert( false ); /* unexpected */
    return NULL;
}

Type_ptr TypeMgr::logical_result_type(Type_ptr lhs, Type_ptr rhs)
{
    // both ops booleans -> boolean
    if (is_boolean(lhs) && (is_boolean(rhs))) {
        return find_boolean();
    }

    // both ops integers -> integer
    if (is_int_const(lhs) && (is_int_const(rhs))) {
        return find_int_const();
    }

    // at least one algebraic -> algebraic
    if (is_algebraic(lhs) || is_algebraic(rhs)) {

        if ( is_boolean(lhs) || is_enum(lhs) || is_array(lhs) ||
             is_boolean(rhs) || is_enum(rhs) || is_array(rhs)) {

            throw TypeMismatch(lhs->repr(),
                               rhs->repr());
        }

        bool is_signed = \
            is_signed_algebraic(lhs) ||
            is_signed_algebraic(rhs) ;

        unsigned width = max( calculate_width(lhs),
                              calculate_width(rhs));

        return (!is_signed)
            ? find_unsigned(width)
            : find_signed(width)
            ;
    }

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

    // at least one algebraic -> algebraic
    if (is_algebraic(lhs) || is_algebraic(rhs)) {

        if ( is_boolean(lhs) || is_enum(lhs) || is_array(lhs) ||
             is_boolean(rhs) || is_enum(rhs) || is_array(rhs)) {

            throw TypeMismatch(lhs->repr(),
                               rhs->repr());
        }

        bool is_signed = \
            is_signed_algebraic(lhs) ||
            is_signed_algebraic(rhs) ;

        unsigned width = max( calculate_width(lhs),
                              calculate_width(rhs));

        return (!is_signed)
            ? find_unsigned(width)
            : find_signed(width)
            ;
    }

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
    if (is_boolean(type)   ||
        is_int_const(type) ||
        is_enum(type)) {
        return 1; /* monolithic */
    }
    else if (is_signed_algebraic(type)) {
        return as_signed_algebraic(type)->width();
    }
    else if (is_unsigned_algebraic(type)) {
        return as_unsigned_algebraic(type)->width();
    }
    else if (is_array(type)) {
        assert(false); // FIXME yet to be supported
    }

    assert(false); /* unexpected */
    return 0;
}
