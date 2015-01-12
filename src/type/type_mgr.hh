/**
 *  @file type_mgr.hh
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
 **/

#ifndef TYPE_MGR_H
#define TYPE_MGR_H

#include <boost/unordered_map.hpp>

#include <symb/symbol.hh>

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <type/type.hh>
#include <type/type_resolver.hh>

typedef boost::unordered_map<Expr_ptr, Type_ptr, PtrHash, PtrEq> TypeMap;

/* The TypeMgr has three well-defined responsibilites:

   1. It keeps track of types that has been defined;

   2. It instantiates (and owns) type descriptors (Type objects);

   3. It is the single authoritative source for determining the
   resulting type of an operand, via the result_type methods. */

typedef class TypeMgr* TypeMgr_ptr;

class TypeMgr {

    // reserved
    Type_ptr f_ctx_type;

    /* Shared enums and literals */
    Literals f_lits;

public:

    /* -- inference --------------------------------------------------------- */
    const ScalarType_ptr find_boolean();

    const ScalarType_ptr find_int_const(unsigned digits);
    const ScalarType_ptr find_signed(unsigned digits);
    const ScalarType_ptr find_signed(unsigned magnitude, unsigned fractional);

    const ArrayType_ptr find_signed_array(unsigned digits,
                                          unsigned size);
    const ArrayType_ptr find_signed_array(unsigned magnitude,
                                          unsigned fractional,
                                          unsigned size);

    const ScalarType_ptr find_unsigned(unsigned digits);
    const ScalarType_ptr find_unsigned(unsigned magnitude, unsigned fractional);

    const ArrayType_ptr find_unsigned_array(unsigned digits,
                                            unsigned size);
    const ArrayType_ptr find_unsigned_array(unsigned magnitude,
                                            unsigned fractional,
                                            unsigned size);

    const Type_ptr find_type_by_def(const Expr_ptr expr);

    /* Remark: following C scoping rules for enums, enums are *globals* */
    const ScalarType_ptr find_enum(ExprSet& lits);

    const Literals& literals() const
    { return f_lits; }

    /** Determine the resulting type of an operation given the type of its
        operands. */
    Type_ptr result_type(Expr_ptr expr, Type_ptr lhs);
    Type_ptr result_type(Expr_ptr expr, Type_ptr lhs, Type_ptr rhs);
    Type_ptr result_type(Expr_ptr expr, Type_ptr cnd, Type_ptr lhs, Type_ptr rhs);

    inline Resolver_ptr resolver()
    { return &f_resolver; }

    /** Singleton instance accessor */
    static inline TypeMgr& INSTANCE() {
        if (! f_instance) {
            f_instance = new TypeMgr();
        }

        return (*f_instance);
    }

    /** A ref to the ExprMgr */
    inline ExprMgr& em() const
    { return f_em; }

protected:
    TypeMgr();
    ~TypeMgr();

private:
    static TypeMgr_ptr f_instance;

    /* --- low-level services ----------------------------------------------- */

    /** service of result_type */
    Type_ptr arithmetical_result_type(Type_ptr lhs, Type_ptr rhs);
    Type_ptr relational_result_type(Type_ptr lhs, Type_ptr rhs);
    Type_ptr logical_result_type(Type_ptr lhs, Type_ptr rhs);
    Type_ptr ite_result_type(Type_ptr lhs, Type_ptr rhs);
    Type_ptr cast_result_type(Type_ptr lhs, Type_ptr rhs);

    // register a type
    inline void register_type(const Expr_ptr expr, Type_ptr vtype) {
        assert ((NULL != expr) && (NULL != vtype) && (! lookup_type(expr)));
        f_register [ expr ] = vtype;
    }

    // lookup up a type, returns NULL if not found
    inline Type_ptr lookup_type(const Expr_ptr expr)
    { return f_register [ expr ]; }

    /* local data */
    TypeMap f_register;

    // ref to expr manager
    ExprMgr& f_em;

    // ref to internal resolver
    TypeResolver f_resolver;
};

#endif
