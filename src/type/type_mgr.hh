/**
 *  @file type_mgr.hh
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

#ifndef TYPE_MGR_H
#define TYPE_MGR_H

#include <expr.hh>
#include <expr_mgr.hh>

typedef class Type* Type_ptr; // fwd
typedef unordered_map<Expr_ptr, Type_ptr, PtrHash, PtrEq> TypeMap;
typedef pair<TypeMap::iterator, bool> TypeHit;

/**
    The TypeMgr has two well-defined responsibilites:

    1. It keeps track of types that has been defined;

    2. It instantiates (and owns) type descriptors (Type objects);

    NOTE: there at distinct concepts of type that should not be mixed
    together: Here we talk about the type of an expression from a
    static analysis PoV. An expression can be boolean, integer, a
    particular enum (TODO: prohibit intersection) or an instance of a
    certain module. And that's final.

    When it comes to encoding though, a variable can be either signed
    or unsigned, with a given number of bits. But this, *by design* is
    completely ignored by the type inferrer.

    Moreover, a wff temporal formula is considered boolean w.r.t. type
    inference, it will be responsibility of the formula-analyzer to
    determine whether its a CTL/LTL/INVAR, and in different section of
    the system different actions can be taken according to this.
  */
typedef class TypeMgr* TypeMgr_ptr;
class TypeMgr {
public:

    /* -- inference --------------------------------------------------------- */
    inline const Type_ptr find_boolean()
    { return f_register[ f_em.make_boolean_type() ]; }

    inline const Type_ptr find_integer() // abstract
    { return f_register[ f_em.make_integer_type() ]; }

    /* -- decls ------------------------------------------------------------- */
    const Type_ptr find_unsigned(unsigned bits);
    const Type_ptr find_signed(unsigned bits);
    const Type_ptr find_range(const Expr_ptr from, const Expr_ptr to);

    const Type_ptr find_enum(ExprSet& lits);
    const Type_ptr find_instance(Expr_ptr identifier);

    // -- is_xxx predicates ----------------------------------------------------

    /* int_enum is an important subcase of enumeratives. An
       all-integer valued enumerative can safely be treated as an
       integer w.r.t. type inferring. */
    bool is_boolean(const Type_ptr tp) const;

    bool is_integer(const Type_ptr tp) const;
    bool is_int_finite(const Type_ptr tp) const;
    bool is_int_range(const Type_ptr tp) const;
    bool is_int_enum(const Type_ptr tp) const;

    bool is_enum(const Type_ptr tp) const;
    bool is_instance(const Type_ptr tp) const;

    // -- as_xxx accessors ------------------------------------------------------
    typedef class BooleanType* BooleanType_ptr;
    BooleanType_ptr as_boolean(const Type_ptr tp) const;

    typedef class IntegerType* IntegerType_ptr;
    IntegerType_ptr as_integer(const Type_ptr tp) const;

    typedef class FiniteIntegerType* FiniteIntegerType_ptr;
    FiniteIntegerType_ptr as_int_finite(const Type_ptr tp) const;

    typedef class IntRangeType* IntRangeType_ptr;
    IntRangeType_ptr as_int_range(const Type_ptr tp) const;

    typedef class EnumType* EnumType_ptr;
    EnumType_ptr as_enum(const Type_ptr tp) const;

    typedef class Instance* Instance_ptr;
    Instance_ptr as_instance(const Type_ptr tp) const;

    // singleton instance accessor
    static inline TypeMgr& INSTANCE() {
        if (! f_instance) {
            f_instance = new TypeMgr();
        }

        return (*f_instance);
    }

    inline ExprMgr& em() const
    { return f_em; }

protected:
    TypeMgr();
    ~TypeMgr();

private:
    static TypeMgr_ptr f_instance;

    /* --- low-level services ----------------------------------------------- */

    // register a type
    void register_type(const Expr_ptr expr, Type_ptr vtype);

    // lookup up a type, returns NULL if not found
    inline Type_ptr lookup_type(const Expr_ptr expr)
    { return f_register [ expr ]; }

    /* local data */
    TypeMap f_register;

    // ref to expr manager
    ExprMgr& f_em;
};

#endif
