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
typedef unordered_map<FQExpr, Type_ptr, FQExprHash, FQExprEq> TypeMap;
typedef pair<TypeMap::iterator, bool> TypeHit;

/**
    The TypeMgr has two well-defined responsibilites:

    1. It keeps track of the type of FQExprs in the system (such as
    those determined by the inferrer);

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

    /** @brief Returns Type object for given expr, or NULL if none is
        available. */
    const Type_ptr type(const FQExpr& fqexpr) const
    {
        TypeMap::const_iterator eye = f_map.find(fqexpr);
        Type_ptr res = NULL;

        // cache miss
        if (eye == f_map.end()) return NULL;

        // TODO: something missing here!!!
        return res;
    }

    inline void set_type(const FQExpr fqexpr, const Type_ptr tp)
    { f_map[ fqexpr ] = tp; }

    /* -- inference --------------------------------------------------------- */
    inline const Type_ptr find_boolean()
    { return f_register[ FQExpr(f_em.make_boolean_type()) ]; }

    inline const Type_ptr find_integer() // abstract
    { return f_register[ FQExpr(f_em.make_integer_type()) ]; }

    /* -- decls ------------------------------------------------------------- */
    const Type_ptr find_unsigned(unsigned bits);
    const Type_ptr find_signed(unsigned bits);
    const Type_ptr find_range(const Expr_ptr from, const Expr_ptr to);

    const Type_ptr find_enum(Expr_ptr ctx, ExprSet_ptr lits);
    const Type_ptr find_instance(Expr_ptr identifier);

    // -- is_xxx predicates ----------------------------------------------------

    /* int_enum is an important subcase of enumeratives. An
       all-integer valued enumerative can safely be treated as an
       integer w.r.t. type inferring. */
    bool is_boolean(const Type_ptr tp) const;
    bool is_integer(const Type_ptr tp) const;
    bool is_int_range(const Type_ptr tp) const;
    bool is_int_enum(const Type_ptr tp) const;
    bool is_instance(const Type_ptr tp) const;

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
    void register_type(const FQExpr fqexpr, Type_ptr vtype);

    // lookup up a type, returns NULL if not found
    inline Type_ptr lookup_type(const FQExpr fqexpr)
    { return f_register [ fqexpr ]; }

    /* local data */
    TypeMap f_register;
    TypeMap f_map;

    // ref to expr manager
    ExprMgr& f_em;
};

#endif
