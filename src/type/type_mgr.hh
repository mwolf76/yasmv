/**
 * @file type_mgr.hh
 * @brief Type system classes (TypeMgr)
 *
 * This header file contains the declarations required by the Type
 * Manager class.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#ifndef TYPE_MGR_H
#define TYPE_MGR_H

#include <boost/unordered_map.hpp>

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <type/typedefs.hh>
#include <type/type_resolver.hh>

/*
   The TypeMgr has two well-defined responsibilites:

   1. It keeps track of types that has been defined;
   2. It instantiates (and owns) type descriptors (Type objects).
*/

class TypeMgr {

    // reserved
    Type_ptr f_ctx_type;

    /* Shared enums and literals */
    symb::Literals f_lits;

public:
    const TimeType_ptr find_time();

    const ScalarType_ptr find_boolean();
    const ArrayType_ptr find_boolean_array(unsigned size);

    /* Remark: following C scoping rules for enums, enums are *globals* */
    const ScalarType_ptr find_enum(ExprSet& lits);
    const ArrayType_ptr find_enum_array(ExprSet& lits, unsigned size);

    const ScalarType_ptr find_constant(unsigned width);

    const ScalarType_ptr find_signed(unsigned width);
    const ArrayType_ptr  find_signed_array(unsigned width, unsigned size);

    const ScalarType_ptr find_unsigned(unsigned width);
    const ArrayType_ptr find_unsigned_array(unsigned width, unsigned size);

    const Type_ptr find_type_by_def(const Expr_ptr expr);

    const ScalarType_ptr find_instance(Expr_ptr module, Expr_ptr params);
    const StringType_ptr find_string();

    const ArrayType_ptr find_array_type( ScalarType_ptr of, unsigned nelems);

    const symb::Literals& literals() const
    { return f_lits; }

    inline symb::Resolver_ptr resolver()
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

    // lookup up a type from its repr, returns NULL if not found
    inline Type_ptr lookup_type(const Expr_ptr expr)
    { return f_register [ expr ]; }

    void register_type(const Expr_ptr expr, Type_ptr vtype);

    /* local data */
    TypeMap f_register;

    // ref to expr manager
    ExprMgr& f_em;

    // ref to internal resolver
    TypeResolver f_resolver;
};

#endif
