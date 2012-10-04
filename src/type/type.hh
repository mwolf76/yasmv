/**
 *  @file type.hh
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

#ifndef TYPE_H
#define TYPE_H

#include <common.hh>

#include <expr.hh>
#include <fqexpr.hh>
#include <expr_mgr.hh>
#include <type_mgr.hh>

/* -- Supported data types: boolean, ranged integers, finite-width
   integers, pure-int enums, symbolic enums, mixed enums,
   instances.
*/

// Reminder: types are *immutable* by design!

/* Basic Type class. Is.. nothing. */
typedef class Type* Type_ptr;
class Type : public Object {
public:
    inline Expr_ptr get_repr() const
    { return f_repr; }

    virtual ~Type()
    {}

protected:
    Type(TypeMgr &owner)
        : f_owner(owner)
        , f_repr(NULL)
    {}

    TypeMgr& f_owner;
    Expr_ptr f_repr;
};

typedef class BooleanType* BooleanType_ptr;
class BooleanType : public Type {
protected:
    friend class TypeMgr; // ctors not public
    BooleanType(TypeMgr& owner)
        : Type(owner)

    {
        f_repr = f_owner.em().make_boolean_type();
    }
};

typedef class Temporalype* TemporalType_ptr;
class TemporalType : public Type {
protected:
    friend class TypeMgr; // ctors not public
    TemporalType(TypeMgr& owner)
        : Type(owner)
    {
        f_repr = f_owner.em().make_temporal_type();
    }
};

typedef class IntegerType* IntegerType_ptr;
class IntegerType : public Type {
protected:
    friend class TypeMgr; // ctors not public
    IntegerType(TypeMgr& owner) // abstract
        : Type(owner)
        , f_abstract(true)
    {
        f_repr = f_signed
            ? f_owner.em().make_signed_type(f_size)
            : f_owner.em().make_unsigned_type(f_size)
            ;
    }

    IntegerType(TypeMgr& owner, unsigned size, bool is_signed=false)
        : Type(owner)
        , f_size(size)
        , f_signed(is_signed)
    {
        f_repr = f_signed
            ? f_owner.em().make_signed_type(f_size)
            : f_owner.em().make_unsigned_type(f_size)
            ;
    }

public:
    inline unsigned size() const
    { return f_size; }

    inline bool is_signed() const
    { return f_signed; }

    inline bool is_abstract() const
    { return f_abstract; }

private:
    unsigned f_size;
    bool f_signed;
    bool f_abstract;
};

typedef class IntRangeType* IntRangeType_ptr;
class IntRangeType : public Type {
protected:
    friend class TypeMgr; // ctors not public
    IntRangeType(TypeMgr& owner, const Expr_ptr min, const Expr_ptr max)
        : Type(owner)
    {
        ExprMgr& em = f_owner.em();

        ExprType min_symbtype  = min->f_symb;
        assert (ICONST == min_symbtype  ||
                SWCONST == min_symbtype ||
                UWCONST == min_symbtype );
        f_min = min->value();

        ExprType max_symbtype  = max->f_symb;
        assert (ICONST == max_symbtype  ||
                SWCONST == max_symbtype ||
                UWCONST == max_symbtype );
        f_max = max->value();

        f_repr = em.make_range_type(em.make_iconst(f_min),
                                    em.make_iconst(f_max));
    }

public:
    inline const value_t min() const
    { return f_min; }

    inline const value_t max() const
    { return f_max; }

    unsigned size() const
    { assert(0); return -1; } // TODO...

private:
    value_t f_min;
    value_t f_max;
};

typedef class EnumType* EnumType_ptr;
class EnumType : public Type {
protected:
    friend class TypeMgr; // ctors not public
    EnumType(TypeMgr& owner, ExprSet literals)
        : Type(owner)
        , f_literals(literals)
    {
        // TODO: kill cast
        f_repr = f_owner.em().make_enum_type(const_cast<ExprSet_ptr> (&f_literals));
    }

public:
    const ExprSet& literals() const
    { return f_literals; }

    bool has_symbs() const;
    bool has_numbers() const;

private:
    ExprSet f_literals;
};

typedef class Instance* Instance_ptr;
class Instance : public Type {
protected:
    friend class TypeMgr; // ctors not public
    Instance(TypeMgr& owner, Expr* identifier)
        : Type(owner)
        , f_identifier(identifier)
          // , f_module(NULL) // flawed design, types are immutable.
          // , f_params()
    {}

public:
    // const ExprVector& params() const
    // { return f_params; }

    const Expr_ptr identifier() const
    { return f_identifier; }

    // void add_param(const Expr_ptr expr)
    // { f_params.push_back(expr); }

    // const IModule_ptr get_module() const
    // { assert(f_module); return f_module; }

    // void set_module(IModule_ptr module)
    // { assert(!f_module); assert(module); f_module = module; }

private:
    const Expr_ptr f_identifier;
    // IModule_ptr f_module;
    // ExprVector f_params;
};

#endif
