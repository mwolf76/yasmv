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
#include <expr_mgr.hh>

#include <type_mgr.hh>

/* Supported data types: boolean, ranged integers, finite-width
   integers, (pure-int) enums, module instances. */

// NOTE: types are *immutable* by design!

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
    BooleanType(TypeMgr& owner);
};

typedef class IntegerType* IntegerType_ptr;
class IntegerType : public Type {
protected:
    friend class TypeMgr; // ctors not public
    IntegerType(TypeMgr& owner);
};

typedef class FiniteIntegerType* FiniteIntegerType_ptr;
class FiniteIntegerType : public IntegerType {
protected:
    friend class TypeMgr; // ctors not public
    FiniteIntegerType(TypeMgr& owner, unsigned width, bool is_signed);

    unsigned f_width;
    bool f_signed;

public:
    inline unsigned width() const
    { return f_width; }

    inline bool is_signed() const
    { return f_signed; }
};

typedef class IntRangeType* IntRangeType_ptr;
class IntRangeType : public Type {
protected:
    friend class TypeMgr; // ctors not public
    IntRangeType(TypeMgr& owner, value_t min, value_t max);

public:
    inline const value_t min() const
    { return f_min; }

    inline const value_t max() const
    { return f_max; }

private:
    value_t f_min;
    value_t f_max;
};

typedef class EnumType* EnumType_ptr;
class EnumType : public Type {
protected:
    friend class TypeMgr; // ctors not public
    EnumType(TypeMgr& owner, ExprSet& literals);

public:
    const ExprSet& literals() const
    { return f_literals; }

    bool has_symbs() const;

private:
    ExprSet f_literals;
};

typedef class Instance* Instance_ptr;
class Instance : public Type {
protected:
    friend class TypeMgr; // ctors not public
    Instance(TypeMgr& owner, Expr* identifier, ExprVector& params);

public:
    const ExprVector& params() const
    { return f_params; }

    const Expr_ptr identifier() const
    { return f_identifier; }

private:
    const Expr_ptr f_identifier;
    ExprVector f_params;
};

#endif
