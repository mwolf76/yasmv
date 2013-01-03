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
#include <cudd_mgr.hh>

#include <expr.hh>
#include <expr_mgr.hh>

#include <type_mgr.hh>

/* Supported data types: boolean, integers (signed and unsigned),
   fixed-point, enums, module instances, arrays of all-of-the-above. */

/* REMARK types are *immutable* by design! */

// ostream helper, uses FQExpr printer (see expr/expr.cc)
ostream& operator<<(ostream& os, Type_ptr type);

// ostream helper, uses FQExpr printer (see expr/expr.cc)
ostream& operator<<(ostream& os, const Type_ptr type);

/* Basic Type class. Is.. nothing. */
typedef class Type* Type_ptr;
class Type : public Object {
public:
    Expr_ptr repr() const
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

typedef class AlgebraicType* AlgebraicType_ptr;
class AlgebraicType : public Type {
public:
    virtual unsigned width() const =0;
    virtual bool is_signed() const =0;

    ADD *dds() const
    { return f_dds; }

protected:
    friend class TypeMgr; // ctors not public
    AlgebraicType(TypeMgr& owner, ADD *dds = NULL);

    // this is reserved for temp encodings, it's NULL for ordinary algebraics
    ADD *f_dds;
};


typedef class SignedAlgebraicType* SignedAlgebraicType_ptr;
class SignedAlgebraicType : public AlgebraicType {
public:
    unsigned width() const
    { return f_width; }

    bool is_signed() const
    { return true; }

 protected:
    friend class TypeMgr; // ctors not public
    SignedAlgebraicType(TypeMgr& owner, unsigned width, ADD *dds = NULL);

    unsigned f_width;
};

typedef class UnsignedAlgebraicType* UnsignedAlgebraicType_ptr;
class UnsignedAlgebraicType : public AlgebraicType {
public:
    unsigned width() const
    { return f_width; }

    bool is_signed() const
    { return false; }

protected:
    friend class TypeMgr; // ctors not public
    UnsignedAlgebraicType(TypeMgr& owner, unsigned width, ADD *dds = NULL);

    unsigned f_width;
};


typedef class FixedAlgebraicType* FixedAlgebraicType_ptr;
class FixedAlgebraicType : public AlgebraicType {
public:
    unsigned width() const
    { return f_width; }

    unsigned fract() const
    { return f_fract; }

    /* in current implementation fixed is signed only */
    bool is_signed() const
    { return true; }

protected:
    friend class TypeMgr; // ctors not public
    FixedAlgebraicType(TypeMgr& owner, unsigned width, unsigned fract, ADD *dds = NULL);

    unsigned f_width;
    unsigned f_fract;
};


typedef class ArrayType* ArrayType_ptr;
class ArrayType : public Type {
public:
    unsigned size() const
    { return f_size; }

    Type_ptr of() const
    { return f_of; }

protected:
    friend class TypeMgr; // ctors not public
    ArrayType(TypeMgr& owner, Type_ptr of, unsigned size);

    Type_ptr f_of;
    unsigned f_size;
};

typedef class EnumType* EnumType_ptr;
class EnumType : public Type {
protected:
    friend class TypeMgr; // ctors not public
    EnumType(TypeMgr& owner, ExprSet& literals);

public:
    const ExprSet& literals() const
    { return f_literals; }

private:
    ExprSet f_literals;
};

typedef class Instance* Instance_ptr;
class Instance : public Type {
protected:
    friend class TypeMgr; // ctors not public
    Instance(TypeMgr& owner, Expr_ptr identifier);

public:
    const Expr_ptr identifier() const
    { return f_identifier; }

private:
    const Expr_ptr f_identifier;
};

#endif
