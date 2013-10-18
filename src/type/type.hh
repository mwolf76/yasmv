/**
 *  @file type.hh
 *  @brief Type system classes
 *
 *  This module contains definitions and services that implement type
 *  classes. YASMINE's types can be classified as (a) Monolithic types
 *  (i.e. that can be represented using a single DD), (b) Algebraic
 *  types (i.e. that are represented using a vector of DDs) or (c)
 *  Array types. The type system is organized as follows:
 *
 *  MONOLITHIC types
 *  ================
 *  + Booleans (type keyword is 'boolean')
 *  + Enumeratives (aka sets) (e.g. { LOUIE, HUEWEY, DEWEY })

 *  ALGEBRAIC types
 *  ===============
 *  + Signed integers(N) (type keyword is 'signed int' or just 'int'),
 *  where N is the number of hexadecimal digits used in the
 *  representation.
 *
 *  + Unsigned integers(N) (type keyword is 'unsigned int'), where N
 *  has the same meaning as above.
 *
 *  COMPOSITE types
 *  ===============
 *
 *  + ARRAYS
 *  + RANGES
 *  + SETS
 *
 * Remark: numeric constants are *always* unsigned and have the
 * special reserved abstract types 'unsigned int(0)'.
 *
 * Type Aliases
 * ============
 *
 * A few type aliases are provided, to make YASMINE's type system look
 * closer to C99's. These type aliases are just synctactig sugar for
 * the type classes defined above, and their usage though recommended
 * is in no way mandatory.
 *
 * INTEGER type aliases:
 * uint8_t,  int8_t
 * uint16_t, int16_t
 * uint32_t, int32_t
 * uint64_t, int64_t
 *
 * Explicit type conversions(casts)
 * ================================
 *
 * C-like Casts operator are provided to force conversions among the
 * various algebraic types.
 *
 * Implicit type conversions
 * =========================
 *
 * To mimic C operators behavior, implicit type conversions (disabled
 * by default) can be enabled so that when expressions of different
 * type are encountered during the compilation of an algebraic
 * operator, type conversions take place as a pre-processing. The
 * following rules apply:
 *
 * 1. When one of the two operands is signed the other one is also converted to signed.
 * 2. The size of the result fits the largest size of the involved operands.
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

/* _ptr typdefs */
typedef class Type* Type_ptr;
typedef class BooleanType* BooleanType_ptr;
typedef class SignedAlgebraicType* SignedAlgebraicType_ptr;
typedef class UnsignedAlgebraicType* UnsignedAlgebraicType_ptr;
typedef class EnumType* EnumType_ptr;
typedef class SetType* SetType_ptr;
typedef class ArrayType* ArrayType_ptr;
typedef class RangeType* RangeType_ptr;

typedef list<Type_ptr> TypeList;
typedef set<Type_ptr> TypeSet;

// reserved for resolution
typedef class CtxType* CtxType_ptr;

// ostream helper, uses FQExpr printer (see expr/expr.cc)
ostream& operator<<(ostream& os, Type_ptr type);

// ostream helper, uses FQExpr printer (see expr/expr.cc)
ostream& operator<<(ostream& os, const Type_ptr type);

class TypeMgr; // fwd

/** Basic Type class. */
class Type : public Object {
public:
    Expr_ptr repr() const
    { return f_repr; }

    bool is_abstract() const
    { return f_abstract; }

    virtual ~Type()
    {}

protected:
    Type(TypeMgr &owner, bool abstract = false)
        : f_owner(owner)
        , f_repr(NULL)
        , f_abstract(abstract)
    {}

    TypeMgr& f_owner;
    Expr_ptr f_repr;
    bool f_abstract;
};

/** Any (scalar) type */
class AnyType : public Type {
protected:
    friend class TypeMgr; // ctors not public
    AnyType(TypeMgr& owner);
};

/** Boolean type */
class BooleanType : public Type {
protected:
    friend class TypeMgr; // ctors not public
    BooleanType(TypeMgr& owner);
};

/** Integer constants type (always unsigned) */
typedef class IntConstType* IntConstType_ptr;
class IntConstType : public Type {
protected:
    friend class TypeMgr; // ctors not public
    IntConstType(TypeMgr& owner);
};

/** Signed integers */
typedef class SignedAlgebraicType* SignedAlgebraicType_ptr;
class SignedAlgebraicType : public Type {
public:
    unsigned width() const
    { return f_width; }

    ADD *dds() const
    { return f_dds; }

 protected:
    friend class TypeMgr; // ctors not public
    SignedAlgebraicType(TypeMgr& owner); // abstract
    SignedAlgebraicType(TypeMgr& owner, unsigned width, ADD *dds = NULL);

    unsigned f_width;

    // this is reserved for temp encodings, it's NULL for ordinary algebraics
    ADD *f_dds;
};

/** Unsigned integers */
typedef class UnsignedAlgebraicType* UnsignedAlgebraicType_ptr;
class UnsignedAlgebraicType : public Type {
public:
    unsigned width() const
    { return f_width; }

    ADD *dds() const
    { return f_dds; }

protected:
    friend class TypeMgr; // ctors not public
    UnsignedAlgebraicType(TypeMgr& owner); // abstract
    UnsignedAlgebraicType(TypeMgr& owner, unsigned width, ADD *dds = NULL);

    unsigned f_width;

    // this is reserved for temp encodings, it's NULL for ordinary algebraics
    ADD *f_dds;
};

/** Arrays */
typedef class ArrayType* ArrayType_ptr;
class ArrayType : public Type {
public:
    unsigned size() const
    { return f_size; }

    Type_ptr of() const
    { return f_of; }

protected:
    friend class TypeMgr; // ctors not public

    // concrete array type
    ArrayType(TypeMgr& owner, Type_ptr of, unsigned size);

    // abstract array type
    ArrayType(TypeMgr& owner, Type_ptr of);

    Type_ptr f_of;
    unsigned f_size;
};

/** Ranges */
typedef class RangeType* RangeType_ptr;
class RangeType : public Type {
public:
    Type_ptr of() const
    { return f_of; }

protected:
    friend class TypeMgr; // ctors not public
    RangeType(TypeMgr& owner, Type_ptr of);

    Type_ptr f_of;
};

/** Sets */
typedef class SetType* SetType_ptr;
class SetType : public Type {
public:
    Type_ptr of() const
    { return f_of; }

protected:
    friend class TypeMgr; // ctors not public
    SetType(TypeMgr& owner, Type_ptr of);

    Type_ptr f_of;
};

/** Enumeratives */
// TODO: this should be renamed to SetType (merging Sets and Enums)
typedef class EnumType* EnumType_ptr;
class EnumType : public Type {
protected:
    friend class TypeMgr; // ctors not public
    EnumType(TypeMgr& owner, ExprSet& literals);

public:
    const ExprSet& literals() const
    { return f_literals; }

    value_t value(Expr_ptr lit) const
    {
        value_t res = 0;
        for (ExprSet::iterator eye = f_literals.begin();
             eye != f_literals.end(); ++ eye, ++ res) {

            if (*eye == lit)
                return res;
        }

        assert(false); // not found
    }

private:
    ExprSet f_literals;
};

typedef class ResolutionCtxType* ResolutionCtxType_ptr;
class ResolutionCtxType : public Type {
protected:
    friend class TypeMgr; // ctors not public
    ResolutionCtxType(TypeMgr& owner);
};

#endif
