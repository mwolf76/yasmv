/**
 *  @file type.hh
 *  @brief Type system classes
 *
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT
 *  gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public License
 *  as published by the Free Software Foundation; either version 2.1
 *  of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free
 *  Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
 *  Boston, MA 02110-1301 USA
 *
 *
 *  This module contains definitions and services that implement type
 *  classes. YASMINE's types can be classified as (a) Monolithic types
 *  (i.e. that can be represented using a single DD), (b) Algebraic
 *  types (i.e. that are represented using a vector of DDs) or (c)
 *  Array types. The type system is organized as follows:
 *
 *  MONOLITHIC types
 *  ================
 *  + Booleans
 *  + Enumeratives (e.g. { LOUIE, HUEWEY, DEWEY })

 *  ALGEBRAIC types
 *  ===============
 *  + Signed integers(N) (type keyword is 'signed int' or just 'int'),
 *  where N is the number of hexadecimal digits used in the
 *  representation. MSB is the sign bit. (e.g. an int(4) ranges from
 *  -8 to 7)
 *
 *  + Unsigned integers(N) (type keyword is 'unsigned int'), where N
 *  has the same meaning as above. (e.g. an unsigned int(4) ranges
 *  from 0 to 15.
 *
 * Remark: numeric constants are *always* unsigned and have the
 * special reserved abstract types 'unsigned int(0)'.
 *
 *  ARRAY types
 *  ===============
 *
 *  + ARRAY of booleans
 *  + ARRAY of enumeratives
 *  + ARRAY of signed integers
 *  + ARRAY of unsigned integers
 *
* Type Aliases
 * ============
 *
 * A few type aliases are provided, to bring YASMINE's type system
 * closer to C99's. These type aliases are just synctactig sugar for
 * the type classes defined above, and their usage though recommended
 * is in no way mandatory.
 *
 * INTEGER type aliases:
 * uint4_t,  int4_t
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
 **/
#ifndef TYPE_H
#define TYPE_H

#include <common.hh>
#include <cudd_mgr.hh>

#include <expr.hh>
#include <expr_mgr.hh>

/* _ptr typdefs */
typedef class Type* Type_ptr;

typedef class ScalarType* ScalarType_ptr;

typedef class MonolithicalType* MonolithicalType_ptr;
typedef class BooleanType* BooleanType_ptr;
typedef class EnumType* EnumType_ptr;
typedef class AlgebraicType* AlgebraicType_ptr;
typedef class ConstantType* ConstantType_ptr;
typedef class SignedAlgebraicType* SignedAlgebraicType_ptr;
typedef class UnsignedAlgebraicType* UnsignedAlgebraicType_ptr;

typedef class ArrayType* ArrayType_ptr;

// reserved for resolution
typedef class CtxType* CtxType_ptr;

typedef list<Type_ptr> TypeList;

// ostream helper, uses FQExpr printer (see expr/expr.cc)
ostream& operator<<(ostream& os, Type_ptr type);

// ostream helper, uses FQExpr printer (see expr/expr.cc)
ostream& operator<<(ostream& os, const Type_ptr type);

/** Exception classes */
class TypeException : public Exception {
public:
    virtual const char* what() const throw() =0;
};

/** Raised when the inferrer detects a wrong type */
class BadType : public TypeException {
    Expr_ptr f_repr;

public:
    BadType(Type_ptr tp);

    const char* what() const throw();
    ~BadType() throw();
};

/** Raised when the inferrer detects two mismatching types */
class TypeMismatch : public TypeException {
    Expr_ptr f_repr_a;
    Expr_ptr f_repr_b;

public:
    TypeMismatch(Type_ptr a, Type_ptr b);

    const char* what() const throw();
    ~TypeMismatch() throw();
};

class TypeMgr; // fwd

/** Basic Type class. */
class Type : public Object {
public:
    Expr_ptr repr() const
    { return f_repr; }

    // This depends on Monolithical vs. Algebraic nature of type.
    // (i.e. for Monoliths, size is the number of bits; for algebraics
    // size is the number of ADDs.

    // Bits width
    virtual unsigned width() const =0;

    // shortcuts
    bool is_scalar();
    bool is_monolithical();

    bool is_boolean();
    BooleanType_ptr as_boolean();

    bool is_algebraic();
    AlgebraicType_ptr as_algebraic();

    bool is_constant();
    ConstantType_ptr as_constant();

    bool is_signed_algebraic();
    SignedAlgebraicType_ptr as_signed_algebraic();

    bool is_unsigned_algebraic();
    UnsignedAlgebraicType_ptr as_unsigned_algebraic();

    bool is_enum();
    EnumType_ptr as_enum();

    bool is_array();
    ArrayType_ptr as_array();

    virtual ~Type();

protected:
    Type(TypeMgr &owner)
        : f_owner(owner)
        , f_repr(NULL)
    {}

    TypeMgr& f_owner;
    Expr_ptr f_repr;
};

/** -- Scalars ------------------------------------------------------------ */

/** Abstract type interface. */
class AbstractType {
public:
    virtual bool is_abstract() const =0;
};

/** Scalar type class. */
class ScalarType : public Type {
protected:
    ScalarType(TypeMgr &owner)
        : Type(owner)
    {}
};

/** Monolithical type class. */
class MonolithicalType : public ScalarType {
protected:
    MonolithicalType(TypeMgr &owner)
        : ScalarType(owner)
    {}
};

/** Boolean type */
typedef class BooleanType* BooleanType_ptr;
class BooleanType : public MonolithicalType {
public:
    unsigned width() const;

protected:
    friend class TypeMgr; // ctors not public
    BooleanType(TypeMgr& owner);
};

/** Algebraic type class. */
class AlgebraicType : public ScalarType,
                      public AbstractType {
protected:
    AlgebraicType(TypeMgr &owner)
        : ScalarType(owner)
    {}
};

/** Enumeratives */
typedef class EnumType* EnumType_ptr;
class EnumType : public MonolithicalType, public AbstractType {
protected:
    friend class TypeMgr; // ctors not public
    EnumType(TypeMgr& owner, ExprSet& literals);

public:
    bool is_abstract() const;
    unsigned width() const;

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

/** Integer constants */
typedef class ConstantType* ConstantType_ptr;
class ConstantType : public AlgebraicType {
public:
    unsigned width() const;
    bool is_abstract() const;

    ADD *dds() const
    { return NULL; }

 protected:
    friend class TypeMgr; // ctors not public
    ConstantType(TypeMgr& owner);
};

/** Signed integers */
typedef class SignedAlgebraicType* SignedAlgebraicType_ptr;
class SignedAlgebraicType : public AlgebraicType {
public:
    unsigned width() const;
    bool is_abstract() const;

    ADD *dds() const
    { return f_dds; }

 protected:
    friend class TypeMgr; // ctors not public
    SignedAlgebraicType(TypeMgr& owner, unsigned width, ADD *dds = NULL);

    unsigned f_width;

    // this is reserved for temp encodings, it's NULL for ordinary algebraics
    ADD *f_dds;
};

/** Unsigned integers */
typedef class UnsignedAlgebraicType* UnsignedAlgebraicType_ptr;
class UnsignedAlgebraicType : public AlgebraicType {
public:
    unsigned width() const;
    bool is_abstract() const;

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

/** Signed fixed */
typedef class SignedFxdAlgebraicType* SignedFxdAlgebraicType_ptr;
class SignedFxdAlgebraicType : public AlgebraicType {
public:
    inline unsigned magnitude() const
    { return f_magnitude; }

    inline unsigned fractional() const
    { return f_fractional; }

    unsigned width() const;
    bool is_abstract() const;

    ADD *dds() const
    { return f_dds; }

 protected:
    friend class TypeMgr; // ctors not public
    SignedFxdAlgebraicType(TypeMgr& owner, unsigned magnitude,
                           unsigned fractional, ADD *dds = NULL);

    unsigned f_magnitude;
    unsigned f_fractional;

    // this is reserved for temp encodings, it's NULL for ordinary algebraics
    ADD *f_dds;
};

/** Unsigned integers */
typedef class UnsignedFxdAlgebraicType* UnsignedFxdAlgebraicType_ptr;
class UnsignedFxdAlgebraicType : public AlgebraicType {
public:
    inline unsigned magnitude() const
    { return f_magnitude; }

    inline unsigned fractional() const
    { return f_fractional; }

    unsigned width() const;
    bool is_abstract() const;

    ADD *dds() const
    { return f_dds; }

protected:
    friend class TypeMgr; // ctors not public
    UnsignedFxdAlgebraicType(TypeMgr& owner); // abstract
    UnsignedFxdAlgebraicType(TypeMgr& owner, unsigned magnitude,
                             unsigned fractional, ADD *dds = NULL);

    unsigned f_magnitude;
    unsigned f_fractional;

    // this is reserved for temp encodings, it's NULL for ordinary algebraics
    ADD *f_dds;
};


/** -- Arrays ------------------------------------------------------------ */

/** Array type class. */
typedef class ArrayType* ArrayType_ptr;
class ArrayType : public Type,
                  public AbstractType {
public:
    bool is_abstract() const;
    unsigned width() const;
    unsigned nelems() const
    { return f_nelems; }

    ScalarType_ptr of() const
    { return f_of; }

protected:
    friend class TypeMgr; // ctors not public

    // concrete array type
    ArrayType(TypeMgr& owner, ScalarType_ptr of, unsigned nelems);

    // abstract array type
    ArrayType(TypeMgr& owner, ScalarType_ptr of);

    ScalarType_ptr f_of;
    unsigned f_nelems;
};

// what whas this again?
typedef class ResolutionCtxType* ResolutionCtxType_ptr;
class ResolutionCtxType : public Type {
protected:
    friend class TypeMgr; // ctors not public
    ResolutionCtxType(TypeMgr& owner);
};

#endif
