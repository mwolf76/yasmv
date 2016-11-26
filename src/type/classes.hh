/**
 * @file type/classes.hh
 * @brief Type system module header file, type system classes.
 *
 * This header file contains the declarations and type definitions
 * required by YASMINE type system classes.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#ifndef TYPE_CLASSES_H
#define TYPE_CLASSES_H

#include <list>

#include <dd/cudd_mgr.hh>

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

/*
 * YASMINE's types can be classified as (a) Monolithic types
 * (i.e. that can be represented using a single DD), (b) Algebraic
 * types (i.e. that are represented using a vector of DDs) or (c)
 * Array types. The type system is organized as follows:
 *
 * MONOLITHIC types
 * ================
 * + Booleans
 * + Enumeratives (e.g. { LOUIE, HUEWEY, DEWEY })

 * ALGEBRAIC types
 * ===============
 *
 * + Signed integers(N) (type keyword is 'signed int' or just 'int'),
 * where N is the number of hexadecimal digits used in the
 * representation. MSB is the sign bit. (e.g. an int(4) ranges from -8
 * to 7)
 *
 * + Unsigned integers(N) (type keyword is 'unsigned int'), where N
 * has the same meaning as above. (e.g. an unsigned int(4) ranges from
 * 0 to 15.
 *
 * Remark: numeric constants are *always* unsigned and have the
 * special reserved abstract types 'unsigned int(0)'.
 *
 * ARRAY types
 * ===============
 *
 * + ARRAY of booleans
 * + ARRAY of enumeratives
 * + ARRAY of signed integers
 * + ARRAY of unsigned integers
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
 * 1. When one of the two operands is signed the other one is also
 * converted to signed;
 *
 * 2. The size of the result fits the largest size of the involved
 * operands.
 *
 **/

#include <type/typedefs.hh>
#include <type/type_mgr.hh>

/** Basic Type class. */
class Type {
public:
    Expr_ptr repr() const
    { return f_repr; }

    /* This depends on the Monolithic vs. Algebraic nature of type.
    (i.e. for Monolithics, size is 1; for algebraics size is the
    number of ADDs). */

    // Bits width
    virtual unsigned width() const =0;

    // shortcuts
    bool is_scalar();
    ScalarType_ptr as_scalar();

    bool is_monolithic();

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

    bool is_instance();
    InstanceType_ptr as_instance();

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

/** Scalar type class. */
class ScalarType : public Type {
protected:
    ScalarType(TypeMgr &owner)
        : Type(owner)
    {}
};

/** Monolithic type class. */
class MonolithicType : public ScalarType {
protected:
    MonolithicType(TypeMgr &owner)
        : ScalarType(owner)
    {}
};

/** Boolean type */
typedef class BooleanType* BooleanType_ptr;
class BooleanType : public MonolithicType {
public:
    unsigned width() const;

protected:
    friend class TypeMgr; // ctors not public
    BooleanType(TypeMgr& owner);
};

/** Algebraic type class. */
class AlgebraicType : public ScalarType {
public:

protected:
    AlgebraicType(TypeMgr &owner)
        : ScalarType(owner)
    {}
};

/** Enumeratives */
typedef class EnumType* EnumType_ptr;
class EnumType : public MonolithicType {
protected:
    friend class TypeMgr; // ctors not public
    EnumType(TypeMgr& owner, ExprSet& literals);

public:
    unsigned width() const;

    inline const ExprSet& literals() const
    { return f_literals; }

    value_t value(Expr_ptr lit) const;

private:
    ExprSet f_literals;
};

/** Instances */
typedef class InstanceType* InstanceType_ptr;
class InstanceType : public ScalarType {
public:
    unsigned width() const;;
    InstanceType(TypeMgr& owner, Expr_ptr name, Expr_ptr params);

    inline Expr_ptr name() const
    { return f_name; }

    inline Expr_ptr params() const
    { return f_params; }

private:
    Expr_ptr f_name;
    Expr_ptr f_params;
};

/** Numeric constants (both integers and fixed) */
typedef class ConstantType* ConstantType_ptr;
class ConstantType : public AlgebraicType {
public:
    unsigned width() const;

    ADD *dds() const
    { return NULL; }

 protected:
    friend class TypeMgr; // ctors not public
    ConstantType(TypeMgr& owner, unsigned width);

    unsigned f_width;
};

/** Signed algebraics (both integers and fixed) */
typedef class SignedAlgebraicType* SignedAlgebraicType_ptr;
class SignedAlgebraicType : public AlgebraicType {
public:
    unsigned width() const;

    ADD *dds() const
    { return f_dds; }

 protected:
    friend class TypeMgr; // ctors not public
    SignedAlgebraicType(TypeMgr& owner, unsigned width, ADD *dds = NULL);

    unsigned f_width;

    // this is reserved for temp encodings, it's NULL for ordinary algebraics
    ADD *f_dds;
};

/** Unsigned algebraics (both integers and fixed) */
typedef class UnsignedAlgebraicType* UnsignedAlgebraicType_ptr;
class UnsignedAlgebraicType : public AlgebraicType {
public:
    unsigned width() const;

    ADD *dds() const
    { return f_dds; }

protected:
    friend class TypeMgr; // ctors not public
    UnsignedAlgebraicType(TypeMgr& owner, unsigned width, ADD *dds = NULL);

    unsigned f_width;

    // this is reserved for temp encodings, it's NULL for ordinary algebraics
    ADD *f_dds;
};

/** -- Arrays ------------------------------------------------------------ */

/** Array type class. */
typedef class ArrayType* ArrayType_ptr;
class ArrayType : public Type {
public:
    unsigned width() const;
    unsigned nelems() const
    { return f_nelems; }

    ScalarType_ptr of() const
    { return f_of; }

protected:
    friend class TypeMgr; // ctors not public

    // array type
    ArrayType(TypeMgr& owner, ScalarType_ptr of, unsigned nelems);

    ScalarType_ptr f_of;
    unsigned f_nelems;
};

/** -- shortcurts to simplify the manipulation of the internal Type stack -- */
#define TOP_TYPE(tp)                            \
    const Type_ptr (tp)(f_type_stack.back())

#define DROP_TYPE()                             \
    f_type_stack.pop_back()

#define POP_TYPE(tp)                            \
    TOP_TYPE(tp); DROP_TYPE()

#define PUSH_TYPE(tp)                           \
    f_type_stack.push_back(tp)

typedef std::vector<Type_ptr> TypeVector;

#endif /* TYPE_CLASSES_H */
