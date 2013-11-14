/**
 *  @file enc.hh
 *  @brief Encoder module
 *
 *  This module contains definitions and services that implement an
 *  encoder for symbols. For each symbol a boolean encoding is
 *  maintained, the encoder takes care of ADD variables definitions
 *  and is provides mapback services as well.
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

#ifndef ENCODER_H
#define ENCODER_H

#include <common.hh>
#include <opts.hh>

#include <expr.hh>
#include <expr_mgr.hh>

#include <type.hh>

#include <cudd_mgr.hh>
#include <enc_mgr.hh>

// -- primary decls  --------------------------------------------------------------
typedef class IEncoding *IEncoding_ptr;
class IEncoding : public IObject {
public:
    /* Full-Digit DDs (roots), used in manipulation of algebraics (e.g.. compiler) */
    virtual DDVector& dv() =0;

    /* Bit-level DDs (leaves), used in bitlevel operations (e.g. SAT solver) */
    virtual DDVector& bits() =0;

    // vector of DD leaves (consts) -> expr
    virtual Expr_ptr expr(int* assignment) =0;
};

class Encoding : public IEncoding {
public:
    DDVector& dv()
    { return f_dv; }

    DDVector& bits()
    { return f_bits; }

protected:
    Encoding()
        : f_mgr(EncodingMgr::INSTANCE())
    {}

    virtual ~Encoding() =0;

    EncodingMgr& f_mgr;

    DDVector f_dv; // digit vector
    DDVector f_bits; // all bits

    // low level services
    ADD make_bit();
    ADD make_monolithic_encoding(unsigned nbits);
};

// 1-bit boolean var (identity encoding)
typedef class BooleanEncoding* BooleanEncoding_ptr;
class BooleanEncoding : public Encoding {
friend class EncodingMgr; // expose ctors only to mgr
public:
    // here assignment *must* have size 1
    Expr_ptr expr(int* assignment);

    ADD bit();

protected:
    virtual ~BooleanEncoding()
    { assert(0); }

    // boolean 1(1 bit) var
    BooleanEncoding();
};

typedef class AlgebraicEncoding* AlgebraicEncoding_ptr;
class AlgebraicEncoding : public Encoding {
friend class EncodingMgr; // expose ctors only to mgr
friend class Compiler;  // for temporaries
public:
    // here assignment *must* have size 1
    virtual Expr_ptr expr(int* assignment);

    inline bool is_signed() const
    { return f_signed; }

    inline bool is_temporary() const
    { return f_temporary; }

    inline unsigned width() const
    { return f_width; }

    // custom iterator
    DDVector::const_iterator bits_begin(unsigned k);
    DDVector::const_iterator bits_end(unsigned k);

protected:
    virtual ~AlgebraicEncoding()
    { assert(0); }

    // width is number of *digits* here, dds is reserved for temporary encodings
    AlgebraicEncoding(unsigned width, unsigned fract, bool is_signed, ADD *dds = NULL);

    unsigned f_width;
    unsigned f_fract; // non-zero for fixed encodings
    bool f_signed;
    bool f_temporary;
};


// base class for finite int based
typedef class MonolithicEncoding* MonolithicEncoding_ptr;
class MonolithicEncoding : public Encoding {
protected:
    virtual ~MonolithicEncoding()
    { assert(0); }

    MonolithicEncoding();

    unsigned range_repr_bits (value_t range);
};

typedef unordered_map<value_t, Expr_ptr, ValueHash, ValueEq> ValueExprMap;
typedef pair<ValueExprMap::iterator, bool> ValueExprMapHit;

typedef unordered_map<Expr_ptr, value_t, PtrHash, PtrEq> ExprValueMap;
typedef pair<ExprValueMap::iterator, bool> ExprValueMapHit;

typedef class EnumEncoding* EnumEncoding_ptr;
class EnumEncoding : public MonolithicEncoding {
friend class EncodingMgr; // expose ctors only to mgr
public:
    // here assignment *must* have size 1
    virtual Expr_ptr expr(int* assignment);

    virtual value_t value(Expr_ptr literal);

protected:
    virtual ~EnumEncoding()
    { assert(0); }

    EnumEncoding(const ExprSet& lits);

    ValueExprMap f_v2e_map;
    ExprValueMap f_e2v_map;
};

typedef vector<IEncoding_ptr> Encodings;
typedef class ArrayEncoding* ArrayEncoding_ptr;
class ArrayEncoding : public Encoding {
friend class EncodingMgr; // expose ctors only to mgr
public:
    // here assignment *must* have size 1
    virtual Expr_ptr expr(int* assignment);

protected:
    ArrayEncoding(Encodings elements);

    virtual ~ArrayEncoding()
    { assert(0); }

    Encodings f_elements;
};

#endif
