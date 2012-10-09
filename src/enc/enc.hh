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
#include <expr.hh>
#include <expr_mgr.hh>

#include <type.hh>

#include <cudd_mgr.hh>
#include <enc_mgr.hh>

// -- primary decls  --------------------------------------------------------------
typedef vector<ADD> DDVector;

typedef class IEncoding *IEncoding_ptr;
class IEncoding : public IObject {
public:
    virtual DDVector& dv() =0;
};

class Encoding : public IEncoding {
public:
    DDVector& dv()
    { return f_dv; }

protected:
    Encoding()
        : f_mgr(EncodingMgr::INSTANCE())
    {}

    virtual ~Encoding() =0;

    EncodingMgr& f_mgr;
    DDVector f_dv; // digit vector

    ADD make_integer_encoding(unsigned nbits);
};

// for constants promotion as algebraic entities
class ConstEncoding : public Encoding {
friend class EncodingMgr; // expose ctors only to mgr
protected:
    virtual ~ConstEncoding()
    { assert(0); }

    // Const value, width is provided by EncMgr
    ConstEncoding(value_t value);
};

// 1-bit boolean var (identity encoding)
class BooleanEncoding : public Encoding {
friend class EncodingMgr; // expose ctors only to mgr
protected:
    virtual ~BooleanEncoding()
    { assert(0); }

    // boolean 1(1 bit) var
    BooleanEncoding();
};

class AlgebraicEncoding : public Encoding {
friend class EncodingMgr; // expose ctors only to mgr
public:

protected:
    virtual ~AlgebraicEncoding()
    { assert(0); }

    AlgebraicEncoding(unsigned width, bool is_signed);

    ADD make_algebraic_encoding();
};

// base class for finite int based
class MonolithicEncoding : public Encoding {
public:
    virtual Expr_ptr expr(ADD leaf) =0;
    virtual ADD leaf(Expr_ptr expr) =0;

protected:
    ADD make_monolithic_encoding(unsigned nbits);
    unsigned range_repr_bits (value_t range);
};

class RangeEncoding : public MonolithicEncoding {
friend class EncodingMgr; // expose ctors only to mgr
public:
    virtual Expr_ptr expr(ADD leaf);
    virtual ADD leaf(Expr_ptr expr);

protected:
    virtual ~RangeEncoding()
    { assert(0); }

    RangeEncoding(value_t min_value, value_t max_value);

    value_t f_min;
    value_t f_max;
};

typedef unordered_map<value_t, Expr_ptr, ValueHash, ValueEq> ValueExprMap;
typedef pair<ValueExprMap::iterator, bool> ValueExprMapHit;

typedef unordered_map<Expr_ptr, value_t, PtrHash, PtrEq> ExprValueMap;
typedef pair<ExprValueMap::iterator, bool> ExprValueMapHit;


class EnumEncoding : public MonolithicEncoding {
friend class EncodingMgr; // expose ctors only to mgr
public:
    virtual Expr_ptr expr(ADD leaf);
    virtual ADD leaf(Expr_ptr expr);

protected:
    virtual ~EnumEncoding()
    { assert(0); }

    EnumEncoding(const ExprSet& lits);

    ValueExprMap f_v2e_map;
    ExprValueMap f_e2v_map;
};

#endif
