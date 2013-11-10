/**
 *  @file enc_mgr.hh
 *  @brief Encoder module (EncMgr class)
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

#ifndef ENCODER_MGR_H
#define ENCODER_MGR_H

#include <common.hh>
#include <expr.hh>
#include <expr_mgr.hh>

#include <type.hh>

#include <cudd_mgr.hh>
#include <cuddInt.h>  /* for cudd_isconstant */

typedef class IEncoding *IEncoding_ptr; // fwd decl

typedef vector<ADD> DDVector; // Deprecated: TODO Rename to ADDVector
typedef vector<int> IndexVector;

struct ADDHash {
    inline long operator() (ADD term) const
    {
        DdNode *tmp = term.getRegularNode();
        return (long) (tmp);
    }
};
struct ADDEq {
    inline bool operator() (const ADD phi,
                            const ADD psi) const
    { return phi == psi; }
};

typedef unordered_map<FQExpr, IEncoding_ptr, FQExprHash, FQExprEq> FQExpr2EncMap;
typedef unordered_map<int, UCBI, IntHash, IntEq> Index2UCBIMap;

typedef class EncodingMgr* EncodingMgr_ptr;
class EncodingMgr  {
    friend class Encoding;

public:
    inline Cudd& dd() const
    { return f_cudd; }

    inline ADD one()
    { return f_cudd.addOne(); }

    inline ADD zero()
    { return f_cudd.addZero(); }

    inline ADD error()
    { return f_cudd.addError(); }

    inline ADD constant(value_t value)
    { assert (error_value != value); return f_cudd.constant(value); }

    inline bool is_constant(ADD x) const
    { return cuddIsConstant(x.getNode()); }

    inline bool is_error(ADD x) const
    { return cuddIsConstant(x.getNode()) && (error_value == Cudd_V(x.getNode())); }

    inline value_t const_value(ADD x) const
    { return Cudd_V(x.getNode()); }

    inline ADD bit()
    { return f_cudd.addVar(); }

    inline unsigned nbits()
    { return f_cudd.ReadSize(); }

    // Makes a new encoding. Used by the compiler
    IEncoding_ptr make_encoding(Type_ptr type);

    // Registers an encoding. Used by the compiler
    void register_encoding(const FQExpr& fqexpr, IEncoding_ptr enc);

    // Retrieves Untimed Canonical Bit Id for index
    inline const UCBI& find_ucbi(int index)
    { return f_index2ucbi_map.at(index); }

    // Retrieves an encoding previously created using
    // make_encoding. User by the SAT model evaluator
    inline IEncoding_ptr find_encoding(const FQExpr& fqexpr)
    {
        FQExpr2EncMap::iterator eye = f_fqexpr2enc_map.find(fqexpr);
        if (eye != f_fqexpr2enc_map.end()) {
            return (*eye).second;
        }

        return NULL;
    }

    inline ExprMgr& em()
    { return f_em; }

    static EncodingMgr& INSTANCE() {
        if (! f_instance) {
            f_instance = new EncodingMgr();
        }
        return (*f_instance);
    }

    inline ADD base() const
    { return f_base; }

    inline ADD msb()
    { return f_msb; }

    inline unsigned bits_per_digit() const
    { return f_bits_per_digit; }

    inline unsigned word_width() const
    { return f_word_width; }

protected:
    EncodingMgr();
    ~EncodingMgr();

private:
    static EncodingMgr_ptr f_instance;

    /* low-level services */

    /* local data */
    Cudd& f_cudd;
    ExprMgr& f_em;

    /* encodings register */
    FQExpr2EncMap f_fqexpr2enc_map;

    /* Untimed Canonical Bit Identifiers register */
    Index2UCBIMap f_index2ucbi_map;

    ADD f_base;  // (eg. 0x10)
    ADD f_msb;   // (eg. 0x8)

    unsigned f_bits_per_digit;
    unsigned f_word_width;
};

#endif
