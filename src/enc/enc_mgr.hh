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
typedef unordered_map<ADD, IEncoding_ptr, ADDHash, ADDEq> ADD2EncMap;

typedef vector<ADD> EncodingBits;

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

    inline ADD constant(value_t value)
    { return f_cudd.constant(value); }

    inline bool is_constant(ADD x) const
    { return cuddIsConstant(x.getNode()); }

    inline value_t const_value(ADD x) const
    { return Cudd_V(x.getNode()); }

    inline ADD bit()
    { return f_cudd.addVar(); }

    // used by the compiler
    IEncoding_ptr make_encoding(Type_ptr type);

    // user by the SAT model evaluator
    IEncoding_ptr find_encoding(ADD add);

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

    inline ADD full() const
    { return f_full; }

    inline ADD msb()
    { return f_msb; }

protected:
    EncodingMgr();
    ~EncodingMgr();

private:
    static EncodingMgr_ptr f_instance;

    /* low-level services */

    /* local data */
    Cudd& f_cudd;
    ExprMgr& f_em;

    /* low-level services */
    FQExpr2EncMap f_fqexpr2enc_map;
    ADD2EncMap f_add2enc_map;

    inline void register_encoding(const FQExpr fqexpr, IEncoding_ptr encoding)
    {
        assert(! f_fqexpr2enc_map [ fqexpr ] );
        f_fqexpr2enc_map [ fqexpr ] = encoding;
    }

    ADD f_base;  // 0x10
    ADD f_width; // 8
    ADD f_full;  // 0xF
    ADD f_msb;   // 0x8
};

#endif
