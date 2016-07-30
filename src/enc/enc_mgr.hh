/**
 * @file enc_mgr.hh
 * @brief Encoder module (EncMgr class)
 *
 * This header file contains the declarations required by the Encoding
 * Manager class.
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

#ifndef ENCODING_MGR_H
#define ENCODING_MGR_H

#include <vector>

#include <boost/unordered_map.hpp>

#include <common.hh>

#include <expr/expr.hh>
#include <expr/timed_expr.hh>
#include <expr/expr_mgr.hh>

#include <type/type.hh>

#include <dd/cudd_mgr.hh>
#include <dd/cudd-2.5.0/cudd/cuddInt.h>  /* for cudd_isconstant */

#include <enc/ucbi.hh>
#include <utils/pool.hh>

typedef class Encoding *Encoding_ptr; // fwd decl

typedef std::vector<int> IndexVector;

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

typedef boost::unordered_map<TimedExpr, Encoding_ptr, TimedExprHash, TimedExprEq> TimedExpr2EncMap;
typedef boost::unordered_map<int, UCBI, IntHash, IntEq> Index2UCBIMap;

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
    Encoding_ptr make_encoding(Type_ptr type);

    // Registers an encoding. Used by the compiler
    void register_encoding(const TimedExpr& key, Encoding_ptr enc);

    // Retrieves Untimed Canonical Bit Id for index
    inline const UCBI& find_ucbi(int index)
    { return f_index2ucbi_map.at(index); }

    // Retrieves an encoding previously created using
    // make_encoding. User by the SAT model evaluator
    Encoding_ptr find_encoding(const TimedExpr& key);

    inline ExprMgr& em()
    { return f_em; }

    static EncodingMgr& INSTANCE() {
        if (! f_instance) {
            f_instance = new EncodingMgr();
        }
        return (*f_instance);
    }

    inline unsigned word_width() const
    { return f_word_width; }

protected:
    EncodingMgr();
    ~EncodingMgr();

private:
    static EncodingMgr_ptr f_instance;

    Cudd& f_cudd;
    ExprMgr& f_em;

    /* encodings register */
    TimedExpr2EncMap f_timed_expr2enc_map;

    /* Untimed Canonical Bit Identifiers register */
    Index2UCBIMap f_index2ucbi_map;

    unsigned f_word_width;
};

#endif /* ENCODING_MGR_H */
