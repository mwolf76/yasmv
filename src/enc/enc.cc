/**
 *  @file enc.cc
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
#include <cmath>
#include <enc.hh>

// Constants
ConstEncoding::ConstEncoding(value_t value)
    : Encoding()
{
    unsigned i, base = f_mgr.base();

    for (i = f_mgr.width(); (i); -- i) {
        ADD digit = f_mgr.constant(value % base);
        f_dv.push_back(digit);
        value /= base;
    }

    assert (value == 0); // not overflowing
}

// boolean 1(1 bit) var
BooleanEncoding::BooleanEncoding()
    : Encoding()
{
    // single bit encoding
    f_dv.push_back(f_mgr.dd().addVar());
}

// bounded integer var
RangeEncoding::RangeEncoding(value_t min, value_t max)
    : f_min(min)
    , f_max(max)
{
    unsigned nbits = range_repr_bits(f_max - f_min);

    make_monolithic_encoding(nbits);
}

Expr_ptr RangeEncoding::expr(ADD leaf)
{
    ExprMgr& em = f_mgr.em();

    value_t res = Cudd_V(leaf.getNode()) + f_min;
    assert (f_min <= res && res <= f_max);

    return em.make_iconst(res);
}

ADD RangeEncoding::leaf(Expr_ptr expr)
{
    ExprMgr& em = f_mgr.em();

    assert(em.is_numeric(expr));
    return f_mgr.constant(expr->value() - f_min);
}

EnumEncoding::EnumEncoding(const ExprSet& lits)
{
    unsigned nbits = range_repr_bits(lits.size());

    make_monolithic_encoding(nbits);

    value_t v;
    ExprSet::iterator eye;
    for (v = 0, eye= lits.begin(); eye != lits.end(); ++ eye, ++ v) {

        f_v2e_map[v] = *eye;
        f_e2v_map[*eye] = v;
    }
}

Expr_ptr EnumEncoding::expr(ADD leaf)
{
    value_t lindex = Cudd_V(leaf.getNode());
    return f_v2e_map [lindex];
}

ADD EnumEncoding::leaf(Expr_ptr expr)
{
    ExprMgr& em = f_mgr.em();
    assert(em.is_identifier(expr));

    return f_mgr.constant(f_e2v_map[expr]);
}

unsigned MonolithicEncoding::range_repr_bits (value_t range)
{
    return ceil(log2(range));
}

ADD MonolithicEncoding::make_monolithic_encoding(unsigned nbits)
{
    ADD res = f_mgr.bit();
    ADD two = f_mgr.constant(2);

    assert(0 < nbits);
    unsigned i = 1;

    while (i < nbits) {
        res *= two;
        res += f_mgr.bit();

        ++ i;
    }

    return res;
}

// dctor
Encoding::~Encoding()
{ }
