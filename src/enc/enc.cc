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
#include <enc.hh>

// boolean 1(1 bit) var
BooleanEncoding::BooleanEncoding()
    : Encoding()
{
    // single bit encoding
    f_dv.push_back(f_mgr.dd().addVar());
}

Expr_ptr BooleanEncoding::expr(DDVector& assignment)
{
    assert(0);
}

MonolithicEncoding::MonolithicEncoding()
    : Encoding()
{}

// base service, has to be in superclass for visibility
ADD Encoding::make_monolithic_encoding(unsigned nbits)
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

// algebraic encoding uses monolithic as a builing block
AlgebraicEncoding::AlgebraicEncoding(unsigned width, bool is_signed)
    : f_width(width)
    , f_signed(is_signed)
{
    unsigned i;
    const unsigned NIBBLE_SIZE = 4; // hexadecimal digit (hard-coded)

    for (i = 0; i < f_width; ++ i) {
        f_dv.push_back(make_monolithic_encoding(NIBBLE_SIZE));
    }
}

TempEncoding::TempEncoding(ADD *dds, unsigned width)
    : f_width(width)
    , f_signed(false)
{
  for (i = 0; i < f_width; ++ i) {
      f_dv.push_back(dds[i]);
  }
}


Expr_ptr AlgebraicEncoding::expr(DDVector& assignment)
{
    ExprMgr& em = f_mgr.em();
    unsigned i;

    value_t res = 0;
    assert (assignment.size() == f_width);

    i = 0; do {
        ADD digit = assignment[i];
        ADD eval = f_dv[i].Times(assignment[i]);

        assert (cuddIsConstant(eval.getNode()));
        res += Cudd_V(eval.getNode());

        if (++ i < f_width) {
            res *= 0x10; // bleah!
        } else break;
    } while (true);

    return em.make_iconst(res);
}

// // bounded integer var
// RangeEncoding::RangeEncoding(value_t min, value_t max)
//     : f_min(min)
//     , f_max(max)
// {
//     unsigned nbits = range_repr_bits(f_max - f_min);
//     make_monolithic_encoding(nbits);
// }

// Expr_ptr RangeEncoding::expr(DDVector& assignment)
// {
//     ExprMgr& em = f_mgr.em();
//     assert (assignment.size() == 1);

//     ADD leaf = assignment[0];
//     ADD eval = f_dv[0].Times(leaf);
//     assert (cuddIsConstant(eval.getNode()));

//     value_t res = Cudd_V(eval.getNode()) + f_min;
//     assert (f_min <= res && res <= f_max);

//     return em.make_iconst(res);
// }

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

Expr_ptr EnumEncoding::expr(DDVector& assignment)
{
    assert (assignment.size() == 1);

    ADD leaf = assignment[0];
    ADD eval = f_dv[0].Times(leaf);
    assert (cuddIsConstant(eval.getNode()));

    value_t lindex = Cudd_V(eval.getNode());
    return f_v2e_map [lindex];
}

unsigned MonolithicEncoding::range_repr_bits (value_t range)
{
    unsigned res = 0;
    assert(0 < range);
    while (range) {
        ++ res;
        range /= 2;
    }

    return res;
}

// dctor
Encoding::~Encoding()
{ }
