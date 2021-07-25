/**
 * @file monolithic.cc
 * @brief Encoding management subsystem, algebraic classes implementation.
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

#include <enc.hh>

namespace enc {

// boolean 1(1 bit) var
BooleanEncoding::BooleanEncoding()
    : Encoding()
{
    f_dv.push_back(make_bit());
}

Expr_ptr BooleanEncoding::expr(int *assignment)
{
    ExprMgr& em = f_mgr.em();
    ADD eval = f_dv[0].Eval( assignment );
    assert (cuddIsConstant(eval.getRegularNode()));

    value_t res = Cudd_V(eval.getNode());
    return res == 0 ? em.make_false() : em.make_true();
}

ADD BooleanEncoding::bit()
{
    assert( 1 == f_dv.size() );
    return f_dv[0];
}

MonolithicEncoding::MonolithicEncoding()
    : Encoding()
{}

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

EnumEncoding::EnumEncoding(const ExprSet& lits)
{
    unsigned nbits = range_repr_bits(lits.size());
    f_dv.push_back( make_monolithic_encoding(nbits));

    value_t v;
    ExprSet::iterator eye;
    for (v = 0, eye = lits.begin(); eye != lits.end(); ++ eye, ++ v) {

        f_v2e_map[v] = *eye;
        f_e2v_map[*eye] = v;
    }
}

value_t EnumEncoding::value(Expr_ptr lit)
{
    ExprValueMap::iterator eye = f_e2v_map.find( lit );
    assert( eye != f_e2v_map.end());

    return (*eye).second;
}

Expr_ptr EnumEncoding::expr(int *assignment)
{
    ADD eval = f_dv[0].Eval(assignment);
    assert (cuddIsConstant(eval.getNode()));

    value_t lindex = Cudd_V(eval.getNode());

    return f_v2e_map [lindex];
}

};
