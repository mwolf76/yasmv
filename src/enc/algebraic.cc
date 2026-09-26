/**
 * @file algebraic.cc
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

    AlgebraicEncoding::AlgebraicEncoding(unsigned width, bool is_signed, ADD* dds)
        : f_width(width)
        , f_signed(is_signed)
        , f_temporary(NULL != dds)
    {
        if (f_temporary) {
            assert(NULL != dds); // obvious
            for (unsigned i = 0; i < width; ++i) {
                f_dv.push_back(dds[i]);
            }
        } else {
            for (unsigned i = 0; i < width; ++i) {
                f_dv.push_back(make_monolithic_encoding(1));
            }
        }
    }

    expr::Expr_ptr AlgebraicEncoding::expr(int* assignment)
    {
        expr::ExprMgr& em { f_mgr.em() };
        uint64_t bits = 0;
        for (unsigned i = 0; i < f_width; ++i) {
            ADD eval { f_dv[i].Eval(assignment) };
            assert(cuddIsConstant(eval.getRegularNode()));
            bits = (bits << 1) | (Cudd_V(eval.getNode()) != 0);
        }
        if (is_signed() && f_width < 64 && (bits & (uint64_t(1) << (f_width - 1))))
            bits |= ~((uint64_t(1) << f_width) - 1);
        value_t res = static_cast<value_t>(bits);

        return em.make_const(res);
    }

}; // namespace enc
