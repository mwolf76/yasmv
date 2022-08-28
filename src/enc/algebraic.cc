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

    static inline value_t pow2(unsigned exp)
    {
        value_t res { 1 };
        if (!exp) {
            return res;
        }

        ++res;

        while (--exp) {
            res <<= 1;
        }

        return res;
    }

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
        unsigned i { 0 }, base { 2 };
        value_t res { 0 };

        do {
            ADD eval { f_dv[i].Eval(assignment) };
            assert(cuddIsConstant(eval.getRegularNode()));

            res += Cudd_V(eval.getNode());

            if (++i < f_width) {
                res *= base;
            } else
                break;
        } while (true);

        if (is_signed()) {
            // REVIEW this for non-exact types
            value_t msb { pow2(i - 1) };
            if (res & msb) {
                value_t cmpl { 1 + (~res & (pow2(i) - 1)) };
                return em.make_neg(em.make_const(cmpl));
            }
        }

        return em.make_const(res);
    }

}; // namespace enc
