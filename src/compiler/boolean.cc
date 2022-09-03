/**
 * @file boolean.cc
 * @brief Expression compiler subsystem, boolean operators implementations.
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
#include <common/common.hh>

#include <compiler.hh>
#include <expr.hh>

namespace compiler {

    void Compiler::boolean_not(const expr::Expr_ptr expr)
    {
        POP_DD(lhs);
        PUSH_DD(lhs.Cmpl());
    }

    void Compiler::boolean_and(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_DD(rhs);
        POP_DD(lhs);
        PUSH_DD(lhs.Times(rhs)); /* 0, 1 logic uses arithmetic product for AND */
    }

    void Compiler::boolean_or(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_DD(rhs);
        POP_DD(lhs);
        PUSH_DD(lhs.Or(rhs));
    }

    void Compiler::boolean_xor(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_DD(rhs);
        POP_DD(lhs);
        PUSH_DD(lhs.Xor(rhs));
    }

    void Compiler::boolean_implies(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_DD(rhs);
        POP_DD(lhs);
        PUSH_DD(lhs.Cmpl().Or(rhs));
    }

    void Compiler::boolean_iff(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_DD(rhs);
        POP_DD(lhs);
        PUSH_DD(lhs.Xnor(rhs));
    }

    // implemented as xnor (logical equivalence)
    void Compiler::boolean_equals(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_DD(rhs);
        POP_DD(lhs);
        PUSH_DD(lhs.Xnor(rhs));
    }

    // implemented as negation of the former (i.e xor)
    void Compiler::boolean_not_equals(const expr::Expr_ptr expr)
    {
        DROP_TYPE();

        POP_DD(rhs);
        POP_DD(lhs);
        PUSH_DD(lhs.Xor(rhs));
    }

    void Compiler::boolean_ite(const expr::Expr_ptr expr)
    {
        DROP_TYPE();
        DROP_TYPE();

        POP_DD(rhs);
        POP_DD(lhs);
        POP_DD(cnd);

        PUSH_DD(cnd.Ite(lhs, rhs));
    }

    void Compiler::boolean_subscript(const expr::Expr_ptr expr)
    {
        enc::EncodingMgr& bm { f_enc };

        // index
        POP_TYPE(t0);
        assert(t0->is_algebraic());

        type::Type_ptr itype { t0->as_algebraic() };
        unsigned iwidth { itype->width() };

        POP_DV(index, iwidth);
        assert(iwidth == bm.word_width()); // needed?

        // array
        POP_TYPE(t1);
        assert(t1->is_array());

        type::ArrayType_ptr atype { t1->as_array() };
        type::ScalarType_ptr type { atype->of() };
        assert(type->is_boolean());

        unsigned elem_width { type->width() };
        assert(elem_width == 1);

        unsigned elem_count { atype->nelems() };
        POP_DV(lhs, elem_width * elem_count);

        PUSH_TYPE(type);

        if (t0->is_constant()) {
            unsigned subscript { 0 };
            for (unsigned i = 0; i < iwidth; ++i) {
                ADD bit { index[i] };
                subscript *= 2;
                if (bit.IsOne()) {
                    subscript++;
                }
            }

            PUSH_DD(lhs[subscript]);
        } else {
            /* Build selection DDs */
            dd::DDVector cnd_dds;
            dd::DDVector act_dds;
            unsigned j_, j { 0 };
            do {

                unsigned i;
                ADD cnd(bm.one());

                i = 0;
                j_ = j;
                while (i < iwidth) {
                    ADD bit { (j_ & 1) ? bm.one() : bm.zero() };
                    unsigned ndx { iwidth - i - 1 };
                    j_ >>= 1;

                    cnd *= index[ndx].Xnor(bit);
                    ++i;
                }

                cnd_dds.push_back(cnd);
                act_dds.push_back(make_auto_dd());
            } while (++j < elem_count);

            /* Push MUX output DD vector */
            FRESH_DV(dv, elem_width);
            PUSH_DV(dv, elem_width);

            MultiwaySelectionDescriptor msd {
                elem_width, elem_count, dv, cnd_dds, act_dds, lhs
            };
            f_multiway_selection_descriptors.push_back(msd);
        }
    }

} // namespace compiler
