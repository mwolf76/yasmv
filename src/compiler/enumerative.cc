/**
 *  @file enumerative.cc
 *  @brief Boolean compiler - enumerative manipulations
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
#include <common/common.hh>

#include <compiler.hh>
#include <expr.hh>

namespace compiler {

    void Compiler::enumerative_equals(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { type::TypeMgr::INSTANCE() };

        DROP_TYPE();
        DROP_TYPE();
        PUSH_TYPE(tm.find_boolean());

        POP_DD(rhs);
        POP_DD(lhs);
        PUSH_DD(lhs.Equals(rhs));
    }

    void Compiler::enumerative_not_equals(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { type::TypeMgr::INSTANCE() };

        DROP_TYPE();
        DROP_TYPE();
        PUSH_TYPE(tm.find_boolean());

        POP_DD(rhs);
        POP_DD(lhs);
        PUSH_DD(lhs.Equals(rhs).Cmpl());
    }

    void Compiler::enumerative_ite(const expr::Expr_ptr expr)
    {
        POP_TYPE(rhs_type);
        DROP_TYPE();
        DROP_TYPE();
        PUSH_TYPE(rhs_type);

        POP_DD(rhs);
        POP_DD(lhs);
        POP_DD(cnd);
        PUSH_DD(cnd.Ite(lhs, rhs));
    }

    void Compiler::enumerative_subscript(const expr::Expr_ptr expr)
    {
        auto& bm(f_enc);

        POP_TYPE(t0);
        assert(t0->is_algebraic());

        const auto itype { t0->as_algebraic() };
        const auto iwidth { itype->width() };

        POP_TYPE(t1);
        assert(t1->is_array());

        const auto atype { t1->as_array() };
        const auto type { atype->of() };
        assert(type->is_enum());

        PUSH_TYPE(type);

        POP_DV(index, iwidth);
        // assert(iwidth == bm.word_width());

        const auto elem_width { type->width() };
        assert(elem_width == 1);

        const auto elem_count { atype->nelems() };
        POP_DV(lhs, elem_width * elem_count);

        if (t0->is_constant()) {
            unsigned subscript { 0 };
            for (unsigned i = 0; i < iwidth; ++i) {
                ADD bit { index[i] };
                subscript *= 2;
                if (bit.IsOne()) {
                    subscript++;
                }
            }

            for (unsigned i = 0; i < elem_width; ++i) {
                PUSH_DD(lhs[elem_width * subscript + elem_width - i - 1]);
            }
        }

        else {
            /* Build selection DDs */
            dd::DDVector cnd_dds;
            dd::DDVector act_dds;
            unsigned j_, j { 0 };
            do {
                unsigned i;
                ADD cnd { bm.one() };

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
