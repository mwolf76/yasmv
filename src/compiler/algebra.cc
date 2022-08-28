/**
 * @file algebra.cc
 * @brief Expression compiler subsystem, algebraic operators implementations.
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

    /**
     * Operand arguments (which are DD vectors) are fetched from the
     * internal DD stack MSB first. On the other hand, to ensure
     * proper behavior the result of any such operation has to be
     * pushed in reversed order. This is taken care of by the POP_DV
     * and PUSH_DV macros. The main methods of this class
     * (algebraic_unary, algebraic_binary, algebraic_relational,
     * algebraic_ternary) all follow a similar structure: (1) verify
     * type information and populate the type stack with the result
     * type, (2) pull the operands DVs and push the result DV (3)
     * populate and register an operator descriptor.
     */

    // unary ops -------------------------------------------------------------------
    void Compiler::algebraic_unary(const expr::Expr_ptr expr)
    {
        assert(is_unary_algebraic(expr));

        TOP_TYPE(lhs_type);
        assert(lhs_type->is_algebraic());
        const type::AlgebraicType_ptr algebraic_type { lhs_type->as_algebraic() };

        unsigned width { algebraic_type->width() };
        bool signedness { algebraic_type->is_signed_algebraic() };

        /* no op on the type stack required */

        POP_DV(lhs, width);

        FRESH_DV(res, width);
        PUSH_DV(res, width);

        InlinedOperatorDescriptor iod {
            make_ios(signedness, expr->symb(), width), res, lhs
        };
        f_inlined_operator_descriptors.push_back(iod);
    }

    void Compiler::algebraic_neg(const expr::Expr_ptr expr)
    {
        algebraic_unary(expr);
    }

    void Compiler::algebraic_bw_not(const expr::Expr_ptr expr)
    {
        algebraic_unary(expr);
    }

    // -- binary ops ---------------------------------------------------------------
    void Compiler::algebraic_binary(const expr::Expr_ptr expr)
    {
        assert(is_binary_algebraic(expr));

        POP_TYPE(rhs_type);
        TOP_TYPE(lhs_type);

        assert(rhs_type->is_algebraic() &&
               lhs_type->is_algebraic() &&
               lhs_type->width() == rhs_type->width());

        unsigned width { rhs_type->width() };
        bool signedness {
            lhs_type->is_signed_algebraic() ||
            rhs_type->is_signed_algebraic()
        };

        /* no op on the type stack required */

        POP_DV(rhs, width);
        POP_DV(lhs, width);

        FRESH_DV(res, width);
        PUSH_DV(res, width);

        InlinedOperatorDescriptor md {
            make_ios(signedness, expr->symb(), width), res, lhs, rhs
        };
        f_inlined_operator_descriptors.push_back(md);
    }

    void Compiler::algebraic_plus(const expr::Expr_ptr expr)
    {
        algebraic_binary(expr);
    }

    void Compiler::algebraic_sub(const expr::Expr_ptr expr)
    {
        algebraic_binary(expr);
    }

    void Compiler::algebraic_mul(const expr::Expr_ptr expr)
    {
        algebraic_binary(expr);
    }

    void Compiler::algebraic_div(const expr::Expr_ptr expr)
    {
        algebraic_binary(expr);
    }

    void Compiler::algebraic_mod(const expr::Expr_ptr expr)
    {
        algebraic_binary(expr);
    }

    void Compiler::algebraic_bw_and(const expr::Expr_ptr expr)
    {
        algebraic_binary(expr);
    }

    void Compiler::algebraic_bw_or(const expr::Expr_ptr expr)
    {
        algebraic_binary(expr);
    }

    void Compiler::algebraic_bw_xor(const expr::Expr_ptr expr)
    {
        algebraic_binary(expr);
    }

    void Compiler::algebraic_bw_xnor(const expr::Expr_ptr expr)
    {
        algebraic_binary(expr);
    }

    void Compiler::algebraic_lshift(const expr::Expr_ptr expr)
    {
        algebraic_binary(expr);
    }

    void Compiler::algebraic_rshift(const expr::Expr_ptr expr)
    {
        algebraic_binary(expr);
    }

    // relationals -----------------------------------------------------------------
    void Compiler::algebraic_relational(const expr::Expr_ptr expr)
    {
        type::TypeMgr& tm { f_owner.tm() };

        assert(is_binary_algebraic(expr));

        POP_TYPE(rhs_type);
        POP_TYPE(lhs_type);

        assert(rhs_type->is_algebraic() &&
               lhs_type->is_algebraic() &&
               lhs_type->width() == rhs_type->width());

        unsigned width { rhs_type->width() };
        bool signedness {
            lhs_type->is_signed_algebraic() ||
            rhs_type->is_signed_algebraic()
        };

        const type::Type_ptr res_type { tm.find_boolean() };
        PUSH_TYPE(res_type);

        POP_DV(rhs, width);
        POP_DV(lhs, width);

        FRESH_DV(res, 1);
        PUSH_DV(res, 1);

        InlinedOperatorDescriptor md {
            make_ios(signedness, expr->symb(), width), res, lhs, rhs
        };

        f_inlined_operator_descriptors.push_back(md);
    }

    void Compiler::algebraic_equals(const expr::Expr_ptr expr)
    {
        algebraic_relational(expr);
    }

    void Compiler::algebraic_not_equals(const expr::Expr_ptr expr)
    {
        algebraic_relational(expr);
    }

    void Compiler::algebraic_gt(const expr::Expr_ptr expr)
    {
        algebraic_relational(expr);
    }

    void Compiler::algebraic_ge(const expr::Expr_ptr expr)
    {
        algebraic_relational(expr);
    }

    void Compiler::algebraic_lt(const expr::Expr_ptr expr)
    {
        algebraic_relational(expr);
    }

    void Compiler::algebraic_le(const expr::Expr_ptr expr)
    {
        algebraic_relational(expr);
    }

    void Compiler::algebraic_ite(const expr::Expr_ptr expr)
    {
        POP_TYPE(rhs_type);
        POP_TYPE(lhs_type);
        POP_TYPE(cnd_type);

        // condition is boolean, ite operands are algebraic, same width
        assert(rhs_type->is_algebraic() &&
               lhs_type->is_algebraic() &&
               lhs_type->width() == rhs_type->width() &&
               cnd_type->is_boolean());

        unsigned width { rhs_type->width() };

        /* as both lhs and rhs are the same type either works here */
        PUSH_TYPE(rhs_type);

        POP_DV(rhs, width);
        POP_DV(lhs, width);
        POP_DD(cnd);

        FRESH_DV(res, width);
        PUSH_DV(res, width);

        expr::Expr_ptr parent { expr };

        BinarySelectionUnionFindMap::const_iterator eye { f_bsuf_map.find(expr) };
        if (f_bsuf_map.end() != eye) {
            parent = eye->second;
        }

        /* verify if entry for toplevel already exists. If it doesn't,
	 * create it. This ensures the next assertion will certainly
	 * hold. */
        Expr2BinarySelectionDescriptorsMap::const_iterator toplevel_mi {
            f_expr2bsd_map.find(parent)
        };
        if (f_expr2bsd_map.end() == toplevel_mi) {
            f_expr2bsd_map.insert(
                std::pair<expr::Expr_ptr, BinarySelectionDescriptors>(parent, BinarySelectionDescriptors()));
        }

        BinarySelectionDescriptor md {
            width, res, cnd, make_auto_dd(), lhs, rhs
        };
        Expr2BinarySelectionDescriptorsMap::iterator mi {
            f_expr2bsd_map.find(parent)
        };
        assert(f_expr2bsd_map.end() != mi);
        mi->second.push_back(md);
    }

    void Compiler::algebraic_subscript(const expr::Expr_ptr expr)
    {
        enc::EncodingMgr& bm { f_enc };

        POP_TYPE(t0);
        assert(t0->is_algebraic());

        type::Type_ptr itype { t0->as_algebraic() };
        unsigned iwidth(itype->width());
        assert(iwidth == bm.word_width());

        type::Type_ptr t1 { f_type_stack.back() };
        f_type_stack.pop_back();
        assert(t1->is_array());

        type::ArrayType_ptr atype { t1->as_array() };
        type::ScalarType_ptr type { atype->of() };

        unsigned elem_width { type->width() };
        unsigned elem_count { atype->nelems() };

        PUSH_TYPE(type);

        POP_DV(index, iwidth);
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
        } else {
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

            FRESH_DV(dv, elem_width);
            PUSH_DV(dv, elem_width);

            MultiwaySelectionDescriptor msd {
                elem_width, elem_count, dv, cnd_dds, act_dds, lhs
            };
            f_multiway_selection_descriptors.push_back(msd);
        }
    }

    /* add n-1 non significant zero, LSB is original bit */
    void Compiler::algebraic_cast_from_boolean(const expr::Expr_ptr expr)
    {
        expr::Expr_ptr ctx { f_ctx_stack.back() };
        type::Type_ptr tp { f_owner.type(expr->lhs(), ctx) };
        for (unsigned i = 0; i < tp->width() - 1; ++i) {
            PUSH_DD(f_enc.zero());
        }
    }

    /* squeeze all bits in a big Or */
    void Compiler::boolean_cast_from_algebraic(const expr::Expr_ptr expr)
    {
        expr::Expr_ptr ctx { f_ctx_stack.back() };
        type::Type_ptr tp { f_owner.type(expr->rhs(), ctx) };
        POP_DV(rhs, tp->width());

        ADD res { f_enc.zero() };
        for (unsigned i = 0; i < tp->width(); ++i)
            res = res.Or(rhs[i]);

        PUSH_DD(res);
    }

    void Compiler::algebraic_cast_from_algebraic(const expr::Expr_ptr expr)
    {
        expr::Expr_ptr ctx { f_ctx_stack.back() };
        type::Type_ptr src_type { f_owner.type(expr->rhs(), ctx) };
        type::Type_ptr tgt_type { f_owner.type(expr->lhs(), ctx) };

        if (src_type->width() == tgt_type->width()) {
            return; /* nop */
        }

        else if (src_type->width() < tgt_type->width()) {
            /* grow */
            if (tgt_type->is_signed_algebraic()) {
                /* signed, needs sign bit extension (src MSB) */
                ADD msb = f_add_stack.back(); /* just inspect */
                for (unsigned i = src_type->width(); i < tgt_type->width(); ++i) {
                    PUSH_DD(msb);
                }
            } else {
                assert(tgt_type->is_unsigned_algebraic());
                /* unsigned, pad with zeroes */
                for (unsigned i = src_type->width(); i < tgt_type->width(); ++i) {
                    PUSH_DD(f_enc.zero());
                }
            }
        } else {
            /* shrink */
            assert(tgt_type->width() < src_type->width());
            for (unsigned i = src_type->width(); i > tgt_type->width(); --i) {
                f_add_stack.pop_back(); /* discard ADDs */
            }
        }
    }

} // namespace compiler
