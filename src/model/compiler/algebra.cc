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

#include <expr.hh>
#include <compiler.hh>

namespace model {

/**
 * REMARK: operand arguments (which are DD vectors) are fetched from
 * the internal DD stack in a big-endian fashion, that is MSB
 * first. On the other hand, to ensure proper behavior the result of
 * any such operation has to be pushed in reversed order.
 */

// unary ops -------------------------------------------------------------------
void Compiler::algebraic_unary(const expr::Expr_ptr expr)
{
    assert(is_unary_algebraic(expr));

    const type::Type_ptr lhs_type
        (f_type_stack.back());

    // operands is algebraic
    assert(lhs_type -> is_algebraic());
    const type::AlgebraicType_ptr algebraic_type
        (lhs_type -> as_algebraic());

    unsigned width
        (algebraic_type -> width());
    bool signedness
        (algebraic_type -> is_signed_algebraic());

    POP_DV(lhs, width);

    FRESH_DV(res, width);
    PUSH_DV(res, width);

    InlinedOperatorDescriptor iod
        (make_ios( signedness, expr->symb(), width), res, lhs);

    f_inlined_operator_descriptors.push_back(iod);

    DEBUG
        << "Registered " << iod
        << std::endl;
}

void Compiler::algebraic_neg(const expr::Expr_ptr expr)
{ algebraic_unary(expr); }

void Compiler::algebraic_bw_not(const expr::Expr_ptr expr)
{ algebraic_unary(expr); }

// -- binary ops ---------------------------------------------------------------
void Compiler::algebraic_binary(const expr::Expr_ptr expr)
{
    assert(is_binary_algebraic(expr));

    const type::Type_ptr rhs_type
        (f_type_stack.back()); f_type_stack.pop_back();
    const type::Type_ptr lhs_type
        (f_type_stack.back());

    // both operands are algebraic, same width
    assert( rhs_type -> is_algebraic() &&
            lhs_type -> is_algebraic() &&
            lhs_type -> width() == rhs_type -> width());

    unsigned width
        (rhs_type -> width());

    bool signedness
        (lhs_type -> is_signed_algebraic() ||
         rhs_type -> is_signed_algebraic() );

    POP_DV(rhs, width);
    POP_DV(lhs, width);

    FRESH_DV(res, width); // algebraic, same width
    PUSH_DV(res, width);

    InlinedOperatorDescriptor md
        (make_ios( signedness, expr->symb(), width), res, lhs, rhs);

    f_inlined_operator_descriptors.push_back(md);

    DEBUG
        << "Registered "
        << md
        << std::endl;
}

void Compiler::algebraic_plus(const expr::Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_sub(const expr::Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_mul(const expr::Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_div(const expr::Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_mod(const expr::Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_bw_and(const expr::Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_bw_or(const expr::Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_bw_xor(const expr::Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_bw_xnor(const expr::Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_lshift(const expr::Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_rshift(const expr::Expr_ptr expr)
{ algebraic_binary(expr); }

// relationals -----------------------------------------------------------------
void Compiler::algebraic_relational(const expr::Expr_ptr expr)
{
    assert(is_binary_algebraic(expr));

    type::TypeMgr& tm
        (f_owner.tm());

    const type::Type_ptr rhs_type
        (f_type_stack.back());
    f_type_stack.pop_back();

    const type::Type_ptr lhs_type
        (f_type_stack.back());
    f_type_stack.pop_back();

    f_type_stack.push_back( tm.find_boolean());

    // both operands are algebraic, same width
    assert( rhs_type -> is_algebraic() &&
            lhs_type -> is_algebraic() &&
            lhs_type -> width() == rhs_type -> width());

    unsigned width
        (rhs_type -> width());

    bool signedness
        (lhs_type -> is_signed_algebraic() ||
         rhs_type -> is_signed_algebraic() );

    POP_DV(rhs, width);
    POP_DV(lhs, width);

    FRESH_DV(res, 1); // boolean
    PUSH_DV(res, 1);

    InlinedOperatorDescriptor md
        (make_ios( signedness, expr->symb(), width), res, lhs, rhs);

    f_inlined_operator_descriptors.push_back(md);

    DEBUG
        << "Registered "
        << md
        << std::endl;
}

void Compiler::algebraic_equals(const expr::Expr_ptr expr)
{ algebraic_relational(expr); }

void Compiler::algebraic_not_equals(const expr::Expr_ptr expr)
{ algebraic_relational(expr); }

void Compiler::algebraic_gt(const expr::Expr_ptr expr)
{ algebraic_relational(expr); }

void Compiler::algebraic_ge(const expr::Expr_ptr expr)
{ algebraic_relational(expr); }

void Compiler::algebraic_lt(const expr::Expr_ptr expr)
{ algebraic_relational(expr); }

void Compiler::algebraic_le(const expr::Expr_ptr expr)
{ algebraic_relational(expr); }

void Compiler::algebraic_ite(const expr::Expr_ptr expr)
{
    const type::Type_ptr rhs_type
        (f_type_stack.back());
    f_type_stack.pop_back();

    const type::Type_ptr lhs_type
        (f_type_stack.back());
    f_type_stack.pop_back();

    const type::Type_ptr cnd_type
        (f_type_stack.back());
    f_type_stack.pop_back();

    // both operands are algebraic, same width
    assert( rhs_type -> is_algebraic() &&
            lhs_type -> is_algebraic() &&
            cnd_type -> is_boolean() &&
            lhs_type -> width() == rhs_type -> width());

    f_type_stack.push_back( rhs_type );

    unsigned width
        (rhs_type -> width());

    POP_DV(rhs, width);
    POP_DV(lhs, width);

    /* Fetch cnd DD */
    POP_DD(cnd);

    /* Push MUX output DD vector */
    FRESH_DV(res, width);
    PUSH_DV(res, width);

    /* Register ITE MUX */
    expr::Expr_ptr parent
        (expr);

    BinarySelectionUnionFindMap::const_iterator eye
        (f_bsuf_map.find( expr ));

    if (f_bsuf_map.end() != eye)
        parent = eye -> second;

    /* verify if entry for toplevel already exists. If it doesn't, create it */
    {
        Expr2BinarySelectionDescriptorsMap::const_iterator mi
            (f_expr2bsd_map.find(parent));

        if (f_expr2bsd_map.end() == mi)
            f_expr2bsd_map.insert( std::pair< expr::Expr_ptr, BinarySelectionDescriptors >
                                   (parent, BinarySelectionDescriptors()));
    }

    BinarySelectionDescriptor md
        (width, res, cnd, make_auto_dd(), lhs, rhs);

    /* Entry for toplevel does exist for sure */
    {
        Expr2BinarySelectionDescriptorsMap::iterator mi
            (f_expr2bsd_map.find(parent));
        assert( f_expr2bsd_map.end() != mi );

        mi -> second.push_back( md );
    }

    DEBUG
        << "Registered "
        << md
        << std::endl;
}

void Compiler::algebraic_subscript(const expr::Expr_ptr expr)
{
    enc::EncodingMgr& bm
        (f_enc);

    // index
    type::Type_ptr t0
        (f_type_stack.back());
    f_type_stack.pop_back(); // consume index
    assert(t0 -> is_algebraic());

    type::Type_ptr itype
        (t0 -> as_algebraic());
    unsigned iwidth
        (itype -> width());

    POP_DV(index, iwidth);
    assert(iwidth == bm.word_width()); // needed?

    // array
    type::Type_ptr t1
        (f_type_stack.back());
    f_type_stack.pop_back(); // consume array
    assert(t1 -> is_array());

    type::ArrayType_ptr atype
        (t1 -> as_array());
    type::ScalarType_ptr type
        (atype -> of());

    unsigned elem_width
        (type -> width());
    unsigned elem_count
        (atype -> nelems());
    POP_DV(lhs, elem_width * elem_count);

    /* Build selection DDs */
    dd::DDVector cnd_dds;
    dd::DDVector act_dds;
    unsigned j_, j = 0; do {

        unsigned i;
        ADD cnd
            (bm.one());

        i = 0; j_ = j; while (i < iwidth) {
            ADD bit
                ((j_ & 1) ? bm.one() : bm.zero());
            unsigned ndx
                (iwidth - i - 1);
            j_ >>= 1;

            cnd *= index[ ndx ].Xnor(bit);
            ++ i;
        }

        cnd_dds.push_back(cnd);
        act_dds.push_back(make_auto_dd());
    } while (++ j < elem_count);

    /* Push MUX output DD vector */
    FRESH_DV(dv, elem_width);
    PUSH_DV(dv, elem_width);

    PUSH_TYPE(type);

    MultiwaySelectionDescriptor msd
        (elem_width, elem_count, dv, cnd_dds, act_dds, lhs);

    f_multiway_selection_descriptors.push_back(msd);

    DEBUG
        << "Registered " << msd
        << std::endl;
}

/* add n-1 non significant zero, LSB is original bit */
void Compiler::algebraic_cast_from_boolean(const expr::Expr_ptr expr)
{
    type::Type_ptr tp = f_owner.type( expr->lhs(),
                                f_ctx_stack.back());

    for (unsigned i = 0; i < tp->width() -1; ++ i) {
        PUSH_DD(f_enc.zero());
    }
}

/* squeeze all bits in a big Or */
void Compiler::boolean_cast_from_algebraic(const expr::Expr_ptr expr)
{
    type::Type_ptr tp
        (f_owner.type( expr->rhs(),
                       f_ctx_stack.back()));

    POP_DV(rhs, tp -> width());

    ADD res
        (f_enc.zero());

    for (unsigned i = 0; i < tp -> width(); ++ i)
        res = res.Or( rhs[i]);

    PUSH_DD(res);
}

void Compiler::algebraic_cast_from_algebraic(const expr::Expr_ptr expr)
{
    expr::Expr_ptr ctx
        (f_ctx_stack.back());
    type::Type_ptr src_type
        (f_owner.type( expr->rhs(), ctx));
    type::Type_ptr tgt_type
        (f_owner.type( expr->lhs(), ctx));

    if (src_type -> width() == tgt_type -> width())
        return; /* nop */

    else if (src_type -> width() < tgt_type -> width()) {
        /* grow */
        if (tgt_type -> is_signed_algebraic()) {
            /* signed, needs sign bit extension (src MSB) */
            ADD msb = f_add_stack.back(); /* just inspect */
            for (unsigned i = src_type -> width(); i < tgt_type -> width(); ++ i) {
                PUSH_DD( msb);
            }
        }
        else {
            assert( tgt_type -> is_unsigned_algebraic());
            /* unsigned, pad with zeroes */
            for (unsigned i = src_type -> width(); i < tgt_type -> width(); ++ i) {
                PUSH_DD( f_enc.zero());
            }
        }
    }
    else {
        /* shrink */
        assert (tgt_type -> width() < src_type -> width());
        for (unsigned i = src_type -> width(); i > tgt_type -> width(); -- i) {
            f_add_stack.pop_back(); /* discard ADDs */
        }
    }
}

};
