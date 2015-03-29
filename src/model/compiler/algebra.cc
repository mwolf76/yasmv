/**
 *  @file algebra.cc
 *  @brief Boolean compiler - algebraic manipulations module.
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
#include <common.hh>

#include <expr.hh>
#include <compiler.hh>

/* Important Remark: operand arguments (which are DD vectors) are
   fetched from the internal DD stack in a big-endian fashion, that is
   MSB first. On the other hand, to ensure proper behavior the
   *result* of the operation has to be pushed in reverse order. */

// unary ops -------------------------------------------------------------------

void Compiler::algebraic_unary(const Expr_ptr expr)
{
    assert(is_unary_algebraic(expr));

    const Type_ptr lhs_type
        (f_type_stack.back());

    // operands is algebraic
    assert(lhs_type -> is_algebraic());
    const AlgebraicType_ptr algebraic_type
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

void Compiler::algebraic_neg(const Expr_ptr expr)
{ algebraic_unary(expr); }

void Compiler::algebraic_bw_not(const Expr_ptr expr)
{ algebraic_unary(expr); }

// -- binary ops ---------------------------------------------------------------
void Compiler::algebraic_binary(const Expr_ptr expr)
{
    assert(is_binary_algebraic(expr));

    const Type_ptr rhs_type
        (f_type_stack.back()); f_type_stack.pop_back();
    const Type_ptr lhs_type
        (f_type_stack.back());

    // both operands are algebraic, same width and signedness
    assert( rhs_type -> is_algebraic() &&
            lhs_type -> is_algebraic() &&

            lhs_type -> width() == rhs_type -> width() &&

            _iff( lhs_type -> is_signed_algebraic(),
                  rhs_type -> is_signed_algebraic()));

    const AlgebraicType_ptr algebraic_type
        (rhs_type -> as_algebraic());
    unsigned width
        (algebraic_type -> width());
    bool signedness
        (algebraic_type -> is_signed_algebraic());

    POP_DV(rhs, width);
    POP_DV(lhs, width);

    FRESH_DV(res, width);
    PUSH_DV(res, width);

    InlinedOperatorDescriptor md
        (make_ios( signedness, expr->symb(), width), res, lhs, rhs);

    f_inlined_operator_descriptors.push_back(md);

    DEBUG
        << "Registered "
        << md
        << std::endl;
}

void Compiler::algebraic_plus(const Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_sub(const Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_mul(const Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_div(const Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_mod(const Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_bw_and(const Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_bw_or(const Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_bw_xor(const Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_bw_xnor(const Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_lshift(const Expr_ptr expr)
{
    assert(is_binary_algebraic(expr));
    ExprMgr& em = f_owner.em();

    const Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();
    const Type_ptr lhs_type = f_type_stack.back(); f_type_stack.pop_back();

    // both operands are algebraic, same width and signedness
    assert( rhs_type -> is_algebraic() &&
            lhs_type -> is_algebraic() &&

            lhs_type -> width() == rhs_type -> width() &&

            _iff( lhs_type -> is_signed_algebraic(),
                  rhs_type -> is_signed_algebraic()));

    unsigned width = rhs_type -> width();
    //bool signedness= rhs_type -> is_signed_algebraic();

    POP_DV(rhs, width);
    POP_DV(lhs, width);

    ADD tmp[width];
    for (unsigned i = 0; i < width; ++ i) {
        tmp[i] = lhs[i];
    }

    ADD res[width];
    for (unsigned i = 0; i < width; ++ i) {
        res[i] = f_enc.zero();
    }

    ADD mask(f_enc.constant(1));
    ADD carry;

    for (unsigned k = 0; k < width; ++ k) {

        /* compile selection condition (re-entrant invocation) */
        (*this)(em.make_eq( expr->rhs(), em.make_const(k)));
        ADD cond = f_add_stack.back(); f_add_stack.pop_back();
        f_type_stack.pop_back(); /* adjust type stack */

        if (! cond.IsZero()) {
            carry = f_enc.zero(); /* lsh always introduces 0 as LSB */
            for (unsigned i = 0; i < width; ++ i) {
                unsigned ndx = width - i - 1;

                /* c' = (0 < D & MSB_MASK); */
                ADD next_carry = f_enc.zero().
                    LT( tmp[ndx].BWTimes( mask ));

                /* x[i] = ( x[i] << 1 ) | carry */
                tmp[ndx] = tmp[ndx].BWLShift().BWOr(carry);

                res[ndx] = cond.Ite( tmp[ndx], res[ndx] );
                carry = next_carry;
            }
        }
    }

    /* push result (reversed) */
    for (unsigned i = 0; i < width; ++ i) {
        unsigned ndx = width - i - 1;
        PUSH_DD( res[ndx]);
    }
}

void Compiler::algebraic_rshift(const Expr_ptr expr)
{
    assert(is_binary_algebraic(expr));
    ExprMgr& em = f_owner.em();

    const Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();
    const Type_ptr lhs_type = f_type_stack.back(); f_type_stack.pop_back();

    // both operands are algebraic, same width and signedness
    assert( rhs_type -> is_algebraic() &&
            lhs_type -> is_algebraic() &&

            lhs_type -> width() == rhs_type -> width() &&

            _iff( lhs_type -> is_signed_algebraic(),
                  rhs_type -> is_signed_algebraic()));

    unsigned width = rhs_type -> width();
    //bool signedness= rhs_type -> is_signed_algebraic();

    POP_DV(rhs, width);
    POP_DV(lhs, width);

    ADD tmp[width];
    for (unsigned i = 0; i < width; ++ i) {
        tmp[i] = lhs[i];
    }

    ADD res[width];
    for (unsigned i = 0; i < width; ++ i) {
        res[i] = f_enc.zero();
    }

    ADD weight(f_enc.constant(0));

    ADD carry;
    for (unsigned k = 0; k < width; ++ k) {

        /* compile selection condition (re-entrant invocation) */
        (*this)(em.make_eq( expr->rhs(), em.make_const(k)));
        ADD cond = f_add_stack.back(); f_add_stack.pop_back();
        f_type_stack.pop_back(); /* adjust type stack */

        if (! cond.IsZero()) {
            /* FIXME: rsh should *not* always introduce 0 as LSB */
            carry = f_enc.zero();

            for (unsigned i = 0; i < width; ++ i) {
                unsigned ndx = i; /* left-to-right */

                /* c' = ( 0 < ( D[i] & 0x1 ) << 3 */
                ADD next_carry = f_enc.zero().
                    LT(tmp[ndx].BWTimes(f_enc.one())).LShift(weight);

                /* x[i] = ( x[i] >> 1 ) | c */
                tmp[ndx] = tmp[ndx].BWRShift().BWOr(carry);

                res[ndx] = cond.Ite( tmp[ndx], res[ndx] );
                carry = next_carry;
            }
        }
    }

    /* push result (reversed) */
    for (unsigned i = 0; i < width; ++ i) {
        unsigned ndx = width - i - 1;
        PUSH_DD(res[ndx]);
    }
}

// relationals -----------------------------------------------------------------
void Compiler::algebraic_relational(const Expr_ptr expr)
{
    assert(is_binary_algebraic(expr));
    TypeMgr& tm (f_owner.tm());

    const Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();
    const Type_ptr lhs_type = f_type_stack.back(); f_type_stack.pop_back();
    f_type_stack.push_back( tm.find_boolean());

    // both operands are algebraic, same width and signedness
    assert( rhs_type -> is_algebraic() &&
            lhs_type -> is_algebraic() &&

            lhs_type -> width() == rhs_type -> width());

    unsigned width = rhs_type -> width();
    bool signedness= lhs_type -> is_signed_algebraic() ||
        rhs_type -> is_signed_algebraic();

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

void Compiler::algebraic_equals(const Expr_ptr expr)
{ algebraic_relational(expr); }

// TODO: evaluate which approach is more efficient
void Compiler::algebraic_not_equals(const Expr_ptr expr)
{ algebraic_relational(expr); }

void Compiler::algebraic_gt(const Expr_ptr expr)
{ algebraic_relational(expr); }

void Compiler::algebraic_ge(const Expr_ptr expr)
{ algebraic_relational(expr); }

void Compiler::algebraic_lt(const Expr_ptr expr)
{ algebraic_relational(expr); }

void Compiler::algebraic_le(const Expr_ptr expr)
{ algebraic_relational(expr); }

void Compiler::algebraic_ite(const Expr_ptr expr)
{
    const Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();
    const Type_ptr lhs_type = f_type_stack.back(); f_type_stack.pop_back();
    const Type_ptr cnd_type = f_type_stack.back(); f_type_stack.pop_back();
    f_type_stack.push_back( rhs_type );

    // both operands are algebraic, same width and signedness
    assert( rhs_type -> is_algebraic() &&
            lhs_type -> is_algebraic() &&
            cnd_type -> is_boolean() &&

            lhs_type -> width() == rhs_type -> width() &&

            _iff( lhs_type -> is_signed_algebraic(),
                  rhs_type -> is_signed_algebraic()));

    unsigned width
        (rhs_type -> width());

    POP_DV(rhs, width);
    POP_DV(lhs, width);

    /* Fetch cnd DD recursively */
    POP_DD(cnd);

    /* Push MUX output DD vector */
    FRESH_DV(res, width);
    PUSH_DV(res, width);

    /* Register ITE MUX */
    Expr_ptr parent
        (expr);

    BinarySelectionUnionFindMap::const_iterator eye
        (f_bsuf_map.find( expr ));

    if (f_bsuf_map.end() != eye)
        parent = eye -> second;

    /* verify if entry for toplevel already exists. If it doesn't,
       create it */
    {
        Expr2BinarySelectionDescriptorsMap::const_iterator mi
            (f_expr2bsd_map.find(parent));

        if (f_expr2bsd_map.end() == mi)
            f_expr2bsd_map.insert( std::make_pair< Expr_ptr, BinarySelectionDescriptors >
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

void Compiler::algebraic_subscript(const Expr_ptr expr)
{
    EncodingMgr& bm
        (f_enc);

    // index
    Type_ptr t0
        (f_type_stack.back());
    f_type_stack.pop_back(); // consume index
    assert(t0 -> is_algebraic());

    Type_ptr itype
        (t0 -> as_algebraic());
    unsigned iwidth
        (itype -> width());

    POP_DV(index, iwidth);
    assert(iwidth == bm.word_width()); // needed?

    // array
    Type_ptr t1
        (f_type_stack.back());
    f_type_stack.pop_back(); // consume array
    assert(t1 -> is_array());

    ArrayType_ptr atype
        (t1 -> as_array());
    ScalarType_ptr type
        (atype -> of());

    unsigned elem_width
        (type -> width());
    unsigned elem_count
        (atype -> nelems());
    POP_DV(lhs, elem_width * elem_count);

    /* Build selection DDs */
    DDVector cnd_dds;
    DDVector act_dds;
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
void Compiler::algebraic_cast_from_boolean(const Expr_ptr expr)
{
    Type_ptr tp = f_owner.type( expr->lhs(),
                                f_ctx_stack.back());

    for (unsigned i = 0; i < tp->width() -1; ++ i) {
        PUSH_DD(f_enc.zero());
    }
}

/* squeeze all bits in a big Or */
void Compiler::boolean_cast_from_algebraic(const Expr_ptr expr)
{
    Type_ptr tp = f_owner.type( expr->rhs(),
                                f_ctx_stack.back());

    POP_DV(rhs, tp -> width());

    ADD res = f_enc.zero();
    for (unsigned i = 0; i < tp -> width(); ++ i)
        res = res.Or( rhs[i]);

    PUSH_DD(res);
}

void Compiler::algebraic_cast_from_algebraic(const Expr_ptr expr)
{
    Expr_ptr ctx (f_ctx_stack.back());
    Type_ptr src_type = f_owner.type( expr->rhs(), ctx);
    Type_ptr tgt_type = f_owner.type( expr->lhs(), ctx);

    if (src_type -> width() == tgt_type -> width()) {
        return; /* nop */
    }
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
