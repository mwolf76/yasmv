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

/* rewrite ( -x ) as ( !x + 1 ) */
void Compiler::algebraic_neg(const Expr_ptr expr)
{
    assert(is_unary_algebraic(expr));
    ExprMgr& em = f_owner.em();

    Type_ptr type = f_type_stack.back(); f_type_stack.pop_back();
    unsigned width = type->width();

    /* create temp complemented ADDs */
    ADD lhs[width];
    for (unsigned i = 0; i < width; ++ i) {
        lhs[i] = f_add_stack.back().BWCmpl(); f_add_stack.pop_back();
    }

    Expr_ptr temp = make_temporary_expr(lhs, width);
    (*this)(em.make_add(temp, em.make_one()));
}

void Compiler::algebraic_not(const Expr_ptr expr)
{
    assert(is_unary_algebraic(expr));

    Type_ptr type = f_type_stack.back(); // just inspect
    unsigned width = type->width();

    ADD lhs[width];
    for (unsigned i = 0; i < width; ++ i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (unsigned i = 0; i < width; ++ i) {
        /* ! x[i] */
        unsigned ndx = width - i - 1;
        f_add_stack.push_back(lhs[ndx].BWCmpl());
    }
}

// -- binary ops ---------------------------------------------------------------
void Compiler::algebraic_binary(const Expr_ptr expr)
{
    assert(is_binary_algebraic(expr));

    unsigned width;
    bool signedness;
    algebrize_binary_arithmetical(width, signedness);

    POP_ALGEBRAIC(rhs, width);
    POP_ALGEBRAIC(lhs, width);
    FRESH_DV(dv, width);

    register_microdescriptor( signedness, expr->symb(),
                              width, dv, lhs, rhs);
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

void Compiler::algebraic_and(const Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_or(const Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_xor(const Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_xnor(const Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_implies(const Expr_ptr expr)
{ algebraic_binary(expr); }

void Compiler::algebraic_lshift(const Expr_ptr expr)
{
    assert(is_binary_algebraic(expr));
    unsigned width;
    bool signedness;
    algebrize_binary_arithmetical(width, signedness);

    ExprMgr& em = f_owner.em();

    POP_ALGEBRAIC(rhs, width);
    POP_ALGEBRAIC(lhs, width);

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
        PUSH_ADD( res[ndx]);
    }
}

void Compiler::algebraic_rshift(const Expr_ptr expr)
{
    assert(is_binary_algebraic(expr));

    unsigned width;
    bool signedness;
    algebrize_binary_arithmetical(width, signedness);

    ExprMgr& em = f_owner.em();

    POP_ALGEBRAIC(rhs, width);
    POP_ALGEBRAIC(lhs, width);

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
        PUSH_ADD(res[ndx]);
    }
}

// relationals -----------------------------------------------------------------
void Compiler::algebraic_relational(const Expr_ptr expr)
{
    assert(is_binary_algebraic(expr));
    unsigned width;
    bool signedness;
    algebrize_binary_relational(width, signedness);

    POP_ALGEBRAIC(rhs, width);
    POP_ALGEBRAIC(lhs, width);
    FRESH_DV(dv, 1);

    register_microdescriptor( signedness, expr->symb(),
                              width, dv, lhs, rhs);
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
    assert(is_ite_algebraic(expr));

    unsigned width;
    bool signedness;
    algebrize_ternary_ite(width, signedness);

    POP_ALGEBRAIC(rhs, width);
    POP_ALGEBRAIC(lhs, width);
    POP_ADD(cnd);

    /* (cond) ? x[i] : y[i] */
    for (unsigned i = 0; i < width; ++ i) {
        unsigned ndx = width - i - 1;
        PUSH_ADD(cnd.Ite(lhs[ndx], rhs[ndx]));
    }
}

void Compiler::algebraic_subscript(const Expr_ptr expr)
{
    assert(is_subscript_algebraic(expr));

    // index
    Type_ptr t0 = f_type_stack.back(); f_type_stack.pop_back(); // consume index
    assert( t0 -> is_algebraic() && ! t0 -> is_constant());

    Type_ptr itype = t0 -> as_algebraic();
    POP_ALGEBRAIC(index, itype -> width());

    assert( itype -> width() == f_enc.word_width());

    // array
    Type_ptr t1 = f_type_stack.back(); f_type_stack.pop_back(); // consume array
    assert( t1 -> is_array());
    ArrayType_ptr atype = t1 -> as_array();

    unsigned elem_size  = atype -> of() -> width();
    unsigned elem_count = atype -> nelems();
    POP_ALGEBRAIC(vec, elem_size * elem_count);

    // build the multiplexer
    ADD mpx[ elem_size ];
    for (unsigned i = 0; i < elem_size; ++ i) {
        mpx[i] = f_enc.error(); // default to failure
    }

    ExprMgr& em = f_owner.em();
    unsigned j = elem_count; do {

        -- j;

        /* A bit of magic: reusing eq code :-) */
        (*this)( em.make_eq( expr->rhs(),
                             em.make_const(j)));

        ADD cnd = f_add_stack.back(); f_add_stack.pop_back();
        f_type_stack.pop_back(); /* adjust type stack */

        for (unsigned i = 0; i < elem_size; ++ i ) {
            unsigned ndx = elem_size - i - 1;
            mpx[ ndx ] = cnd.Ite( vec[ j * elem_size + i ], mpx[ ndx ]);
        }

    } while (j);

    // push mpx backwards
    for (unsigned i = 0; i < elem_size; ++ i) {
        PUSH_ADD( mpx[ elem_size - i - 1]);
    }

    f_type_stack.push_back( atype -> of());
}

/* add n-1 non significant zero, LSB is original bit */
void Compiler::algebraic_cast_from_boolean(const Expr_ptr expr)
{
    Type_ptr tp = f_owner.type( expr->lhs(),
                                f_ctx_stack.back());

    for (unsigned i = 0; i < tp->width() -1; ++ i) {
        PUSH_ADD(f_enc.zero());
    }
}

/* squeeze all bits in a big Or */
void Compiler::boolean_cast_from_algebraic(const Expr_ptr expr)
{
    Type_ptr tp = f_owner.type( expr->rhs(),
                                f_ctx_stack.back());

    POP_ALGEBRAIC(rhs, tp -> width());
    ADD res = f_enc.zero();
    for (unsigned i = 0; i < tp->width(); ++ i) {
        res = res.Or( rhs[i]); // order is not relevant here
    }

    Expr_ptr temp = make_temporary_expr( &res, 1);
    (*this)(temp);
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
                PUSH_ADD( msb);
            }
        }
        else {
            assert( tgt_type -> is_unsigned_algebraic());
            /* unsigned, pad with zeroes */
            for (unsigned i = src_type -> width(); i < tgt_type -> width(); ++ i) {
                PUSH_ADD( f_enc.zero());
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
