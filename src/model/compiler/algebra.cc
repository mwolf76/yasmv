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

void Compiler::algebraic_not(const Expr_ptr expr)
{
    assert( is_unary_algebraic(expr) );

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

// TODO: add options to enable ADD-based or microcode-based
// TODO: evaluate which approach is more efficient
void Compiler::algebraic_plus(const Expr_ptr expr)
{
#if 0
    unsigned width = algebrize_binary_arithmetical();

    POP_ALGEBRAIC(rhs, width);
    POP_ALGEBRAIC(lhs, width);

    /* x[i] + y[i] + c */
    ADD carry = f_enc.zero();
    for (unsigned i = 0; i < width; ++ i) {

        unsigned ndx = width - i - 1;

        ADD tmp = lhs[ndx].Plus(rhs[ndx]).Plus(carry);
        carry = f_enc.base().LEQ(tmp); /* c >= 0x10 */

        /* x[i] = (x[i] + y[i] + c) % base */
        PUSH_ADD(tmp.Modulus(f_enc.base()));
    }
#else
    algebraic_binary_microcode_operation(expr);
#endif
}

/* rewrite ( -x ) as ( !x + 1 ) */
void Compiler::algebraic_neg(const Expr_ptr expr)
{
    assert( is_unary_algebraic(expr) );
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

// TODO: add options to enable ADD-based or microcode-based
void Compiler::algebraic_sub(const Expr_ptr expr)
{
#if 1
    ExprMgr& em = f_owner.em();
    assert( is_binary_algebraic(expr) );

    /* rewrite requires discarding operands */
    algebraic_discard_op();
    algebraic_discard_op();

    (*this)( em.make_add( expr->lhs(),
                          em.make_neg(expr->rhs())));
#else
    algebrize_binary_microcode_operation(expr);
#endif
}

// TODO: add options to enable ADD-based or microcode-based
// TODO: evaluate which approach is more efficient
void Compiler::algebraic_mul(const Expr_ptr expr)
{
#if 0
    /* longhand mul */
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_binary_arithmetical();

    POP_ALGEBRAIC(rhs, width);
    POP_ALGEBRAIC(lhs, width);

    ADD res[width];
    ADD tmp[width];

    for (unsigned i = 0; i < width; ++ i) {
        res[i] = f_enc.zero();
        tmp[i] = f_enc.zero();
    }

    ADD carry;
    for (unsigned i = 0; i < width; ++ i) {
        unsigned ndx_i = width - i - 1;

        carry = f_enc.zero();
        for (unsigned j = 0; j < width; ++ j) {
            unsigned ndx_j = width - j - 1;

            // ignore what happens out of result boundaries
            if (i + j < width) {
                unsigned ndx = width - i - j - 1;

                /* MUL table for digit product */
                ADD product = lhs[ndx_i].Times(rhs[ndx_j]).Plus(carry);

                /* calculate digit and carry */
                tmp[ndx] = product.Modulus(f_enc.base());
                carry    = product.Divide (f_enc.base());
            }
        }

        // update result
        for (unsigned j = 0; j < width; ++ j) {
            unsigned ndx_j = width - j - 1;
            res[ndx_j] += tmp[ndx_j];
        }

        // return i-th digit of result
        PUSH_ADD(res[ndx_i]);
    }
#else
    algebraic_binary_microcode_operation(expr);
#endif
}

// microcode-only
void Compiler::algebraic_div(const Expr_ptr expr)
{ algebraic_binary_microcode_operation(expr); }

// microcode-only
void Compiler::algebraic_mod(const Expr_ptr expr)
{ algebraic_binary_microcode_operation(expr); }

// bitwise operators
void Compiler::algebraic_and(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_binary_arithmetical();

    POP_ALGEBRAIC(rhs, width);
    POP_ALGEBRAIC(lhs, width);

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (unsigned i = 0; i < width; ++ i) {

        /* x[i] &  y[i] */
        unsigned ndx = width - i - 1;
        PUSH_ADD(lhs[ndx].BWTimes(rhs[ndx]));
    }
}

void Compiler::algebraic_or(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_binary_arithmetical();

    POP_ALGEBRAIC(rhs, width);
    POP_ALGEBRAIC(lhs, width);

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (unsigned i = 0; i < width; ++ i) {

        /* x[i] | y[i] */
        unsigned ndx = width - i - 1;
        PUSH_ADD(lhs[ndx].BWOr(rhs[ndx]));
    }
}

void Compiler::algebraic_xor(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_binary_arithmetical();

    POP_ALGEBRAIC(rhs, width);
    POP_ALGEBRAIC(lhs, width);

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (unsigned i = 0; i < width; ++ i) {

        /* x[i] ^ y[i] */
        unsigned ndx = width - i - 1;
        PUSH_ADD(lhs[ndx].BWXor(rhs[ndx]));
    }
}

void Compiler::algebraic_xnor(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    assert( is_binary_algebraic(expr) );

    /* rewrite requires discarding operands */
    algebraic_discard_op();
    algebraic_discard_op();

    (*this)(em.make_not( em.make_xor( expr->lhs(),
                                      expr->rhs())));
}

void Compiler::algebraic_implies(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    assert( is_binary_algebraic(expr) );

    /* rewrite requires discarding operands */
    algebraic_discard_op();
    algebraic_discard_op();

    (*this)(em.make_or( em.make_not( expr->lhs()),
                        expr->rhs()));
}

void Compiler::algebraic_lshift(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_binary_arithmetical();

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
    ExprMgr& em = f_owner.em();

    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_binary_arithmetical();

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

void Compiler::algebraic_equals(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_binary_relational();

    POP_ALGEBRAIC(rhs, width);
    POP_ALGEBRAIC(lhs, width);

#if 1
    ADD tmp = f_enc.one();
    for (unsigned i = 0; i < width; ++ i) {
        unsigned ndx = width - 1 -i;
        tmp *= lhs[ndx].Equals(rhs[ndx]);
    }
    PUSH_ADD( tmp );
#else
    ADD tmp[width];
    for (unsigned i = 0; i < width; ++ i) {
        unsigned ndx = width - 1 -i;
        tmp[ndx] = lhs[ndx].Equals(rhs[ndx]);
    }

    PUSH_ADD( book_and_chain(tmp, width));
#endif
}

// TODO: evaluate which approach is more efficient
void Compiler::algebraic_not_equals(const Expr_ptr expr)
{
#if 1
    /* new implementation, does not perform rewriting on equals */
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_binary_relational();

    POP_ALGEBRAIC(rhs, width);
    POP_ALGEBRAIC(lhs, width);

    ADD tmp = f_enc.zero();
    for (unsigned i = 0; i < width; ++ i) {
        unsigned ndx = width - 1 -i;
        tmp = tmp.Or( lhs[ndx].NotEquals(rhs[ndx]));
    }

    PUSH_ADD( tmp);
#else
    /* old implementation, performs rewriting on Equals */
    ExprMgr& em = f_owner.em();
    assert( is_binary_algebraic(expr) );

    /* rewrite requires discarding operands */
    algebraic_discard_op();
    algebraic_discard_op();

    (*this)(em.make_not(em.make_eq(expr->lhs(),
                                   expr->rhs())));
#endif
}

void Compiler::algebraic_gt(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );

    /* rewrite requires discarding operands */
    algebraic_discard_op();
    algebraic_discard_op();

    ExprMgr& em = f_owner.em();
    (*this)(em.make_not( em.make_le( expr->lhs(), expr->rhs())));
}

void Compiler::algebraic_ge(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    assert( is_binary_algebraic(expr) );

    /* rewrite requires discarding operands */
    algebraic_discard_op();
    algebraic_discard_op();

    (*this)(em.make_not( em.make_lt( expr->lhs(),
                                     expr->rhs())));
}

void Compiler::algebraic_lt(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_binary_relational();

    POP_ALGEBRAIC(rhs, width);
    POP_ALGEBRAIC(lhs, width);

    // MSB predicate first, if false and prefix matches, inspect next
    // digit. Uses AND-chain optimization to build clauses.
    ADD pred = f_enc.zero();
    for (unsigned i = 0; i < width; ++ i) {

        DDVector chain;

        /* build chain prefix */
        for (unsigned j = 0; j < i; j ++ ) {
            chain.push_back(rhs[j].Equals(lhs[j]));
        }

        /* add final condition */
        chain.push_back(lhs[i].LT(rhs[i]));

        assert(1 + i == chain.size());

        /* add optimized chain to disjunction */
        pred = pred.Or( book_and_chain(chain));
    }

    /* just one predult */
    PUSH_ADD(pred);
}

void Compiler::algebraic_le(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_binary_relational();

    POP_ALGEBRAIC(rhs, width);
    POP_ALGEBRAIC(lhs, width);

    // MSB predicate first, if false and prefix matches, inspect next
    // digit. Uses AND-chain optimization to build clauses.
    ADD pred = f_enc.zero();
    for (unsigned i = 0; i < width; ++ i) {

        DDVector chain;

        /* build chain prefix */
        for (unsigned j = 0; j < i; j ++ ) {
            chain.push_back(rhs[j].Equals(lhs[j]));
        }

        /* add final condition */
        chain.push_back(lhs[i].LEQ(rhs[i]));

        assert(1 + i == chain.size());

        /* add optimized chain to disjunction */
        pred = pred.Or( book_and_chain(chain));
    }

    /* just one result */
    PUSH_ADD(pred);
}

void Compiler::algebraic_ite(const Expr_ptr expr)
{
    assert( is_ite_algebraic(expr) );
    unsigned width = algebrize_ternary_ite();

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
    assert( is_subscript_algebraic(expr));

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
