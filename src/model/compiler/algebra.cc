/**
 *  @file algebra.cc
 *  @brief Boolean compiler - algebraic manipulations
 *
 *  This module contains definitions and services that implement the
 *  booolean expressions compilation into a form which is suitable for
 *  the SAT analysis. Current implementation uses ADDs to perform
 *  expression manipulation and booleanization. Expressions are
 *  assumed to be type-safe, only boolean expressions on arithmetic
 *  predicates are supported. The final result of expression
 *  compilation must be a 0-1 ADD_ which is suitable for CNF clauses
 *  injection directly into the SAT solver. The compilation engine is
 *  implemented using a simple walker pattern: (a) on preorder, return
 *  true if the node has not yet been visited; (b) always do in-order
 *  (for binary nodes); (c) perform proper compilation in post-order
 *  hooks.
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

void Compiler::algebraic_neg(const Expr_ptr expr)
{
    assert( is_unary_algebraic(expr) );
    ExprMgr& em = f_owner.em();

    Type_ptr type = f_type_stack.back(); f_type_stack.pop_back();
    unsigned width = type->size();

    /* create temp complemented ADDs */
    ADD lhs[width];
    for (unsigned i = 0; i < width; ++ i) {
        lhs[i] = f_add_stack.back().BWCmpl(); f_add_stack.pop_back();
    }

    /* rewrite ( -x ) as ( !x + 1 ) */
    Expr_ptr temp = make_temporary_encoding(lhs, width);
    (*this)(em.make_add(temp, em.make_one()));
}

void Compiler::algebraic_not(const Expr_ptr expr)
{
    assert( is_unary_algebraic(expr) );

    Type_ptr type = f_type_stack.back(); // just inspect
    unsigned width = type->size();

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

void Compiler::algebraic_plus(const Expr_ptr expr)
{
    unsigned width = algebrize_binary_arithmetical();

    POP_ALGEBRAIC(rhs, width);
    POP_ALGEBRAIC(lhs, width);

    /* perform arithmetic sum using positional algorithm */
    ADD carry = f_enc.zero();
    for (unsigned i = 0; i < width; ++ i) {

        /* x[i] + y[i] + c */
        unsigned ndx = width - i - 1;
        ADD tmp = lhs[ndx].Plus(rhs[ndx]).Plus(carry);
        carry = f_enc.base().LEQ(tmp); /* c >= 0x10 */

        /* x[i] = (x[i] + y[i] + c) % base */
        PUSH_ADD(tmp.Modulus(f_enc.base()));
    }
}

void Compiler::algebraic_sub(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    assert( is_binary_algebraic(expr) );

    /* rewrite requires discarding operands */
    algebraic_discard_op();
    algebraic_discard_op();

    (*this)( em.make_add( expr->lhs(),
                          em.make_neg(expr->rhs())));
}

void Compiler::algebraic_mul(const Expr_ptr expr)
{
#if 0
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_binary_arithmetical();

    recursive_mul(width, false);
#else
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
#endif
}

/* fetched width digits from the ADD stack, shifts to the left of the
   given amount, pads with non-significant left-hand zeros up to 2 *
   width digits, and pushes back into the ADD stack in reverse
   order. This is a private service of Compiler::recursive_mul */
void Compiler::recursive_mul_prepare_shift_and_pad(unsigned width, unsigned shift)
{
    unsigned i, ndx = 0, dbl = 2 * width;
    unsigned pad = dbl - width - shift;
    ADD tmp[dbl];

    /* padding */
    for (i = 0; i < pad; ++ i) {
        tmp[ ndx ++ ] = f_enc.zero();
    }

    /* fetching */
    for (i = 0; i < width; ++ i) {
        tmp[ ndx ++ ] = f_add_stack.back();
        f_add_stack.pop_back();
    }

    /* shifting */
    for (i = 0; i < shift; ++ i) {
        tmp[ ndx ++ ] = f_enc.zero();
    }

    assert( ndx == dbl );

    /* push result */
    for (i = 0; i < dbl; ++ i) {
        ndx = dbl - i - 1;
        f_add_stack.push_back( tmp[ndx] );
    }
}

/**
    Let x and y be represented as n-digit strings in some base B. For
    any positive integer m less than n, one can write the two given
    numbers as

    x = x1 B^m + x0
    y = y1 B^m + y0,
    where x0 and y0 are less than B^m. The product is then

    xy = x1y1 B2^m + x1y0 B^m + x0y1 B^m + x0y0
**/
void Compiler::recursive_mul(unsigned width, bool extra)
{
    /* Induction base */
    assert((width == 1) || ((width & 1) == 0)); // is 1 or even
    if (width == 1) {
        longhand_mul(1, extra);
        return;
    }

    unsigned stack_size = f_add_stack.size();

    POP_ALGEBRAIC( rhs, width);
    POP_ALGEBRAIC( lhs, width);

    // width is a multiple of 2
    unsigned hlf = width / 2;
    unsigned dbl = width * 2;

    /* -- DIVIDE ------------------------------------------------------------ */
    {
        /* -- 2.1. Al * Bl */
        for (unsigned i = 0; i < hlf; ++ i) {
            unsigned ndx = width - i - 1;
            PUSH_ADD( rhs[ndx]);
        }
        for (unsigned i = 0; i < hlf; ++ i) {
            unsigned ndx = width - i - 1;
            PUSH_ADD( lhs[ndx]);
        }
        recursive_mul(hlf, true);
        recursive_mul_prepare_shift_and_pad( width, 0);

        /* -- 2.2.  Ah * Bl */
        for (unsigned i = 0; i < hlf; ++ i) {
            unsigned ndx = width - i - 1;
            PUSH_ADD( rhs[ndx]);
        }
        for (unsigned i = hlf; i < width; ++ i) {
            unsigned ndx = width - i - 1;
            PUSH_ADD( lhs[ndx]);
        }
        recursive_mul(hlf, true);
        recursive_mul_prepare_shift_and_pad( width, hlf);

        /* -- 2.3.  Al * Bh */
        for (unsigned i = hlf; i < width; ++ i) {
            unsigned ndx = width - i - 1;
            PUSH_ADD( rhs[ndx]);
        }
        for (unsigned i = 0; i < hlf; ++ i) {
            unsigned ndx = width - i - 1;
            PUSH_ADD( lhs[ndx]);
        }
        recursive_mul(hlf, true);
        recursive_mul_prepare_shift_and_pad( width, hlf);

        /* -- 2.4. Ah * Bh */
        for (unsigned i = hlf; i < width; ++ i) {
            unsigned ndx = width - i - 1;
            PUSH_ADD( rhs[ndx]);
        }
        for (unsigned i = hlf; i < width; ++ i) {
            unsigned ndx = width - i - 1;
            PUSH_ADD( lhs[ndx]);
        }
        recursive_mul(hlf, true);
        recursive_mul_prepare_shift_and_pad( width, width);
    }

    /* -- COMBINE ----------------------------------------------------------- */
    {
        /* Now we have 4 2m digits numbers in the stack: A, B, C and
           D, in reversed order. Result is (((A + B) + C) + D). */
        ADD lhs[dbl];
        ADD rhs[dbl];
        unsigned j;

        j = 0; do {

            // Fetch operands
            for (unsigned i = 0; i < dbl; ++ i) {
                rhs[i] = f_add_stack.back();
                f_add_stack.pop_back();
            }
            for (unsigned i = 0; i < dbl; ++ i) {
                lhs[i] = f_add_stack.back();
                f_add_stack.pop_back();
            }

            ADD carry = f_enc.zero();

            /* If not in extra mode (this occurs at toplevel), prevent
               useless calculations to be performed. */
            for (unsigned i = 0; i < (extra ? dbl : width); ++ i) {
                unsigned ndx = dbl - i - 1;
                ADD tmp = lhs[ndx].Plus( rhs[ndx]).Plus(carry);

                carry = f_enc.base().LEQ(tmp); /* c >= 0x10 */
                PUSH_ADD(tmp.Modulus(f_enc.base()));
            }

            if (j == 2) // we're done
                break;

            // if not in extra mode, zero padding is required to keep going
            if (!extra) {
                PUSH_ADD(carry);
                for (unsigned i = 1; i < width; ++ i) {
                    f_add_stack.push_back(f_enc.zero());
                }
            }

            ++ j;
        } while (1);
    }

    // recursion check
    if (extra) {
        assert( f_add_stack.size() == stack_size );
    }
}


/* Multiplying 2 m-digits numbers yields a 2m digits number. As in
   ordinary ALU operations result digits "falling off" the word
   representation boundary just get discarded (overflow). However,
   keeping those extra digits in calculations is required when using
   this algorithm as a building block for recursive algorithms
   (i.e. Recursive and Karatsuba algorithms). This method yields a
   single m-digits number if extra is false (default), a 2m-digits
   number otherwise. */
void Compiler::longhand_mul(unsigned width, bool extra)
{
    POP_ALGEBRAIC(rhs, width);
    POP_ALGEBRAIC(lhs, width);

    unsigned actual = extra ? 2 * width : width;

    ADD res[actual];
    ADD tmp[actual];
    ADD carry;

    // blanking the result and tmp ADD stores
    for (unsigned i = 0; i < actual; ++ i) {
        res[i] = f_enc.zero();
        tmp[i] = f_enc.zero();
    }

    // foreach actual digit, perform long mul algorithm
    for (unsigned i = 0; i < actual; ++ i) {

        unsigned ndx_i = actual - i - 1;
        ADD left = (extra)
            ? (width <= ndx_i) ? lhs[ndx_i - width] : f_enc.zero()
            : lhs[ndx_i]
            ;

        carry = f_enc.zero();
        for (unsigned j = 0; j < actual; ++ j) {
            // just ignore what happens out of result boundaries
            if (i + j < actual) {
                unsigned ndx_j = actual - j - 1;
                ADD right = (extra)
                    ? (width <= ndx_j) ? rhs[ndx_j - width] : f_enc.zero()
                    : rhs[ndx_j]
                    ;

                unsigned ndx_p = actual - i - j - 1;
                ADD product = left.Times(right).Plus(carry);

                /* calculate digit and carry */
                tmp[ndx_p] = product.Modulus(f_enc.base());
                carry      = product.Divide (f_enc.base());
            }
        }

        // update the result and push i-th digit of it.
        for (unsigned j = 0; j < actual; ++ j) {
            unsigned ndx_j = actual - j - 1;
            res[ndx_j] += tmp[ndx_j];
        }

        PUSH_ADD(res[ndx_i]);
    }
}

void Compiler::algebraic_div(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    assert( false ); // TODO
}

void Compiler::algebraic_mod(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    assert( false ); // TODO
}

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

    unsigned bits_per_digit (OptsMgr::INSTANCE().bits_per_digit());
    ADD mask(f_enc.constant(1 << (bits_per_digit - 1)));
    ADD carry;

    for (unsigned k = 0; k < bits_per_digit * width; ++ k) {

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

    unsigned bits_per_digit (OptsMgr::INSTANCE().bits_per_digit());
    ADD weight(f_enc.constant(bits_per_digit - 1));

    ADD carry;
    for (unsigned k = 0; k < bits_per_digit * width; ++ k) {

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

    ADD tmp[width];
    for (unsigned i = 0; i < width; ++ i) {
        unsigned ndx = width - 1 -i;
        tmp[ndx] = lhs[ndx].Equals(rhs[ndx]);
    }

    PUSH_ADD( book_and_chain(tmp, width));
}

void Compiler::algebraic_not_equals(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    assert( is_binary_algebraic(expr) );

    /* rewrite requires discarding operands */
    algebraic_discard_op();
    algebraic_discard_op();

    (*this)(em.make_not(em.make_eq(expr->lhs(),
                                   expr->rhs())));
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

    /* MSB predicate first, if false and prefix matches, inspect next
       digit. */
    ADD pred = f_enc.zero();
    for (unsigned i = 0; i < width; ++ i) {
        ADD phi[1 + i];

        /* prefix */
        for (unsigned j = 0; j < i; j ++ ) {
            phi[j] = rhs[j].Equals(lhs[j]);
        }

        /* add final condition */
        phi[i] = lhs[i].LT(rhs[i]);

        /* add optimized chain to disjunction */
        pred = pred.Or( book_and_chain(phi, 1 + i));
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

    /* MSB predicate first, if false and prefix matches, inspect next
       digit. */
    ADD pred = f_enc.zero();
    for (unsigned i = 0; i < width; ++ i) {

        ADD phi[1 + i];

        /* prefix */
        for (unsigned j = 0; j < i; j ++ ) {
            phi[j] = rhs[j].Equals(lhs[j]);
        }

        /* add final condition */
        phi[i] = lhs[i].LEQ(rhs[i]);

        /* add optimized chain to disjunction */
        pred = pred.Or( book_and_chain(phi, 1 + i));
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
    POP_ALGEBRAIC(index, itype -> size());

    // argh! this breaks octals.. :-/
    assert( itype -> size() * f_enc.bits_per_digit() == f_enc.word_width());

    // array
    Type_ptr t1 = f_type_stack.back(); f_type_stack.pop_back(); // consume array
    assert( t1 -> is_array());
    ArrayType_ptr atype = t1 -> as_array();
    unsigned elem_size  = atype -> of() -> size();
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
