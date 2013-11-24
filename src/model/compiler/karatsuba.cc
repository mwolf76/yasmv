/**
 *  @file karatsuba.cc
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

#if 0
/* Important Remark: operand arguments (which are DD vectors) are
   fetched from the internal DD stack in a big-endian fashion, that is
   MSB first. On the other hand, to ensure proper behavior the
   *result* of the operation has to be pushed in reverse order. */

static inline bool is_even (unsigned int x)
{ return (0 == (x & 1)); }

void Compiler::karatsuba(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_binary_arithmetical();

    karatsuba_aux(width);

    /* Throw away the most significant digits */
    for (unsigned i = 0; i < width; ++ i) {
        f_add_stack.pop_back();
    }
}

void Compiler::karatsuba_add_high_and_low(unsigned width)
{
    ADD carry = f_enc.zero();

    unsigned half = width/2;
    assert(is_even(half));

    // half digits
    for (unsigned i = 0; i < half; ++ i) {

        /* x[i] + x[i + m/2] + c */
        unsigned ndx = width - i - 1;
        ADD tmp = rhs[ndx].Plus( rhs[ndx - half]).Plus(carry);

        carry = f_enc.base().LEQ(tmp); /* c >= 0x10 */
        PUSH_ADD(tmp.Modulus(f_enc.base()));
    }

    // half digits
    PUSH_ADD(carry);
    for (unsigned i = 1; i < half; ++ i) {
        PUSH_ADD(f_enc.zero());
    }
}


void Compiler::karatsuba_aux(unsigned width)
{
    ADD carry;

    /* Base case, use long multiplication algorithm as a fallback. */
    if (width < 4) {
        long_mul(m, true); // yields 2m number
        return;
    }

    /* -- 1. Fetch input ADDs ------------------------------------------------- */

    // Fetch RHS ADDs and add zero-padding to 2m digits
    ADD rhs[2 * width];
    for (unsigned i = 0; i < width ; ++ i) {
        rhs[i] = f_enc.zero();
        rhs[i + width] = f_add_stack.back();
        f_add_stack.pop_back();
    }

    // Fetch RHS ADDs and add zero-padding to 2m digits
    ADD lhs[2 * width];
    for (unsigned i = 0; i < width ; ++ i) {
        lhs[i] = f_enc.zero();
        lhs[i + width] = f_add_stack.back();
        f_add_stack.pop_back();
    }

    /* -- 2. Divide ----------------------------------------------------------- */

    /* if width is odd, the leftmost half has an odd nummber of
       digits, rightmost half always has an even number of digits. */
    unsigned low_half = width / 2;
    if (width & 1) {
        ++ low_half;
    }

    /* -- 2.1. z0 = K( Al, Bl, width) */
    for (unsigned i = 0; i < low_half; ++ i) {
        unsigned ndx = width - i - 1;
        PUSH_ADD( rhs[ndx]);
    }
    for (unsigned i = 0; i < low_half; ++ i) {
        unsigned ndx = width - i - 1;
        PUSH_ADD( lhs[ndx]);
    }
    karatsuba_mul_aux(low_half, true); // yields 2 * low_half digits
    ADD z0[2 * width];
    {
        unsigned i = 0;
        while (i < low_half) {
            z0[width + i] = f_add_stack.back();
            f_add_stack.pop_back();
            ++ i;
        }
        while (i < width) {
            z0[width + i] = f_enc.zero();
            ++ i;
        }
    }

    /* -- 2.3. z2 = K( Ah, Bh, width) */
    for (unsigned i = 1 + low_half; i < width; ++ i) {
        unsigned ndx = i - 1;
        PUSH_ADD( rhs[ndx]);
    }
    for (unsigned i = 1 + low_half; i < width; ++ i) {
        unsigned ndx = i - 1;
        PUSH_ADD( lhs[ndx]);
    }
    karatsuba_mul_aux(half, true); // yields 2 * hi_half digits
    ADD z2[2 * width];
    {
        unsigned i = 0;
        while (i < low_half) {
            z2[width + i] = f_enc.zero();
            ++ i;
        }
        while (i < width) {
            z2[width + i] = f_add_stack.back();
            f_add_stack.pop_back();
            ++ i;
        }
    }

    /* -- 2.4. z1 = K( Ah+Al, Bh+Bl, m/2), yields an (m + 2) digits number */
    for (unsigned i = 0; i < width; ++ i) {
        unsigned ndx = width - i - 1;
        PUSH_ADD( rhs[ndx] );
    }
    karatsuba_add_high_and_low(width); // yields m + 1 digits number
    ADD A[1 + width];
    for (unsigned i = 0; i < width ; ++ i) {
        rhs[i] = f_enc.zero();
        rhs[i + width] = f_add_stack.back();
        f_add_stack.pop_back();
    }
    A[width-1] = f_add_stack.back(); // carry
    f_add_stack.pop_back();
    for (unsigned i = 1; i < width ; ++ i) {
        A[i] = f_enc.zero();
    }

    for (unsigned i = 0; i < width; ++ i) {
        unsigned ndx = width - i - 1;
        PUSH_ADD( lhs[ndx] );
    }
    karatsuba_add_high_and_low(width); // yields m + 1 digits number, padded to 2m
    ADD B[2 * width];
    for (unsigned i = 0; i < width ; ++ i) {
        rhs[i] = f_enc.zero();
        rhs[i + width] = f_add_stack.back();
        f_add_stack.pop_back();
    }
    B[width-1] = f_add_stack.back(); // carry
    f_add_stack.pop_back();
    for (unsigned i = 1; i < width ; ++ i) {
        B[i] = f_enc.zero();
    }
    karatsuba_mul_aux(2 * width, true);

    ADD carry = f_enc.zero();
    for (unsigned i = 0; i < m/2; ++ i) {

        /* x[i] + y[i + m/2] + c */
        unsigned ndx = width - i - 1;
        ADD tmp = lhs[ndx].Plus(lhs[ndx - m/2]).Plus(carry);
        carry = f_enc.base().LEQ(tmp); /* c >= 0x10 */

        /* x[i] = (x[i] + y[i] + c) % base */
        PUSH_ADD(tmp.Modulus(f_enc.base()));
    }
    PUSH_ADD(carry);

    karatsuba(m/2+1, true); // yields an m+2 digits number
    POP_ALGEBRAIC(z1, m+2);


    /* 4. COMBINE: AxB := z2 * B^m + ... */
    {
        for (unsigned i = 0; i < m; ++ i) {
            PUSH_ADD(f_enc.zero());
        }
        for (i = 0; i < m; ++ i) {
            unsigned ndx = width - i - 1;
            PUSH_ADD( z2 [ndx]);
        }

        /* ... + (z1 - (z2 + z0)) * B^(m/2) ... */
        for (unsigned i = 0; i < m/2; ++ i) {
            PUSH_ADD(f_enc.zero());
        }
        { // (z2 + z0) (both m digits numbers)
            ADD carry = f_enc.zero();

            // m digits
            for (unsigned i = 0; i < m; ++ i) {

                /* x[i] + y[i + m/2] + c */
                unsigned ndx = width - i - 1;
                ADD tmp = z1[ndx].Sub(z0[ndx]).Sub(z2[ndx]).Plus(carry)

                    carry = f_enc.base().LEQ(tmp); /* c >= 0x10 */

                /* x[i] = (x[i] + y[i] + c) % base */
                PUSH_ADD(tmp.Modulus(f_enc.base()));
            }

            // m digits
            PUSH_ADD(carry);
            for (unsigned i = 1; i < m; ++ i) {
                PUSH_ADD(f_enc.zero());
            }
        }

        /* + z0 */
        for (i = 0; i < m; ++ i) {
            unsigned ndx = width - i - 1;
            PUSH_ADD( z0 [ndx]);
        }
        for (unsigned i = 0; i < m; ++ i) {
            PUSH_ADD(f_enc.zero());
        }

        /* We've got three operands here, all of which have 2m digits: A,
           B, C. On the first cycle, we add A and B and push the temp
           result on the stack. On the second cycle, we fetch temp result
           and operand C from the stack and add them together. */
        for (unsigned c = 0; c < 2; ++ c) {
            POP_ALGEBRAIC( lhs, 2 * m);
            POP_ALGEBRAIC( rhs, 2 * m);

            {
                ADD carry = f_enc.zero();
                for (unsigned i = 0; i < m*2; ++ i) {

                    /* x[i] + y[i] + c */
                    unsigned ndx = 2 * m - i - 1;
                    ADD tmp = lhs[ndx].Plus( rhs[ndx]).Plus(carry);
                    carry = f_enc.base().LEQ(tmp); /* c >= 0x10 */

                    /* x[i] = (x[i] + y[i] + c) % base */
                    PUSH_ADD(tmp.Modulus(f_enc.base()));
                }
                PUSH_ADD(carry);
            }
        }
    }
}
#endif
