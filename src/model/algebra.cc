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
 *  compilation must be a 0-1 ADD which is suitable for CNF clauses
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

void BECompiler::algebraic_neg(const Expr_ptr expr)
{
    assert( is_unary_algebraic(expr) );
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    const Type_ptr type = f_type_stack.back(); // just inspect
    unsigned width = tm.as_algebraic(type)->width();

    /* create temp complemented ADDs */
    ADD dds[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        dds[i] = f_add_stack.back().Cmpl(); f_add_stack.pop_back();
    }
    FQExpr temp = make_temporary_encoding(dds, width);

    /* type stack is untouched because the argument is already algebraic */
    (*this)(em.make_add(temp.expr(), em.make_one()));
}

void BECompiler::algebraic_not(const Expr_ptr expr)
{
    assert( is_unary_algebraic(expr) );
    TypeMgr& tm = f_owner.tm();

    const Type_ptr type = f_type_stack.back(); // just inspect
    unsigned width = tm.as_algebraic(type)->width();

    ADD lhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (int i = width -1; (0 <= i); -- i) {
        /* ! x[i] */
        ADD tmp = lhs[i].Cmpl();
        f_add_stack.push_back(tmp);
    }
}

void BECompiler::algebraic_plus(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    int width = algebrize_ops_binary(); // largest, takes care of type stack

    ADD rhs[width];
    for (int i = 0; i < width ; ++ i) {
        rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD lhs[width];
    for (int i = 0; i < width ; ++ i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform arithmetic sum using positional algorithm */
    ADD carry = f_enc.zero();
    for (int i = width -1; (0 <= i); -- i) {

        /* x[i] + y[i] + c */
        ADD tmp = lhs[i].Plus(rhs[i]).Plus(carry);
        carry = f_enc.base().LEQ(tmp); /* c >= 0x10 */

        /* x[i] = (x[i] + y[i] + c) % base */ // TODO: detect overflow on MSB
        f_add_stack.push_back(tmp.Modulus(f_enc.base()));
    }
}

void BECompiler::algebraic_sub(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );

    ExprMgr& em = f_owner.em();
    (*this)(em.make_add(expr->lhs(), em.make_neg(expr->rhs())));
}

void BECompiler::algebraic_mul(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned pos, width = algebrize_ops_binary(); // largest, takes care of type stack

    ADD rhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD lhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD res[width];
    for (int i = width -1; 0 <= i; -- i) {
        res[i] = f_enc.zero();
    }

    ADD tmp[width];
    for (int i = width -1; 0 <= i; -- i) {
        tmp[i] = f_enc.zero();
    }

    ADD carry = f_enc.zero();

    for (int i = width -1; 0 <= i; -- i) {
        for (int j = width -1; 0 <= j; -- j) {

            // ignore what happend out of result boundaries
            if (0 <= (pos = width - i - j)) {

                /* build mul table for digit product */
                ADD product = lhs[i].Times(rhs[j]).Plus(carry);

                tmp[pos] = product.Modulus(f_enc.base());
                carry = product.Divide(f_enc.base());
            }
        }

        // update result
        for (int j = width -1; i <= j; -- j) {
            res[j] += tmp[j];
        }

        // return i-th digit of result
        f_add_stack.push_back(res[i]);
    }
}

void BECompiler::algebraic_div(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    assert( false ); // TODO
}

void BECompiler::algebraic_mod(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    assert( false ); // TODO
}

void BECompiler::algebraic_and(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_ops_binary(); // largest


    ADD rhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD lhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (int i = width -1; (0 <= i); -- i) {

        /* x[i] &  y[i] */
        ADD tmp = lhs[i].BWTimes(rhs[i]);
        f_add_stack.push_back(tmp);
    }
}

void BECompiler::algebraic_or(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_ops_binary(); // largest

    ADD rhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD lhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (int i = width -1; (0 <= i); -- i) {

        /* x[i] &  y[i] */
        ADD tmp = lhs[i].BWOr(rhs[i]);
        f_add_stack.push_back(tmp);
    }
}

void BECompiler::algebraic_xor(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_ops_binary(); // largest

    ADD rhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD lhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (int i = width -1; (0 <= i); -- i) {

        /* x[i] &  y[i] */
        ADD tmp = lhs[i].BWXor(rhs[i]);
        f_add_stack.push_back(tmp);
    }
}

void BECompiler::algebraic_xnor(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_ops_binary(); // largest

    ADD rhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD lhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (int i = width -1; (0 <= i); -- i) {

        /* x[i] &  y[i] */
        ADD tmp = lhs[i].BWXnor(rhs[i]);
        f_add_stack.push_back(tmp);
    }
}

void BECompiler::algebraic_implies(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_ops_binary(); // largest

    ADD rhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD lhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (int i = width -1; (0 <= i); -- i) {

        /* x[i] &  y[i] */
        ADD tmp = lhs[i].BWCmpl().BWOr(rhs[i]);
        f_add_stack.push_back(tmp);
    }
}

void BECompiler::algebraic_lshift(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_ops_binary(); // largest

    ADD rhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD lhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (int i = width -1; (0 <= i); -- i) {

        /* x[i] &  y[i] */
        ADD tmp = lhs[i].BWCmpl().BWXor(rhs[i]);
        f_add_stack.push_back(tmp);
    }
}

void BECompiler::algebraic_rshift(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    assert( 0 ); // TODO: yet to be implemented...
}

void BECompiler::algebraic_equals(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_ops_binary(); // largest

    ADD rhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD lhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, similar to xnor, only conjuct res */
    ADD tmp = f_enc.one();
    for (int i = width -1; (0 <= i); -- i) {

        /* x[i] &  y[i] */
        tmp *= lhs[i].Equals(rhs[i]);
    }

    /* just one result */
    f_add_stack.push_back(tmp);
}

void BECompiler::algebraic_not_equals(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_ops_binary(); // largest

    ADD rhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD lhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, similar to xnor, only conjuct res */
    ADD tmp = f_enc.one();
    for (int i = width; (0 <= i); -- i) {

        /* x[i] &  y[i] */
        tmp *= lhs[i].Equals(rhs[i]);
    }

    /* just one result */
    f_add_stack.push_back(tmp.Cmpl());
}

void BECompiler::algebraic_gt(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_ops_binary(); // largest

    ADD rhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD lhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* relationals, msb predicate first, if false inspect next digit ... */
    ADD tmp = f_enc.zero();
    for (int i = width -1; (0 <= i); -- i) {

        /* x[i] &  y[i] */
        tmp += rhs[i].LT(lhs[i]); // CHECK MSB
    }

    /* just one result */
    f_add_stack.push_back(tmp);
}

void BECompiler::algebraic_ge(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_ops_binary(); // largest

    ADD rhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD lhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* relationals, msb predicate first, if false inspect next digit ... */
    ADD tmp = f_enc.zero();
    for (int i = width -1; (0 <= i); -- i) {

        /* x[i] &  y[i] */
        tmp += rhs[i].LEQ(lhs[i]); // CHECK MSB
    }

    /* just one result */
    f_add_stack.push_back(tmp);
}

void BECompiler::algebraic_lt(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_ops_binary(); // largest

    ADD rhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD lhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* relationals, msb predicate first, if false inspect next digit ... */
    ADD tmp = f_enc.zero();
    for (int i = width -1; (0 <= i); -- i) {

        /* x[i] &  y[i] */
        tmp += lhs[i].LT(rhs[i]); // CHECK MSB
    }

    /* just one result */
    f_add_stack.push_back(tmp);
}

void BECompiler::algebraic_le(const Expr_ptr expr)
{
    assert( is_binary_algebraic(expr) );
    unsigned width = algebrize_ops_binary(); // largest

    ADD rhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD lhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* relationals, msb predicate first, if false inspect next digit ... */
    ADD tmp = f_enc.zero();
    for (int i = width -1; (0 <= i); -- i) {

        /* x[i] &  y[i] */
        tmp += lhs[i].LEQ(rhs[i]); // CHECK MSB
    }

    /* just one result */
    f_add_stack.push_back(tmp);
}

// TODO fix type stack
void BECompiler::algebraic_ite(const Expr_ptr expr)
{
    assert(is_ite_algebraic(expr));
    unsigned width = algebrize_ops_binary(); // largest

    ADD rhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD lhs[width];
    for (int i = width -1; (0 <= i) ; -- i) {
        lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    const ADD c = f_add_stack.back(); f_add_stack.pop_back();

    /* multiplex, easy as pie :-) */
    for (int i = width -1; (0 <= i); -- i) {
        f_add_stack.push_back(c.Ite(lhs[i], rhs[i]));
    }
}

// REMARK: algebrizations makes sense only for binary ops, there is no
// need to algebrize a single operand! (unless casts are introduced,
// but then again a CAST can be thought as a binary op...[ CAST 8 x ])

/* This is slightly complex: it fetches 2 ops, one of them must be
   algebraic, possibly both. Performs integer to algebraic
   conversion if needed, aligns algebraic operands to the largest
   size, and return this size. */
unsigned BECompiler::algebrize_ops_binary()
{
    TypeMgr& tm = f_owner.tm();

    unsigned stack_size = f_type_stack.size();
    assert (2 <= stack_size);

    const Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();
    const Type_ptr lhs_type = f_type_stack.back(); f_type_stack.pop_back();

    assert( tm.is_algebraic(rhs_type) || tm.is_algebraic(lhs_type) );
    unsigned rhs_width = tm.is_algebraic(rhs_type)
        ? tm.as_algebraic(rhs_type)->width()
        : 0;

    unsigned lhs_width = tm.is_algebraic(lhs_type)
        ? tm.as_algebraic(lhs_type)->width()
        : 0;

    /* max */
    unsigned res = rhs_width < lhs_width
        ? lhs_width
        : rhs_width
        ;

    /* perform conversion or padding, taking sign bit into account */
    if (rhs_width < res) {
        if (! rhs_width) { // integer, conversion required
            algebraic_from_integer(res);
        }
        else { // just padding required
            bool is_signed = tm.as_algebraic(rhs_type)->is_signed();
            algebraic_padding(rhs_width, res, is_signed);
        }

        // push other operand's type
        f_type_stack.push_back(lhs_type);
    }

    if (lhs_width < res) {
        if (! lhs_width) { // integer, conversion required
            algebraic_from_integer(res);
        }
        else { // just padding required
            bool is_signed = tm.as_algebraic(lhs_type)->is_signed();
            algebraic_padding(lhs_width, res, is_signed);
        }

        // push other operand's type
        f_type_stack.push_back(rhs_type);
    }

    // fix the type stack
    if ((rhs_width == res) && (lhs_width == res)) {
        f_type_stack.push_back(rhs_type); // arbitrary
    }

    assert( stack_size - 1 == f_type_stack.size());
    return res;
}

// due to new type system, integer can be only constant (good)
void BECompiler::algebraic_from_integer(unsigned width)
{
    const ADD top = f_add_stack.back(); f_add_stack.pop_back();
    assert (f_enc.is_constant(top));

    value_t value = f_enc.const_value(top);

    unsigned base = Cudd_V(f_enc.base().getNode());

    for (int i = width -1; (0 <= i); -- i) {
        ADD digit = f_enc.constant(value % base);
        f_add_stack.push_back(digit);
        value /= base;
    }

    assert (value == 0); // not overflowing
}

void BECompiler::algebraic_padding(unsigned old_width, unsigned new_width, bool is_signed)
{
    ADD padding = f_enc.zero();
    ADD zero = f_enc.zero();

    assert (old_width < new_width); // old is smaller than new

    ADD tmp[old_width];
    for (int i = old_width -1; (0 <= i) ; -- i) {
        tmp[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    // sign extension predicate (0x00 or 0xFF?) only if required.
    if (is_signed) {
        padding += tmp[0].BWTimes(f_enc.msb()).Equals(zero).Ite(zero, f_enc.full());
    }

    for (int i = new_width - old_width /* -1 + 1 */; (0 <= i); -- i) {
        f_add_stack.push_back(padding);
    }
    for (int i = old_width -1; (0 <= i); -- i) {
        f_add_stack.push_back(tmp[i]);
    }
}

FQExpr BECompiler::make_temporary_encoding(ADD dds[], unsigned width)
{
    ExprMgr& em = f_owner.em();

    ostringstream oss;
    oss << "__tmp" << f_temp_auto_index ++ ;

    Expr_ptr expr = em.make_identifier(oss.str());
    IEncoding_ptr enc = new AlgebraicEncoding(width, false, dds);
    FQExpr key(expr);

    register_temporary( key, enc);
    return key;
}

// Resolution for temp symbols
ISymbol_ptr BECompiler::fetch_temporary(const Expr_ptr expr, step_t time)
{
    FQExpr key(ExprMgr::INSTANCE().make_main(), expr, time);
    Temporaries::iterator viter = f_temporaries.find(key);
    if (viter != f_temporaries.end()) {
        return (*viter).second;
    }

    return NULL; // not found
}
