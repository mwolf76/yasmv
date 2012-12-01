/**
 *  @file compiler.cc
 *  @brief Boolean compiler
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

// comment this out to disable debug
// #define DEBUG_COMPILER

// comment this out to disable benchmarking
#define BENCHMARK_COMPILER

#include <common.hh>

#include <expr.hh>
#include <compiler.hh>

Compiler::Compiler()
    : f_temp_auto_index(0)
    , f_map()
    , f_type_stack()
    , f_add_stack()
    , f_ctx_stack()
    , f_owner(ModelMgr::INSTANCE())
    , f_enc(EncodingMgr::INSTANCE())
{ DEBUG << "Created Compiler @" << this << endl; }

Compiler::~Compiler()
{ DEBUG << "Destroying Compiler @" << this << endl; }

ADD Compiler::process(Expr_ptr ctx, Expr_ptr body, step_t time = 0)
{
    // remove previous results
    f_add_stack.clear();
    f_type_stack.clear();
    f_ctx_stack.clear();
    f_time_stack.clear();

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);
    f_time_stack.push_back(time);

    FQExpr key(ctx, body, time);
    TRACE << "Compiling " << key << endl;

    // invoke walker on the body of the expr to be processed
    (*this)(body);

    // Just one 0-1 ADD returned. This is ok, because the compiler is
    // supposed to return a boolean formula, suitable for CNF
    // conversion. This condition is checked by the post-hook method.
    return f_add_stack.back();
}

void Compiler::pre_hook()
{
#ifdef BENCHMARK_COMPILER
    f_elapsed = clock();
#endif
}

void Compiler::post_hook()
{
    if (0 < f_recursion_stack.size()) return;

    ADD add = f_add_stack.back();
    assert( add.FindMin().Equals(f_enc.zero()) );
    assert( add.FindMax().Equals(f_enc.one()) );

    // sanity conditions
    assert(1 == f_add_stack.size());
    assert(1 == f_type_stack.size());
    assert(1 == f_ctx_stack.size());
    assert(1 == f_time_stack.size());

#ifdef BENCHMARK_COMPILER
    f_elapsed = clock() - f_elapsed;
    double secs = (double) f_elapsed / (double) CLOCKS_PER_SEC;
    TRACE << "Took " << secs << " seconds" << endl;
#endif

#ifdef DEBUG_COMPILER
    cout << "Result: " << endl;
    add.PrintMinterm();
    cout << endl;
#endif
}

bool Compiler::walk_next_preorder(const Expr_ptr expr)
{
    step_t curr_time = f_time_stack.back();
    f_time_stack.push_back(1 + curr_time);
    return true;
}
void Compiler::walk_next_postorder(const Expr_ptr expr)
{
    f_time_stack.pop_back(); // reset time stack
}

bool Compiler::walk_neg_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Compiler::walk_neg_postorder(const Expr_ptr expr)
{
    if (is_unary_integer(expr)) {
        const ADD top = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(top.Negate());
        return;
    }
    else if (is_unary_algebraic(expr)) {
        algebraic_neg(expr);
        return;
    }

    assert( false ); // unreachable
}

bool Compiler::walk_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Compiler::walk_not_postorder(const Expr_ptr expr)
{
    if (is_unary_boolean(expr)) {
        const ADD top = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(top.Cmpl());
        return;
    }
    else if (is_unary_algebraic(expr)) {
        algebraic_not(expr); // bitwise
        return;
    }

    assert(false); // unreachable
}

bool Compiler::walk_add_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_add_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_add_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Plus(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_plus(expr);
        return;
    }

    assert( false ); // unreachable
}

bool Compiler::walk_sub_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_sub_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_sub_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Minus(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_sub(expr);
        return;
    }

    assert( false ); // unexpected
}

bool Compiler::walk_div_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_div_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_div_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Divide(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_div(expr);
        return;
    }

    assert( false ); // unexpected
}

bool Compiler::walk_mul_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_mul_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_mul_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Times(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }


    else if (is_binary_algebraic(expr)) {
        algebraic_mul(expr);
        return;
    }

    assert( false ); // unreachable
}

bool Compiler::walk_mod_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_mod_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_mod_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Modulus(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_mod(expr);
        return;
    }

    assert( false ); // unreachable
}

bool Compiler::walk_and_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_and_postorder(const Expr_ptr expr)
{
    if (is_binary_boolean(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Times(rhs)); /* 0, 1 logic uses arithmetic product */
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.BWTimes(rhs)); /* bitwise integer arithmetic */
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_and(expr); // bitwise
        return;
    }

    assert( false ); // unreachable
}

bool Compiler::walk_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_or_postorder(const Expr_ptr expr)
{
    if (is_binary_boolean(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Or(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.BWOr(rhs)); /* bitwise integer arithmetic */
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_or(expr);
        return;
    }
}

bool Compiler::walk_xor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_xor_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_xor_postorder(const Expr_ptr expr)
{
    if (is_binary_boolean(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Xor(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.BWXor(rhs)); /* bitwise integer arithmetic */
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_xor(expr);
        return;
    }

    assert( false ); // unreachable
}

bool Compiler::walk_xnor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_xnor_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_xnor_postorder(const Expr_ptr expr)
{
    if (is_binary_boolean(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Xnor(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.BWXnor(rhs)); /* bitwise integer arithmetic */
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_xnor(expr);
        return;
    }

    assert( false ); // unreachable
}

bool Compiler::walk_implies_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_implies_postorder(const Expr_ptr expr)
{
    if (is_binary_boolean(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Cmpl().Or(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.BWCmpl().BWXor(rhs)); /* bitwise integer arithmetic */
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_implies(expr);
        return;
    }

    assert( false ); // unreachable
}

bool Compiler::walk_iff_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_iff_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_iff_postorder(const Expr_ptr expr)
{ /* just a fancy name for xnor :-) */ walk_xnor_postorder(expr); }

bool Compiler::walk_lshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_lshift_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_lshift_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.LShift(rhs)); /* bitwise integer arithmetic */
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }
    else if (is_binary_algebraic(expr)) {
        algebraic_lshift(expr);
        return;
    }

    assert( false ); // unreachable
}

bool Compiler::walk_rshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_rshift_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_rshift_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.RShift(rhs)); /* bitwise integer arithmetic */
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }
    else if (is_binary_algebraic(expr)) {
        algebraic_rshift(expr);
        return;
    }

    assert( false ); // unreachable
}

bool Compiler::walk_eq_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_eq_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_eq_postorder(const Expr_ptr expr)
{
    if (is_binary_boolean(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Equals(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_integer(expr) ||
             is_binary_enumerative(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Equals(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_equals(expr);
        return;
    }

    assert( false ); // unreachable
}

bool Compiler::walk_ne_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_ne_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_ne_postorder(const Expr_ptr expr)
{
    if (is_binary_boolean(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Equals(rhs).Cmpl());
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_integer(expr) ||
             is_binary_enumerative(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Equals(rhs).Cmpl());
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_not_equals(expr);
        return;
    }

    assert( false ); // unreachable
}

bool Compiler::walk_gt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_gt_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_gt_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(rhs.LT(lhs)); // simulate GT op
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_gt(expr);
        return;
    }
    else assert( false );
}

bool Compiler::walk_ge_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_ge_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_ge_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(rhs.LEQ(lhs)); // simulate GEQ op
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_ge(expr);
        return;
    }

    assert( false ); // unreachable
}

bool Compiler::walk_lt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_lt_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_lt_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.LT(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_lt(expr);
        return;
    }

    assert( false ); // unreachable
}

bool Compiler::walk_le_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_le_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_le_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.LEQ(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_le(expr);
        return;
    }

    assert( false ); // unreachable
}

bool Compiler::walk_ite_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_ite_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_ite_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    if (is_ite_boolean(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD c = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(c.Ite(lhs, rhs));

        f_type_stack.pop_back();
        f_type_stack.pop_back(); // consume two, leave the third
        return;
    }

    else if (is_ite_integer(expr)) {
        integer_ite(expr);
        return;
    }

    else if (is_ite_enumerative(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD c = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(c.Ite(lhs, rhs));

        f_type_stack.pop_back();
        f_type_stack.pop_back();
        f_type_stack.pop_back(); // consume all, push integer
        f_type_stack.push_back(tm.find_integer());
        return;
    }

    else if (is_ite_algebraic(expr)) {
        algebraic_ite(expr);
        return;
    }

    assert( false ); // unreachable
 }

bool Compiler::walk_cond_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_cond_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_cond_postorder(const Expr_ptr expr)
{ /* nop */ }

bool Compiler::walk_dot_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_dot_inorder(const Expr_ptr expr)
{
    // ADD tmp = f_add_stack.back();
    // Expr_ptr ctx = tmp->get_repr();
    // f_ctx_stack.push_back(ctx);
    return true;
}
void Compiler::walk_dot_postorder(const Expr_ptr expr)
{
    ADD rhs_add;

    // { // RHS, no checks necessary/possible
    //     const ADD top = f_add_stack.back(); f_add_stack.pop_back();
    //     rhs_add = top;
    // }

    // { // LHS, must be an instance (by assertion, otherwise leaf would have fail)
    //     const ADD top = f_add_stack.back(); f_add_stack.pop_back();
    //     assert(tm.is_instance(top));
    // }

    // // propagate rhs add
    // f_add_stack.push_back(rhs_add);

    // // restore previous ctx
    // f_ctx_stack.pop_back();
}

bool Compiler::walk_subscript_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_subscript_inorder(const Expr_ptr expr)
{ return true; }

/* Array selector builder: for arrays subscription, a chain of ITE is
   built out of the encodings for each element which are assumed to be
   present in dd stack in reversed order (walk_leaf took care of
   this). */
void Compiler::walk_subscript_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();
    unsigned base = Cudd_V(f_enc.base().getNode());

    const Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();

    /* algebrize selection expr (rhs), using machine width */
    assert (tm.is_integer(rhs_type) || tm.is_algebraic(rhs_type));
    algebrize_unary();

    ADD selector[2]; // TODO
    for (unsigned i = 0; i < 2; ++ i) {
        selector[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    const Type_ptr lhs_type = f_type_stack.back(); f_type_stack.pop_back();

    unsigned size = tm.as_array(lhs_type)->size();

    const Type_ptr scalar_type = tm.as_array(lhs_type)->of();
    unsigned width = tm.is_algebraic(scalar_type)
        ? tm.as_algebraic(rhs_type)->width()
        : 1; /* monolithics, consts, enum, etc... use just 1 DD */
    ;

    /* fetch DDs from the stack */
    ADD dds[width * size];
    for (unsigned i = 0; i < width * size; ++ i) {
        dds[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD res; /* one digit at a time */
    for (unsigned i = 0; i < width; ++ i) {
        unsigned ndx = width - i - 1;
        res = f_enc.zero(); // TODO: FAILURE here

        for (unsigned j = 0; j < size; ++ j) {

            /* selected index */
            unsigned selection = size - j -1;

            ADD cond = f_enc.one();
            value_t value = ndx;

            /* encode the case selection as a conjunction of
               Equals ADD digit-by-digit (inlined) */
            for (unsigned k = 0; k < width; ++ k) {

                ADD digit = f_enc.constant(value % base);
                f_add_stack.push_back(digit);
                value /= base;

                /* case selection */
                cond *= selector[ndx].Equals(digit);
            }
            assert (value == 0); // not overflowing

            /* chaining */
            res = cond.Ite( dds[width * selection + i], res);
        }

        f_add_stack.push_back(res);
    }
}

/* private service of walk_leaf */
void Compiler::push_variable(IEncoding_ptr enc, Type_ptr type)
{
    TypeMgr& tm = f_owner.tm();

    assert (NULL != enc);
    DDVector& dds = enc->dv();
    unsigned width = dds.size();

    // push into type stack
    f_type_stack.push_back(type);

    /* booleans, constants, monoliths are just one DD */
    if (tm.is_boolean(type)
        || tm.is_integer(type)
        || tm.is_enum(type)) {
        assert(1 == width);
        f_add_stack.push_back(dds[0]);
    }

    /* arrays and algebraics, reversed list of encoding DDs */
    else if (tm.is_algebraic(type)
             || (tm.is_array(type))) {
        // assert( tm.as_algebraic(type)->width() == width ); // type and enc width info has to match
        for (DDVector::reverse_iterator ri = dds.rbegin();
             ri != dds.rend(); ++ ri) {
            f_add_stack.push_back(*ri);
        }
    }

    else assert( false ); // unexpected
}

void Compiler::walk_leaf(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* cached? */
    if (! cache_miss(expr)) return;

    // symb resolution
    // Model& model = static_cast <Model&> (*f_owner.model());
    IResolver& resolver = * f_owner.resolver();

    Expr_ptr ctx = f_ctx_stack.back();
    step_t time = f_time_stack.back();

    ENCMap::iterator eye;
    IEncoding_ptr enc = NULL;

    // 1. explicit constants are integer ints (e.g. 42)
    if (em.is_numeric(expr)) {
        f_type_stack.push_back(tm.find_integer()); // consts
        f_add_stack.push_back(f_enc.constant(expr->value()));
        return;
    }

    // 2. Symbols
    ISymbol_ptr symb = resolver.fetch_symbol(ctx, expr);

    // 2. 1. Temporary symbols are maintained internally by the compiler
    ITemporary_ptr temp;
    if (NULL != (temp = dynamic_cast<ITemporary_ptr>(symb))) {
        Type_ptr type = NULL;

        type = symb->as_variable().type();
        assert(tm.is_algebraic(type));

        // temporary encodings must be already defined.
        FQExpr key(ExprMgr::INSTANCE().make_main(), expr, time);

        ENCMap::iterator eye = f_temp_encodings.find(key);
        if (eye != f_temp_encodings.end()) {
            enc = (*eye).second;
        }
        else assert(false); // unexpected

        push_variable(enc, type);
        return;
    } /* Temporary symbols */

    // 2. 2. Model symbol
    if (NULL != symb) {
        Type_ptr type = NULL;

        // 2. 2. 1. bool/integer constant leaves
        if (symb->is_const()) {
            IConstant& konst =  symb->as_const();

            f_type_stack.push_back(konst.type());
            f_add_stack.push_back(f_enc.constant(konst.value()));
            return;
        }

        // 2. 2. 2. variables
        else if (symb->is_variable()) {

            // push into type stack
            type = symb->as_variable().type();

            // if encoding for variable is available reuse it,
            // otherwise create and cache it.
            FQExpr key(ctx, expr, time);

            /* build a new encoding for this symbol if none is available */
            if (NULL == (enc = f_enc.find_encoding(key))) {
                enc = f_enc.make_encoding(type);
                f_enc.register_encoding(key, enc);
            }

            push_variable(enc, type);
            return;
        } /* variables */

        // 2. 3. define? Simply compile it recursively.
        else if (symb->is_define()) {
            (*this)(symb->as_define().body());
            return;
        }
    }  /* Model symbols */

    assert( false ); // unreachable
}
