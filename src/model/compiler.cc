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

#include <common.hh>

#include <expr.hh>
#include <compiler.hh>

// comment this out
// #define DEBUG_BE_COMPILER

BECompiler::BECompiler()
    : f_map()
    , f_type_stack()
    , f_add_stack()
    , f_ctx_stack()
    , f_owner(ModelMgr::INSTANCE())
    , f_enc(EncodingMgr::INSTANCE())
{ DEBUG << "Created BECompiler @" << this << endl; }

BECompiler::~BECompiler()
{ DEBUG << "Destroying BECompiler @" << this << endl; }

ADD BECompiler::process(Expr_ptr ctx, Expr_ptr body, step_t time = 0)
{
    // remove previous results
    f_add_stack.clear();
    f_type_stack.clear();
    f_ctx_stack.clear();
    f_time_stack.clear();

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);
    f_time_stack.push_back(time);

    DEBUG << "Compiling boolean expression "
          << "(time = " << time << ") "
          << ctx << "::" << body
          << endl;

    // invoke walker on the body of the expr to be processed
    (*this)(body);

    // sanity conditions
    assert(1 == f_add_stack.size());
    assert(1 == f_type_stack.size());
    assert(1 == f_ctx_stack.size());
    assert(1 == f_time_stack.size());

    // Just one add returned. This is ok, because the compiler is
    // supposed to return a boolean formula.
    ADD add = f_add_stack.back();
    return add;
}

void BECompiler::pre_hook()
{}
void BECompiler::post_hook()
{
    ADD add = f_add_stack.back();
    assert( add.FindMin() == f_enc.zero() );
    assert( add.FindMax() == f_enc.one() );
}

bool BECompiler::walk_next_preorder(const Expr_ptr expr)
{
    step_t curr_time = f_time_stack.back();
    f_time_stack.push_back(1 + curr_time);
    return true;
}
void BECompiler::walk_next_postorder(const Expr_ptr expr)
{
    f_time_stack.pop_back(); // reset time stack
}

bool BECompiler::walk_neg_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void BECompiler::walk_neg_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    if (is_unary_integer(expr)) {
        const ADD top = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(top.Negate());
        return;
    }
    else if (is_unary_algebraic(expr)) {
        const Type_ptr rhs_type = f_type_stack.back(); // just inspect
        unsigned i, width = tm.as_int_algebraic(rhs_type)->width();

        ADD* lhs[width];
        for (i = width; (i) ; -- i) {
            *lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
        }

        algebraic_neg();
        return;
    }

    assert(0); // unreachable
}

bool BECompiler::walk_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void BECompiler::walk_not_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    if (is_unary_boolean(expr)) {
        const ADD top = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(top.Cmpl());
        return;
    }
    else if (is_unary_algebraic(expr)) {
        const Type_ptr rhs_type = f_type_stack.back(); // just inspect
        unsigned i, width = tm.as_int_algebraic(rhs_type)->width();

        ADD* lhs[width];
        for (i = width; (i) ; -- i) {
            *lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
        }

        algebraic_not(); // bitwise
        return;
    }

    assert(false); // unreachable
}

bool BECompiler::walk_add_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_add_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_add_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Plus(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_plus();
        return;
    }

    assert(0); // unreachable
}

bool BECompiler::walk_sub_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_sub_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_sub_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Minus(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_sub();
        return;
    }

    assert(0); // unexpected
}

bool BECompiler::walk_div_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_div_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_div_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Divide(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_div();
        return;
    }

    assert(0); // unexpected
}

bool BECompiler::walk_mul_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_mul_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_mul_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Times(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }


    else if (is_binary_algebraic(expr)) {
        algebraic_mul();
        return;
    }

    assert(0); // unreachable
}

bool BECompiler::walk_mod_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_mod_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_mod_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.Modulus(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_mod();
        return;
    }

    assert(0); // unreachable
}

bool BECompiler::walk_and_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_and_postorder(const Expr_ptr expr)
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
        algebraic_and(); // bitwise
        return;
    }

    assert(0); // unreachable
}

bool BECompiler::walk_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_or_postorder(const Expr_ptr expr)
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
        algebraic_or();
        return;
    }
}

bool BECompiler::walk_xor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_xor_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_xor_postorder(const Expr_ptr expr)
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
        algebraic_xor();
        return;
    }

    assert(0); // unreachable
}

bool BECompiler::walk_xnor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_xnor_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_xnor_postorder(const Expr_ptr expr)
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
        algebraic_xnor();
        return;
    }

    assert(0); // unreachable
}

bool BECompiler::walk_implies_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_implies_postorder(const Expr_ptr expr)
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
        algebraic_implies();
        return;
    }

    assert(0); // unreachable
}

bool BECompiler::walk_iff_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_iff_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_iff_postorder(const Expr_ptr expr)
{ /* just a fancy name for xnor :-) */ walk_xnor_postorder(expr); }

bool BECompiler::walk_lshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_lshift_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_lshift_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.LShift(rhs)); /* bitwise integer arithmetic */
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }
    else if (is_binary_algebraic(expr)) {
        algebraic_lshift();
        return;
    }

    assert(0); // unreachable
}

bool BECompiler::walk_rshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_rshift_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_rshift_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.RShift(rhs)); /* bitwise integer arithmetic */
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }
    else if (is_binary_algebraic(expr)) {
        algebraic_rshift();
        return;
    }

    assert(0); // unreachable
}

bool BECompiler::walk_eq_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_eq_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_eq_postorder(const Expr_ptr expr)
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
        algebraic_equals();
        return;
    }

    assert(0); // unreachable
}

bool BECompiler::walk_ne_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_ne_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_ne_postorder(const Expr_ptr expr)
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
        algebraic_not_equals();
        return;
    }

    assert(0); // unreachable
}

bool BECompiler::walk_gt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_gt_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_gt_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(rhs.LT(lhs)); // simulate GT op
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_gt();
        return;
    }
    else assert(0);
}

bool BECompiler::walk_ge_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_ge_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_ge_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(rhs.LEQ(lhs)); // simulate GEQ op
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_ge();
        return;
    }

    assert(0); // unreachable
}

bool BECompiler::walk_lt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_lt_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_lt_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.LT(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_lt();
        return;
    }

    assert(0); // unreachable
}

bool BECompiler::walk_le_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_le_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_le_postorder(const Expr_ptr expr)
{
    if (is_binary_integer(expr)) {
        const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
        const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
        f_add_stack.push_back(lhs.LEQ(rhs));
        f_type_stack.pop_back(); // consume one, leave the other
        return;
    }

    else if (is_binary_algebraic(expr)) {
        algebraic_le();
        return;
    }

    assert(0); // unreachable
}

bool BECompiler::walk_ite_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_ite_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_ite_postorder(const Expr_ptr expr)
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
        algebraic_ite();
        return;
    }

    assert(0); // unreachable
 }

bool BECompiler::walk_cond_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_cond_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_cond_postorder(const Expr_ptr expr)
{ /* nop, ite will do all the work */ }

bool BECompiler::walk_dot_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_dot_inorder(const Expr_ptr expr)
{
    // ADD tmp = f_add_stack.back();
    // Expr_ptr ctx = tmp->get_repr();
    // f_ctx_stack.push_back(ctx);
    return true;
}
void BECompiler::walk_dot_postorder(const Expr_ptr expr)
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

void BECompiler::walk_leaf(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* cached? */
    if (! cache_miss(expr)) return;

    // symb resolution
    Model& model = static_cast <Model&> (*f_owner.model());
    Expr_ptr ctx = f_ctx_stack.back();
    step_t time = f_time_stack.back();

    // 0. explicit constants are integer ints (e.g. 42)
    if (em.is_numeric(expr)) {
        f_add_stack.push_back(f_enc.constant(expr->value()));
        f_type_stack.push_back(tm.find_integer()); // consts
        return;
    }

    else {
        ISymbol_ptr symb = model.fetch_symbol(ctx, expr);
        assert (NULL != symb);

        // 1. bool/integer constant leaves
        if (symb->is_const()) {
            IConstant& konst =  symb->as_const();
            f_add_stack.push_back(f_enc.constant(konst.value()));
            f_type_stack.push_back(konst.type());
            return;
        }

        // 2. variable
        else if (symb->is_variable()) {

            // push into type stack
            Type_ptr vtype = symb->as_variable().type();

            // if encoding for variable is available reuse it,
            // otherwise create and cache it.
            FQExpr key(ctx, expr, time);
            IEncoding_ptr enc = NULL;

            ENCMap::iterator eye = f_encodings.find(key);
            if (eye != f_encodings.end()) {
                enc = (*eye).second;
            }
            else {
                enc = f_enc.make_encoding(vtype);
                register_encoding(key, enc); // TODO: move the
                                             // encoding register to a
                                             // dedicated
                                             // object. (maybe the
                                             // enc_mgr itself?)
            }
            assert (NULL != enc);

            // push either 1 or more ADDs depending on the encoding
            f_type_stack.push_back(vtype);
            if (tm.is_boolean(vtype) ||
                tm.is_enum(vtype) ||
                tm.is_integer(vtype)) {
                f_add_stack.push_back(enc->dv()[0]);
            }
            else if (tm.is_int_algebraic(vtype)) {
                for (unsigned i = tm.as_int_algebraic(vtype)->width(); (i); -- i) {
                    f_add_stack.push_back(enc->dv()[i]);
                }
            }
            else assert(0); // unexpected
            return;
        }

        // 3. define? Simply compile it recursively.
        else if (symb->is_define()) {
            (*this)(symb->as_define().body());
            return;
        }
    }

    assert(0); // unreachable
}

/**
   Booleans:
   . binary: AND, OR, XOR, XNOR, IFF, IMPLIES, EQ, NE
   . unary : NOT, () ?

   Finite Range Integers (aka Monolithes)

   . binary: AND (bw), OR(bw), XOR(bw), XNOR(bw), IFF(bw),
   IMPLIES(bw), LT, LE, GT, GE, EQ, NE, PLUS, SUB, DIV, MUL, MOD

   . unary : ? (), : (), NEG, NOT(bw)

   Enums (strict subset of the above)
   . binary : LT, LE, GT, GE, EQ, NE
   . unary  : ? (), : (),

   Algebraic:

   . binary : AND(bw), OR(bw), XOR(bw), XNOR(bw), IFF(bw),
   IMPLIES(bw), LT, LE, GT, GE, EQ, NE, PLUS, SUB, DIV, MUL, MOD

   . unary  : NOT(bw), ? (), : (), NEG,
*/

bool BECompiler::is_binary_boolean(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* AND, OR, XOR, XNOR, IFF, IMPLIES */
    if (em.is_binary_logical(expr)) {
        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());
        return (tm.is_boolean(f_owner.type(lhs)) &&
                tm.is_boolean(f_owner.type(rhs)));
    }

    return false;
}

bool BECompiler::is_unary_boolean(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /*  NOT, () ? */
    if (em.is_unary_logical(expr)) {
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());
        return (tm.is_boolean(f_owner.type(lhs)));
    }

    return false;
}

bool BECompiler::is_binary_integer(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* AND (bw), OR(bw), XOR(bw), XNOR(bw), IFF(bw),
       IMPLIES(bw), LT, LE, GT, GE, EQ, NE, PLUS, SUB, DIV, MUL, MOD */
    if ((em.is_binary_logical(expr)) ||
        (em.is_binary_arithmetical(expr)) ||
        (em.is_binary_relational(expr))) {

        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());
        return (tm.is_integer(f_owner.type(lhs)) &&
                tm.is_integer(f_owner.type(rhs)));
    }

    return false;
}

bool BECompiler::is_unary_integer(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* unary : ? (), : (), NEG, NOT(bw) */
    if (em.is_unary_arithmetical(expr)) {
        Type_ptr tp = f_type_stack.back();
        return (tm.is_integer(tp));
    }

    return false;
}

bool BECompiler::is_binary_enumerative(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* AND (bw), OR(bw), XOR(bw), XNOR(bw), IFF(bw),
       IMPLIES(bw), LT, LE, GT, GE, EQ, NE, PLUS, SUB, DIV, MUL, MOD */
    if ((em.is_binary_arithmetical(expr)) ||
        (em.is_binary_relational(expr))) {

        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());
        return (tm.is_enum(f_owner.type(lhs)) &&
                tm.is_enum(f_owner.type(rhs)));
    }

    return false;
}

bool BECompiler::is_unary_enumerative(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* unary : ? (), : (), NEG, NOT(bw) */
    if (em.is_unary_arithmetical(expr)) {
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());

        return (tm.is_enum(f_owner.type(lhs)));
    }

    return false;
}

/* following predicates take into account that conversion may be
   needed to "algebrize" an operand, *but not BOTH of them* */
bool BECompiler::is_binary_algebraic(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    if ((em.is_binary_logical(expr)) ||
        (em.is_binary_arithmetical(expr)) ||
        (em.is_binary_relational(expr))) {

        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());

        // see comment above
        return ( (tm.is_int_algebraic(f_owner.type(lhs)) ||
                  tm.is_integer(f_owner.type(lhs))) &&

                 (tm.is_int_algebraic(f_owner.type(rhs)) ||
                  tm.is_integer(f_owner.type(rhs))));
    }

    return false;
}

bool BECompiler::is_unary_algebraic(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    if ((em.is_unary_logical(expr)) ||
        (em.is_unary_arithmetical(expr))) {

        FQExpr lhs(f_ctx_stack.back(), expr->lhs());

        return ( (tm.is_int_algebraic(f_owner.type(lhs)) ||
                  tm.is_integer(f_owner.type(lhs))));
    }

    return false;
}

/* this is cool, due to stack organization is perfectly fine to use
   binary variants :-) */
bool BECompiler::is_ite_boolean(const Expr_ptr expr)
{ return is_binary_boolean(expr); }

bool BECompiler::is_ite_integer(const Expr_ptr expr)
{ return is_binary_integer(expr); }

bool BECompiler::is_ite_enumerative(const Expr_ptr expr)
{ return is_binary_enumerative(expr); }

bool BECompiler::is_ite_algebraic(const Expr_ptr expr)
{ return is_binary_algebraic(expr); }


void BECompiler::algebraic_plus()
{
    unsigned i, width = algebrize_ops_binary(); // largest, takes care of type stack

    ADD* rhs[width];
    for (i = width; (i) ; -- i) {
        *rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD* lhs[width];
    for (i = width; (i) ; -- i) {
        *lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform arithmetic sum using positional algorithm */
    ADD carry = f_enc.zero();
    for (i = width; (i); -- i) {

        /* x[i] + y[i] + c */
        ADD tmp = (*lhs[i]).Plus(*rhs[i]).Plus(carry);
        carry = f_enc.base().LT(tmp); /* c > 0x10 */

        /* x[i] = (x[i] + y[i] + c) % base */ // TODO: detect overflow on MSB
        f_add_stack.push_back(tmp.Modulus(f_enc.base()));
    }
}

void BECompiler::algebraic_and()
{
    unsigned i, width = algebrize_ops_binary(); // largest

    ADD* rhs[width];
    for (i = width; (i) ; -- i) {
        *rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD* lhs[width];
    for (i = width; (i) ; -- i) {
        *lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (i = width; (i); -- i) {

        /* x[i] &  y[i] */
        ADD tmp = (*lhs[i]).BWTimes(*rhs[i]);
        f_add_stack.push_back(tmp);
    }
}

void BECompiler::algebraic_or()
{
    unsigned i, width = algebrize_ops_binary(); // largest

    ADD* rhs[width];
    for (i = width; (i) ; -- i) {
        *rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD* lhs[width];
    for (i = width; (i) ; -- i) {
        *lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (i = width; (i); -- i) {

        /* x[i] &  y[i] */
        ADD tmp = (*lhs[i]).BWOr(*rhs[i]);
        f_add_stack.push_back(tmp);
    }
}

void BECompiler::algebraic_xor()
{
    unsigned i, width = algebrize_ops_binary(); // largest

    ADD* rhs[width];
    for (i = width; (i) ; -- i) {
        *rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD* lhs[width];
    for (i = width; (i) ; -- i) {
        *lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (i = width; (i); -- i) {

        /* x[i] &  y[i] */
        ADD tmp = (*lhs[i]).BWXor(*rhs[i]);
        f_add_stack.push_back(tmp);
    }
}

void BECompiler::algebraic_xnor()
{
    unsigned i, width = algebrize_ops_binary(); // largest

    ADD* rhs[width];
    for (i = width; (i) ; -- i) {
        *rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD* lhs[width];
    for (i = width; (i) ; -- i) {
        *lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (i = width; (i); -- i) {

        /* x[i] &  y[i] */
        ADD tmp = (*lhs[i]).BWXnor(*rhs[i]);
        f_add_stack.push_back(tmp);
    }
}

void BECompiler::algebraic_implies()
{
    unsigned i, width = algebrize_ops_binary(); // largest

    ADD* rhs[width];
    for (i = width; (i) ; -- i) {
        *rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD* lhs[width];
    for (i = width; (i) ; -- i) {
        *lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (i = width; (i); -- i) {

        /* x[i] &  y[i] */
        ADD tmp = (*lhs[i]).BWCmpl().BWXor(*rhs[i]);
        f_add_stack.push_back(tmp);
    }
}

void BECompiler::algebraic_lshift()
{
    unsigned i, width = algebrize_ops_binary(); // largest

    ADD* rhs[width];
    for (i = width; (i) ; -- i) {
        *rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD* lhs[width];
    for (i = width; (i) ; -- i) {
        *lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, nothing fancy  here :-) */
    for (i = width; (i); -- i) {

        /* x[i] &  y[i] */
        ADD tmp = (*lhs[i]).BWCmpl().BWXor(*rhs[i]);
        f_add_stack.push_back(tmp);
    }
}

void BECompiler::algebraic_rshift()
{
}

void BECompiler::algebraic_equals()
{
    unsigned i, width = algebrize_ops_binary(); // largest

    ADD* rhs[width];
    for (i = width; (i) ; -- i) {
        *rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD* lhs[width];
    for (i = width; (i) ; -- i) {
        *lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, similar to xnor, only conjuct res */
    ADD tmp = f_enc.one();
    for (i = width; (i); -- i) {

        /* x[i] &  y[i] */
        tmp *= (*lhs[i]).Equals(*rhs[i]);
    }

    /* just one result */
    f_add_stack.push_back(tmp);
}

void BECompiler::algebraic_not_equals()
{
    unsigned i, width = algebrize_ops_binary(); // largest

    ADD* rhs[width];
    for (i = width; (i) ; -- i) {
        *rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD* lhs[width];
    for (i = width; (i) ; -- i) {
        *lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* perform bw arithmetic, similar to xnor, only conjuct res */
    ADD tmp = f_enc.one();
    for (i = width; (i); -- i) {

        /* x[i] &  y[i] */
        tmp *= (*lhs[i]).Equals(*rhs[i]);
    }

    /* just one result */
    f_add_stack.push_back(tmp.Cmpl());
}

void BECompiler::algebraic_gt()
{
    unsigned i, width = algebrize_ops_binary(); // largest

    ADD* rhs[width];
    for (i = width; (i) ; -- i) {
        *rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD* lhs[width];
    for (i = width; (i) ; -- i) {
        *lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* relationals, msb predicate first, if false inspect next digit ... */
    ADD tmp = f_enc.zero();
    for (i = width; (i); -- i) {

        /* x[i] &  y[i] */
        tmp += (*rhs[i]).LT(*lhs[i]); // CHECK MSB
    }

    /* just one result */
    f_add_stack.push_back(tmp);
}

void BECompiler::algebraic_ge()
{
    unsigned i, width = algebrize_ops_binary(); // largest

    ADD* rhs[width];
    for (i = width; (i) ; -- i) {
        *rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD* lhs[width];
    for (i = width; (i) ; -- i) {
        *lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* relationals, msb predicate first, if false inspect next digit ... */
    ADD tmp = f_enc.zero();
    for (i = width; (i); -- i) {

        /* x[i] &  y[i] */
        tmp += (*rhs[i]).LEQ(*lhs[i]); // CHECK MSB
    }

    /* just one result */
    f_add_stack.push_back(tmp);
}

void BECompiler::algebraic_lt()
{
    unsigned i, width = algebrize_ops_binary(); // largest

    ADD* rhs[width];
    for (i = width; (i) ; -- i) {
        *rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD* lhs[width];
    for (i = width; (i) ; -- i) {
        *lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* relationals, msb predicate first, if false inspect next digit ... */
    ADD tmp = f_enc.zero();
    for (i = width; (i); -- i) {

        /* x[i] &  y[i] */
        tmp += (*lhs[i]).LT(*rhs[i]); // CHECK MSB
    }

    /* just one result */
    f_add_stack.push_back(tmp);
}

void BECompiler::algebraic_le()
{
    unsigned i, width = algebrize_ops_binary(); // largest

    ADD* rhs[width];
    for (i = width; (i) ; -- i) {
        *rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD* lhs[width];
    for (i = width; (i) ; -- i) {
        *lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    /* relationals, msb predicate first, if false inspect next digit ... */
    ADD tmp = f_enc.zero();
    for (i = width; (i); -- i) {

        /* x[i] &  y[i] */
        tmp += (*lhs[i]).LEQ(*rhs[i]); // CHECK MSB
    }

    /* just one result */
    f_add_stack.push_back(tmp);
}

// TODO fix type stack
void BECompiler::algebraic_ite()
{
    unsigned i, width = algebrize_ops_binary(); // largest

    ADD* rhs[width];
    for (i = width; (i) ; -- i) {
        *rhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD* lhs[width];
    for (i = width; (i) ; -- i) {
        *lhs[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    const ADD c = f_add_stack.back(); f_add_stack.pop_back();

    /* multiplex, easy as pie :-) */
    for (i = width; (i); -- i) {
        f_add_stack.push_back(c.Ite(*lhs[i], *rhs[i]));
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

    const Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();
    const Type_ptr lhs_type = f_type_stack.back(); f_type_stack.pop_back();

    assert( tm.is_int_algebraic(rhs_type) || tm.is_int_algebraic(lhs_type) );
    unsigned rhs_width = tm.is_int_algebraic(rhs_type)
        ? tm.as_int_algebraic(rhs_type)->width()
        : 0;

    unsigned lhs_width = tm.is_int_algebraic(lhs_type)
        ? tm.as_int_algebraic(lhs_type)->width()
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
            bool is_signed = tm.as_int_algebraic(rhs_type)->is_signed();
            algebraic_padding(rhs_width, res, is_signed);
        }
    }

    if (lhs_width < res) {
        if (! lhs_width) { // integer, conversion required
            algebraic_from_integer(res);
        }
        else { // just padding required
            bool is_signed = tm.as_int_algebraic(lhs_type)->is_signed();
            algebraic_padding(lhs_width, res, is_signed);
        }
    }

    return res;
}

// due to new type system, integer can be only constant (good)
void BECompiler::algebraic_from_integer(unsigned width)
{
    const ADD top = f_add_stack.back(); f_add_stack.pop_back();
    assert (f_enc.is_constant(top));

    value_t value = f_enc.const_value(top);

    unsigned i, base = Cudd_V(f_enc.base().getNode());

    for (i = width; (i); -- i) {
        ADD digit = f_enc.constant(value % base);
        f_add_stack.push_back(digit);
        value /= base;
    }

    assert (value == 0); // not overflowing
}

void BECompiler::algebraic_padding(unsigned old_width, unsigned new_width, bool is_signed)
{
    unsigned i;
    ADD padding = f_enc.zero();
    ADD zero = f_enc.zero();

    assert (old_width < new_width); // old is smaller than new

    ADD* tmp[old_width];
    for (i = old_width; (i) ; -- i) {
        *tmp[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    // sign extension predicate (0x00 or 0xFF?) only if required.
    if (is_signed) {
        padding += (*tmp[i]).BWTimes(f_enc.msb()).Equals(zero).Ite(zero, f_enc.full());
    }

    for (i = new_width - old_width; (i); -- i) {
        f_add_stack.push_back(padding);
    }
    for (i = old_width; (i); -- i) {
        f_add_stack.push_back(*tmp[i]);
    }
}
