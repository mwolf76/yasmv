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

    // Just one 0-1 ADD returned. This is ok, because the compiler is
    // supposed to return a boolean formula, suitable for CNF
    // conversion. This condition is checked by the post-hook method.
    return f_add_stack.back();
}

void BECompiler::pre_hook()
{}

void BECompiler::post_hook()
{
    ADD add = f_add_stack.back();
    assert( add.FindMin().Equals(f_enc.zero()) );
    assert( add.FindMax().Equals(f_enc.one()) );

    // sanity conditions
    assert(1 == f_add_stack.size());
    assert(1 == f_type_stack.size());
    assert(1 == f_ctx_stack.size());
    assert(1 == f_time_stack.size());
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

bool BECompiler::walk_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void BECompiler::walk_not_postorder(const Expr_ptr expr)
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
        algebraic_plus(expr);
        return;
    }

    assert( false ); // unreachable
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
        algebraic_sub(expr);
        return;
    }

    assert( false ); // unexpected
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
        // algebraic_div(expr->rhs());
        return;
    }

    assert( false ); // unexpected
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
        algebraic_mul(expr);
        return;
    }

    assert( false ); // unreachable
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
        algebraic_mod(expr);
        return;
    }

    assert( false ); // unreachable
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
        algebraic_and(expr); // bitwise
        return;
    }

    assert( false ); // unreachable
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
        algebraic_or(expr);
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
        algebraic_xor(expr);
        return;
    }

    assert( false ); // unreachable
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
        algebraic_xnor(expr);
        return;
    }

    assert( false ); // unreachable
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
        algebraic_implies(expr);
        return;
    }

    assert( false ); // unreachable
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
        algebraic_lshift(expr);
        return;
    }

    assert( false ); // unreachable
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
        algebraic_rshift(expr);
        return;
    }

    assert( false ); // unreachable
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
        algebraic_equals(expr);
        return;
    }

    assert( false ); // unreachable
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
        algebraic_not_equals(expr);
        return;
    }

    assert( false ); // unreachable
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
        algebraic_gt(expr);
        return;
    }
    else assert( false );
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
        algebraic_ge(expr);
        return;
    }

    assert( false ); // unreachable
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
        algebraic_lt(expr);
        return;
    }

    assert( false ); // unreachable
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
        algebraic_le(expr);
        return;
    }

    assert( false ); // unreachable
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
        algebraic_ite(expr);
        return;
    }

    assert( false ); // unreachable
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


void BECompiler::push_variable(IEncoding_ptr enc, Type_ptr type)
{
    TypeMgr& tm = f_owner.tm();

    assert (NULL != enc);
    DDVector& dds = enc->dv();
    unsigned width = dds.size();

    // push into type stack
    f_type_stack.push_back(type);

    // push either 1 or more ADDs depending on the encoding
    if (tm.is_boolean(type) || tm.is_enum(type) || tm.is_integer(type)) {
        assert(1 == width);
        f_add_stack.push_back(dds[0]);
    }
    else if (tm.is_algebraic(type)) {
        assert( tm.as_algebraic(type)->width() == width ); // type and enc width info has to match
        for (int i = width -1; (0 <= i); -- i) {
            f_add_stack.push_back(dds[i]);
        }
    }
    else assert( false ); // unexpected
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

    ENCMap::iterator eye;
    IEncoding_ptr enc = NULL;

    // 1. explicit constants are integer ints (e.g. 42)
    if (em.is_numeric(expr)) {
        f_add_stack.push_back(f_enc.constant(expr->value()));
        f_type_stack.push_back(tm.find_integer()); // consts
        return;
    }

    // 2. Symbols
    ISymbol_ptr symb = NULL;
    Type_ptr type = NULL;

    // 2. 1. Temporary symbols are maintained internally by the compiler
    if (NULL != (symb = fetch_temporary(expr, time))) {

        type = symb->as_variable().type();
        assert(tm.is_algebraic(type));

        // temporary encodings must be already defined.
        FQExpr key(ExprMgr::INSTANCE().make_main(), expr, time);

        ENCMap::iterator eye = f_temporary.find(key);
        if (eye != f_temporary.end()) {
            enc = (*eye).second;
        }
        else assert(false); // unexpected

        push_variable(enc, type);
        return;
    } /* Temporary symbols */

    // 2. 2. Model symbol
    if (NULL != (symb = model.fetch_symbol(ctx, expr))) {

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

            ENCMap::iterator eye = f_encodings.find(key);
            if (eye != f_encodings.end()) {
                enc = (*eye).second;
            }
            else {
                /* build a new encoding for this symbol */
                enc = f_enc.make_encoding(type);
                register_encoding(key, enc);
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
        return ( (tm.is_algebraic(f_owner.type(lhs)) ||
                  tm.is_integer(f_owner.type(lhs))) &&

                 (tm.is_algebraic(f_owner.type(rhs)) ||
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

        return ( (tm.is_algebraic(f_owner.type(lhs)) ||
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
