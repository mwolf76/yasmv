/**
 *  @file evaluator.cc
 *  @brief Expr evaluator
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
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
#include <evaluator.hh>

#include <witness_mgr.hh>

Evaluator::Evaluator(WitnessMgr& owner)
    : f_owner(owner)
{ DEBUG << "Created Evaluator @" << this << endl; }

Evaluator::~Evaluator()
{ DEBUG << "Destroying Evaluator @" << this << endl; }

value_t Evaluator::process(Witness &witness, Expr_ptr ctx,
                           Expr_ptr body, step_t time)
{
    // remove previous results
    f_values_stack.clear();
    f_ctx_stack.clear();
    f_time_stack.clear();
    f_map.clear();

    // setting the environment
    f_witness = &witness;

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);

    // toplevel (time is assumed at 0, arbitrarily nested next allowed)
    f_time_stack.push_back(time);

    FQExpr key(ctx, body, time);
    TRACE << "Evaluating " << key << endl;

    /* Invoke walker on the body of the expr to be processed */
    (*this)(body);

    // sanity conditions
    assert(1 == f_values_stack.size());
    assert(1 == f_ctx_stack.size());
    assert(1 == f_time_stack.size());

    // Exactly one expression
    value_t res = f_values_stack.back();
    return res;
}

/*  Evaluation engine is implemented using a simple expression walker
 *  pattern: (a) on preorder, return true if the node has not yet been
 *  visited; (b) always do in-order (for binary nodes); (c) perform
 *  proper compilation in post-order hooks. */

bool Evaluator::walk_next_preorder(const Expr_ptr expr)
{
    step_t curr_time = f_time_stack.back();
    f_time_stack.push_back(curr_time + 1);
    return true;
}
void Evaluator::walk_next_postorder(const Expr_ptr expr)
{
    assert (0 < f_time_stack.size());
    f_time_stack.pop_back(); // reset time stack
}

bool Evaluator::walk_prev_preorder(const Expr_ptr expr)
{
    step_t curr_time = f_time_stack.back();
    f_time_stack.push_back(curr_time - 1);
    return true;
}
void Evaluator::walk_prev_postorder(const Expr_ptr expr)
{
    assert (0 < f_time_stack.size());
    f_time_stack.pop_back(); // reset time stack
}

bool Evaluator::walk_neg_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Evaluator::walk_neg_postorder(const Expr_ptr expr)
{
    POP_VALUE(lhs);
    PUSH_VALUE(- lhs);
}

bool Evaluator::walk_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Evaluator::walk_not_postorder(const Expr_ptr expr)
{
    POP_VALUE(lhs);
    PUSH_VALUE(! lhs);
}

bool Evaluator::walk_add_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_add_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_add_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(lhs + rhs);
}

bool Evaluator::walk_sub_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_sub_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_sub_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(lhs - rhs);
}

bool Evaluator::walk_div_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_div_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_div_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(lhs / rhs);
}

bool Evaluator::walk_mul_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_mul_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_mul_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(lhs * rhs);
}

bool Evaluator::walk_mod_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_mod_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_mod_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(lhs % rhs);
}

bool Evaluator::walk_and_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_and_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(lhs & rhs);
}

bool Evaluator::walk_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_or_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(lhs | rhs);
}

bool Evaluator::walk_xor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_xor_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_xor_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(lhs ^ rhs);
}

bool Evaluator::walk_xnor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_xnor_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_xnor_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(( ! lhs | rhs ) & ( ! rhs | lhs ));
}

bool Evaluator::walk_implies_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_implies_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(( ! lhs | rhs ));
}

bool Evaluator::walk_iff_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_iff_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_iff_postorder(const Expr_ptr expr)
{ /* just a fancy name for xnor :-) */ walk_xnor_postorder(expr); }

bool Evaluator::walk_lshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_lshift_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_lshift_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(( lhs << rhs ));
}

bool Evaluator::walk_rshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_rshift_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_rshift_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(( lhs >> rhs ));
}

bool Evaluator::walk_eq_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_eq_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_eq_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(( lhs == rhs ));
}

bool Evaluator::walk_ne_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_ne_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_ne_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(lhs != rhs);
}

bool Evaluator::walk_gt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_gt_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_gt_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(( lhs > rhs ));
}

bool Evaluator::walk_ge_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_ge_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_ge_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(( lhs >= rhs ));
}

bool Evaluator::walk_lt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_lt_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_lt_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(( lhs < rhs ));
}

bool Evaluator::walk_le_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_le_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_le_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(( lhs <= rhs ));
}

bool Evaluator::walk_ite_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_ite_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_ite_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    POP_VALUE(cnd);
    PUSH_VALUE(( cnd ? lhs : rhs ));
}

bool Evaluator::walk_cond_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_cond_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_cond_postorder(const Expr_ptr expr)
{ /* nop */ }

bool Evaluator::walk_dot_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_dot_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_dot_postorder(const Expr_ptr expr)
{
    assert( false ); // yet to be implemented
}

bool Evaluator::walk_params_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_params_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_params_postorder(const Expr_ptr expr)
{ assert (false); /* not yet implemented */ }

bool Evaluator::walk_subscript_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_subscript_inorder(const Expr_ptr expr)
{ return true; }

void Evaluator::walk_subscript_postorder(const Expr_ptr expr)
{
#if 0
    unsigned base = Cudd_V(f_enc.base().getNode());

    const Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();

    /* algebrize selection expr (rhs), using machine width */
    assert (rhs_type->is_algebraic());
    // algebrize_unary_subscript();
    assert(false); // tODO

    ADD selector[2]; // TODO
    for (unsigned i = 0; i < 2; ++ i) {
        selector[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    const Type_ptr lhs_type = f_type_stack.back(); f_type_stack.pop_back();
    unsigned size = lhs_type -> size();

    const Type_ptr scalar_type = lhs_type -> as_array() ->of();
    unsigned width = scalar_type->size();

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
#endif
}

bool Evaluator::walk_set_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Evaluator::walk_set_postorder(const Expr_ptr expr)
{
    assert(false); // TODO
}

bool Evaluator::walk_comma_preorder(const Expr_ptr expr)
{  return cache_miss(expr); }
bool Evaluator::walk_comma_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_comma_postorder(const Expr_ptr expr)
{ assert (false); /* TODO support inlined non-determinism */ }

void Evaluator::walk_leaf(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();

    /* cached? */
    if (! cache_miss(expr)) return;

    Expr_ptr ctx = f_ctx_stack.back();
    step_t time = f_time_stack.back();

    // 0. explicit boolean consts
    if (em.is_bool_const(expr)) {

        if (em.is_false(expr)) {
            f_values_stack.push_back(0);
        }
        else if (em.is_true(expr)) {
            f_values_stack.push_back(1);
        }
        else assert(false) ; // unexpected
    }

    // 1. explicit constants are integer consts (e.g. 42) ..
    else  if (em.is_numeric(expr)) {
        f_values_stack.push_back(expr -> value());
        return;
    }

    else {
        /* Look for symbols in the witness */
        ISymbol_ptr symb = ModelMgr::INSTANCE().resolver() -> symbol(ctx, expr);
        if (symb->is_variable()) { // vars

            FQExpr key( ctx, expr, time);
            if (f_witness -> has_value( key)) {
                Expr_ptr expr = f_witness -> value(key);
                value_t res = expr -> value();
                f_values_stack.push_back(res);
                return;
            }

            assert( false ); /* unexpected */
        }

        else if (symb->is_define()) { // defines

            // A little bit of magic, re-entrant invocation ;-)
            (*this)(symb->as_define().body());
            return;
        }

        assert( false ); /* unexpected */
    }
}