/**
 * @file witness/internals.cc
 * @brief Expressions evaluator class implementation, internal helpers.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#include <env/environment.hh>
#include <symb/proxy.hh>
#include <witness/witness.hh>
#include <witness/witness_mgr.hh>
#include <witness/evaluator.hh>

#include <utils/time.hh>
#include <utils/values.hh>

void Evaluator::push_value(const Expr_ptr expr)
{
    ResolverProxy resolver;

    ExprMgr& em
        (ExprMgr::INSTANCE());

    if (em.is_identifier(expr)) {
        Expr_ptr full_lit
            (em.make_dot(em.make_empty(), expr));

        Symbol_ptr symb_lit
            (resolver.symbol(full_lit));

        assert(symb_lit->is_literal());

        Literal& lit
            (symb_lit->as_literal());

        value_t value
            (lit.value());

        PUSH_VALUE(value);
        return;
    }

    if (em.is_constant(expr)) {
        /* scalar value, easy case */
        PUSH_VALUE(expr->value());
        return;
    }

    if (em.is_neg(expr) &&
        em.is_constant(expr->lhs())) {

        /* negative scalar value, easy case */
        PUSH_VALUE(- expr->lhs()->value());
        return;
    }

    if (em.is_array(expr)) {
        /* array value, push each element */
        Expr_ptr eye
            (expr->lhs());

        while (em.is_array_comma(eye)) {
            PUSH_VALUE(eye->lhs()->value());
            eye = eye->rhs();
        }

        PUSH_VALUE(eye->value()); /* last */
        return;
    }

    ERR
        << "Cannot evaluate `"
        << expr
        << "`"
        << std::endl;

    assert(false);
}


/* the evaluator treats time relatively */
void Evaluator::walk_instant(const Expr_ptr expr)
{
    step_t curr_time
        (f_time_stack.back());

    f_time_stack.push_back(curr_time + expr->value());
}

void Evaluator::walk_leaf(const Expr_ptr expr)
{
    ExprMgr& em
        (f_owner.em());

    TypeMgr& tm
        (f_owner.tm());

    /* cached? */
    if (! cache_miss(expr))
        return;

    TOP_CTX(ctx);
    TOP_TIME(time);

    // explicit boolean consts
    if (em.is_bool_const(expr)) {

        PUSH_TYPE(tm.find_boolean());

        if (em.is_false(expr))
            PUSH_VALUE(0);

        else if (em.is_true(expr))
            PUSH_VALUE(1);

        else assert(false);

        return;
    }

    // explicit int consts (e.g. 42) ...
    if (em.is_int_const(expr)) {
        unsigned ww
            (OptsMgr::INSTANCE().word_width());

        PUSH_TYPE (tm.find_unsigned(ww));
        PUSH_VALUE(expr->value());
        return;
    }

    // explicit string consts (e.g. "hello") ...
    if (em.is_qstring(expr)) {
        PUSH_TYPE (tm.find_string());
        PUSH_VALUE((value_t) expr->atom().c_str());
        return;
    }

    ResolverProxy resolver;

    Expr_ptr full
        (em.make_dot( ctx, expr));

    Symbol_ptr symb
        (resolver.symbol(full));

    // 2. enum literals
    if (symb->is_literal()) {

        Literal& lit
            (symb->as_literal());

        Type_ptr type
            (lit.type());
        PUSH_TYPE(type);

        value_t value
            (lit.value());
        PUSH_VALUE(value);
        return;
    }

    if (symb->is_variable()) {

        Variable& var
            (symb->as_variable());

        // push into type stack
        Type_ptr type
            (var.type());

        PUSH_TYPE(type);
        if (type->is_instance())
            return;

        else if (var.is_input()) {
            push_value(env::Environment::INSTANCE().get(expr));
        }

        else if (f_witness->has_value( full, time)) {
            push_value(f_witness->value( full, time));
        }

        else throw NoValue(full);

        return;
    } /* is_variable() */

    if (symb->is_parameter()) {

        ModelMgr& mm
            (ModelMgr::INSTANCE());

        /* parameters must be resolved against the Param map
           maintained by the ModelMgr */
        Expr_ptr rewrite
            (mm.rewrite_parameter(full));

#if 0
        DRIVEL
            << "Rewritten `"
            << full << "` to "
            << rewrite
            << std::endl;
#endif

        Expr_ptr rewritten_ctx
            (rewrite->lhs());
        PUSH_CTX(rewritten_ctx);

        Expr_ptr rewritten_expr
            (rewrite->rhs());
        (*this) (rewritten_expr);

        DROP_CTX();
        return;
    }

    if (symb->is_define()) {
        Expr_ptr body
            (symb->as_define().body());

        DEBUG
            << "Inlining `"
            << expr
            << "` := "
            << body
            << std::endl;

        (*this) (body);
        return;
    }

    assert( false ); /* unexpected */
}

bool Evaluator::cache_miss(const Expr_ptr expr)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    assert(0 < f_ctx_stack.size());
    Expr_ptr ctx
        (f_ctx_stack.back());

    assert(0 < f_time_stack.size());
    step_t step
        (f_time_stack.back());

    TimedExpr key
        ( em.make_dot( ctx , expr), step);

    TimedExprValueMap::iterator eye
        (f_te2v_map.find(key));

    if (eye != f_te2v_map.end()) {
        value_t res
            ((*eye).second);

        PUSH_VALUE(res);
        return false;
    }

    return true;
}
