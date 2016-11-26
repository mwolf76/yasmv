/**
 * @file evaluator.cc
 * @brief Expressions evaluator class implementation.
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

#include <common/common.hh>

#include <expr/expr.hh>

#include <symb/proxy.hh>

#include <witness/evaluator.hh>
#include <witness/witness_mgr.hh>

#include <env/environment.hh>

Evaluator::Evaluator(WitnessMgr& owner)
    : f_owner(owner)
{
    const void *instance(this);
    DRIVEL
        << "Created Evaluator @"
        << instance
        << std::endl;
}

Evaluator::~Evaluator()
{
    const void* instance(this);
    DRIVEL
        << "Destroying Evaluator @"
        << instance
        << std::endl;
}

void Evaluator::clear_internals()
{
    f_type_stack.clear();
    f_values_stack.clear();
    f_ctx_stack.clear();
    f_time_stack.clear();
    f_te2v_map.clear();
}

Expr_ptr Evaluator::process(Witness &witness, Expr_ptr ctx,
                            Expr_ptr body, step_t time)
{
    ExprMgr& em
        (ExprMgr::INSTANCE());

    clear_internals();

    // setting the environment
    f_witness = &witness;

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);

    // toplevel (time is assumed at 0, arbitrarily nested next allowed)
    f_time_stack.push_back(time);

    /* Invoke walker on the body of the expr to be processed */
    (*this)(body);

    // sanity conditions, relaxed for arrays
    assert (0 < f_values_stack.size() &&
            1 == f_type_stack.size()  &&
            1 == f_ctx_stack.size()   &&
            1 == f_time_stack.size()) ;

    /* exactly one type in all cases */
    POP_TYPE(res_type);

    if (res_type -> is_boolean()) {
        assert(1 == f_values_stack.size());
        value_t res_value
            (f_values_stack.back());
        return res_value ? em.make_true() : em.make_false();
    }
    else if (res_type -> is_enum()) {
        assert(1 == f_values_stack.size());
        value_t res_value
            (f_values_stack.back());
        EnumType_ptr enum_type
            (res_type -> as_enum());

        const ExprSet& literals
            (enum_type -> literals());

        ExprSet::const_iterator i
            (literals.begin());

        while (0 < res_value) {
            -- res_value;
            ++ i;
        }

        return *i;
    }
    else if (res_type -> is_algebraic()) {
        assert(1 == f_values_stack.size());
        value_t res_value
            (f_values_stack.back());
        return em.make_const(res_value);
    }
    else if (res_type -> is_array()) {
        ArrayType_ptr atype
            (res_type -> as_array());

        assert(atype -> nelems() ==
               f_values_stack.size());

        Expr_ptr lst
            (NULL);

        /* assemble array values list */
        for (unsigned i = 0; i < atype -> nelems(); ++ i) {
            value_t lst_value
                (f_values_stack.back());
            f_values_stack.pop_back();

            lst = lst
                ? em.make_array_comma(lst, em.make_const(lst_value))
                : em.make_const(lst_value)
                ;
        }

        /* wrap list in ARRAY node and return */
        return em.make_array(lst);
    }
    else assert(false);
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

bool Evaluator::walk_bw_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Evaluator::walk_bw_not_postorder(const Expr_ptr expr)
{
    DROP_TYPE();

    POP_VALUE(lhs);
    PUSH_VALUE(~ lhs);
}

bool Evaluator::walk_add_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_add_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_add_postorder(const Expr_ptr expr)
{
    DROP_TYPE();

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
    DROP_TYPE();

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
    DROP_TYPE();

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
    DROP_TYPE();

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
    DROP_TYPE();

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
    DROP_TYPE();

    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(lhs && rhs);
}

bool Evaluator::walk_bw_and_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_bw_and_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_bw_and_postorder(const Expr_ptr expr)
{
    DROP_TYPE();

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
    DROP_TYPE();

    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(lhs || rhs);
}

bool Evaluator::walk_bw_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_bw_or_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_bw_or_postorder(const Expr_ptr expr)
{
    DROP_TYPE();

    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(lhs | rhs);
}

bool Evaluator::walk_bw_xor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_bw_xor_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_bw_xor_postorder(const Expr_ptr expr)
{
    DROP_TYPE();

    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(lhs ^ rhs);
}

bool Evaluator::walk_bw_xnor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_bw_xnor_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_bw_xnor_postorder(const Expr_ptr expr)
{
    DROP_TYPE();

    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(( ! lhs | rhs ) & ( ! rhs | lhs ));
}

bool Evaluator::walk_guard_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_guard_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_guard_postorder(const Expr_ptr expr)
{ assert(false); /* unreachable */ }

bool Evaluator::walk_implies_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_implies_postorder(const Expr_ptr expr)
{
    DROP_TYPE();

    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(( ! lhs || rhs ));
}

bool Evaluator::walk_lshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_lshift_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_lshift_postorder(const Expr_ptr expr)
{
    /* drops rhs, which is fine */
    DROP_TYPE();

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
    /* drop rhs, which is fine */
    DROP_TYPE();

    POP_VALUE(rhs);
    POP_VALUE(lhs);
    PUSH_VALUE(( lhs >> rhs ));
}

bool Evaluator::walk_assignment_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_assignment_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_assignment_postorder(const Expr_ptr expr)
{ assert(false); /* unreachable */ }

bool Evaluator::walk_eq_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_eq_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_eq_postorder(const Expr_ptr expr)
{
    TypeMgr& tm
        (f_owner.tm());

    POP_TYPE(rhs_type);
    POP_TYPE(lhs_type);

    if (rhs_type -> is_scalar() &&
        lhs_type -> is_scalar()) {

        POP_VALUE(rhs);
        POP_VALUE(lhs);

        PUSH_VALUE(( lhs == rhs ));
    }

    else if (rhs_type -> is_array() &&
             lhs_type -> is_array()) {

        ArrayType_ptr arhs_type
            (rhs_type -> as_array());
        ArrayType_ptr alhs_type
            (lhs_type -> as_array());

        assert (arhs_type -> width() ==
                alhs_type -> width() &&
                arhs_type -> nelems() ==
                alhs_type -> nelems());

        unsigned nelems
            (arhs_type -> nelems());

        value_t rhs[nelems];
        for (unsigned i = 0; i < nelems; ++ i) {
            rhs[i] = TOP_VALUE();
            DROP_VALUE();
        }

        value_t lhs[nelems];
        for (unsigned i = 0; i < nelems; ++ i) {
            lhs[i] = TOP_VALUE();
            DROP_VALUE();
        }

        bool res
            (true);

        for (unsigned i = 0; res && i < nelems; ++ i) {
            if (rhs[i] != lhs[i])
                res = false;
        }

        PUSH_VALUE((value_t) res);
    }

    else assert(false);

    PUSH_TYPE(tm.find_boolean());
}

bool Evaluator::walk_ne_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_ne_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_ne_postorder(const Expr_ptr expr)
{
    TypeMgr& tm
        (f_owner.tm());

    DROP_TYPE();
    DROP_TYPE();
    PUSH_TYPE(tm.find_boolean());

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
    TypeMgr& tm
        (f_owner.tm());

    DROP_TYPE();
    DROP_TYPE();
    PUSH_TYPE(tm.find_boolean());

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
    TypeMgr& tm
        (f_owner.tm());

    DROP_TYPE();
    DROP_TYPE();
    PUSH_TYPE(tm.find_boolean());

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
    TypeMgr& tm
        (f_owner.tm());

    DROP_TYPE();
    DROP_TYPE();
    PUSH_TYPE(tm.find_boolean());

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
    TypeMgr& tm
        (f_owner.tm());

    DROP_TYPE();
    DROP_TYPE();
    PUSH_TYPE(tm.find_boolean());

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
   POP_TYPE(rhs_type);
   DROP_TYPE();
   DROP_TYPE();
   PUSH_TYPE(rhs_type);

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
{
    ExprMgr& em
        (f_owner.em());

    DROP_TYPE();

    TOP_CTX(parent_ctx);

    Expr_ptr ctx
        (em.make_dot( parent_ctx, expr -> lhs()));
    PUSH_CTX(ctx);

    return true;
}
void Evaluator::walk_dot_postorder(const Expr_ptr expr)
{ DROP_CTX(); }

bool Evaluator::walk_params_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_params_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_params_postorder(const Expr_ptr expr)
{ assert (false); /* not yet implemented */ }

bool Evaluator::walk_params_comma_preorder(const Expr_ptr expr)
{  return cache_miss(expr); }
bool Evaluator::walk_params_comma_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_params_comma_postorder(const Expr_ptr expr)
{ assert (false); /* TODO support inlined non-determinism */ }


bool Evaluator::walk_subscript_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_subscript_inorder(const Expr_ptr expr)
{ return true; }

void Evaluator::walk_subscript_postorder(const Expr_ptr expr)
{
    value_t res;

    POP_TYPE(rhs_type);
    assert(rhs_type -> is_algebraic());

    POP_TYPE(lhs_type);
    assert(lhs_type -> is_array());

    ArrayType_ptr alhs_type
        (lhs_type -> as_array());

    /* fetch the index */
    POP_VALUE(index);

    /* fetch all items, record the interesting one */
    for (unsigned i = 0; i < alhs_type -> nelems(); ++ i) {
        POP_VALUE(elem);

        if (i == alhs_type -> nelems() - index - 1)
            res = elem;
    }

    /* return the value and scalar type*/
    PUSH_TYPE(alhs_type -> of());
    PUSH_VALUE(res);
}

bool Evaluator::walk_array_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Evaluator::walk_array_postorder(const Expr_ptr expr)
{}

bool Evaluator::walk_array_comma_preorder(const Expr_ptr expr)
{  return cache_miss(expr); }
bool Evaluator::walk_array_comma_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_array_comma_postorder(const Expr_ptr expr)
{
    TypeMgr& tm
        (TypeMgr::INSTANCE());

    POP_TYPE(rhs_type);

    unsigned nelems
        (rhs_type -> is_scalar()
         ? 2 /* base */
         : 1 + rhs_type -> as_array() -> nelems());

    POP_TYPE(lhs_type);
    assert(lhs_type -> is_scalar());

    ArrayType_ptr atmp_type
        (tm.find_array_type(lhs_type -> as_scalar(), nelems));

    PUSH_TYPE(atmp_type);
}

bool Evaluator::walk_set_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Evaluator::walk_set_postorder(const Expr_ptr expr)
{
    assert(false); // TODO
}

bool Evaluator::walk_set_comma_preorder(const Expr_ptr expr)
{  return cache_miss(expr); }
bool Evaluator::walk_set_comma_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_set_comma_postorder(const Expr_ptr expr)
{ assert (false); /* TODO support inlined non-determinism */ }

bool Evaluator::walk_type_preorder(const Expr_ptr expr)
{ return false; }
bool Evaluator::walk_type_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Evaluator::walk_type_postorder(const Expr_ptr expr)
{ assert (false); }

bool Evaluator::walk_cast_preorder(const Expr_ptr expr)
{  return cache_miss(expr); }
bool Evaluator::walk_cast_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_cast_postorder(const Expr_ptr expr)
{ /* nop */ }

void Evaluator::push_value(const Expr_ptr expr)
{
    ResolverProxy resolver;

    ExprMgr& em
        (ExprMgr::INSTANCE());

    if (em.is_false(expr))
        f_values_stack.push_back(0);

    else if (em.is_true(expr))
        f_values_stack.push_back(1);

    else if (em.is_identifier(expr)) {
        Expr_ptr full_lit
            (em.make_dot(em.make_empty(), expr));
        Symbol_ptr symb_lit
            (resolver.symbol(full_lit));
        assert( symb_lit -> is_literal());

        Literal& lit
            (symb_lit->as_literal());

        value_t value
            (lit.value());
        PUSH_VALUE(value);
    }
    else {
        if (em.is_constant(expr)) {
            /* scalar value, easy case */
            f_values_stack.push_back(expr -> value());
        }
        else if (em.is_neg(expr) &&
                 em.is_constant(expr -> lhs())) {
            /* negative scalar value, easy case */
            f_values_stack.push_back(- expr -> lhs() -> value());
        }
        else if (em.is_array(expr)) {
            /* array value, push each element */

            Expr_ptr eye
                (expr -> lhs());
            while (em.is_array_comma(eye)) {
                f_values_stack.push_back(eye -> lhs() -> value());
                eye = eye -> rhs();
            }
            f_values_stack.push_back(eye -> value()); /* last */
        }
        else {
            ERR
                << "Cannot evaluate `"
                << expr
                << "`"
                << std::endl;

            assert(false);
        }
    }
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

    // 0. explicit boolean consts
    if (em.is_bool_const(expr)) {

        PUSH_TYPE(tm.find_boolean());

        if (em.is_false(expr))
            PUSH_VALUE(0);
        else if (em.is_true(expr))
            PUSH_VALUE(1);
        else assert(false);

        return;
    }

    // 1. explicit int consts (e.g. 42) ...
    else if (em.is_int_numeric(expr)) {
        unsigned ww
            (OptsMgr::INSTANCE().word_width());
        PUSH_TYPE (tm.find_unsigned(ww));
        PUSH_VALUE(expr -> value());
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

    else if (symb->is_variable()) {

        Variable& var
            (symb -> as_variable());

        // push into type stack
        Type_ptr type
            (var.type());

        PUSH_TYPE(type);
        if (type->is_instance())
            return;

        else if (var.is_input()) {
            push_value(Environment::INSTANCE().get(expr));
        }

        else if (f_witness -> has_value( full, time)) {
            push_value(f_witness -> value( full, time));
        }

        else throw NoValue(full);

        return;
    } /* is_variable() */

    else if (symb->is_parameter()) {

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
            (rewrite -> lhs());
        PUSH_CTX(rewritten_ctx);

        Expr_ptr rewritten_expr
            (rewrite -> rhs());
        (*this) (rewritten_expr);

        DROP_CTX();
        return;
    }

    else if (symb -> is_define()) {
        Expr_ptr body
            (symb -> as_define().body());

#if 0
        DRIVEL
            << "Inlining `"
            << expr
            << "` := "
            << body
            << std::endl;
#endif

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
