/**
 * @file nnfizer.cc
 * @brief Expr nnfizer class implementation
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
#include <expr/expr_mgr.hh>

#include <expr/nnfizer/nnfizer.hh>

namespace expr {

Nnfizer::Nnfizer()
    : f_em(ExprMgr::INSTANCE())
     , f_polarity_stack()
{
    const void* instance { this };
    DRIVEL
        << "Initialized NNFizer @"
        << instance
        << std::endl;
}

Nnfizer::~Nnfizer()
{
    const void* instance { this };
    DRIVEL
        << "Destroyed NNizer @"
        << instance
        << std::endl;
}

void Nnfizer::pre_hook()
{}

void Nnfizer::post_hook()
{}

Expr_ptr Nnfizer::process(Expr_ptr expr)
{
    assert(0 == f_polarity_stack.size());
    f_polarity_stack.push_back(true);

    this->operator()(expr);

    assert(1 == f_expr_stack.size());
    assert(0 == f_polarity_stack.size());


    Expr_ptr res
        (f_expr_stack.back());
    f_expr_stack.pop_back();
    return res;
}

bool Nnfizer::walk_unary_preorder(const Expr_ptr expr)
{
    bool polarity
        (f_polarity_stack.back());

    f_polarity_stack.push_back(polarity);
    return true;
}

bool Nnfizer::walk_binary_preorder(const Expr_ptr expr)
{
    bool polarity
        (f_polarity_stack.back());

    f_polarity_stack.push_back(polarity);
    f_polarity_stack.push_back(polarity);
    return true;
}


bool Nnfizer::walk_F_preorder(const Expr_ptr expr)
{ return walk_unary_preorder(expr); }


void Nnfizer::walk_F_postorder(const Expr_ptr expr)
{
    Expr_ptr lhs
        (f_expr_stack.back());
    f_expr_stack.pop_back();

    bool polarity
        (f_polarity_stack.back());
    f_polarity_stack.pop_back();

    f_expr_stack.push_back(
        polarity
        ? f_em.make_F(lhs)
        : f_em.make_G(lhs)) ;
}

bool Nnfizer::walk_G_preorder(const Expr_ptr expr)
{ return walk_unary_preorder(expr); }

void Nnfizer::walk_G_postorder(const Expr_ptr expr)
{
    Expr_ptr lhs
        (f_expr_stack.back());
    f_expr_stack.pop_back();

    bool polarity
        (f_polarity_stack.back());
    f_polarity_stack.pop_back();

    f_expr_stack.push_back(
        polarity
        ? f_em.make_G(lhs)
        : f_em.make_F(lhs)) ;
}

bool Nnfizer::walk_X_preorder(const Expr_ptr expr)
{ return walk_unary_preorder(expr); }

void Nnfizer::walk_X_postorder(const Expr_ptr expr)
{
    Expr_ptr lhs
        (f_expr_stack.back());
    f_expr_stack.pop_back();

    f_expr_stack.push_back(f_em.make_X(lhs));
}

bool Nnfizer::walk_U_preorder(const Expr_ptr expr)
{ return walk_binary_preorder(expr); }
bool Nnfizer::walk_U_inorder(const Expr_ptr expr)
{ return true; }

void Nnfizer::walk_U_postorder(const Expr_ptr expr)
{
    Expr_ptr rhs
        (f_expr_stack.back());
    f_expr_stack.pop_back();

    Expr_ptr lhs
        (f_expr_stack.back());
    f_expr_stack.pop_back();

    bool polarity
        (f_polarity_stack.back());
    f_polarity_stack.pop_back();

    f_expr_stack.push_back(
        polarity
        ? f_em.make_U(lhs, rhs)
        : f_em.make_R(lhs, rhs)) ;
}

bool Nnfizer::walk_R_preorder(const Expr_ptr expr)
{ return walk_binary_preorder(expr); }
bool Nnfizer::walk_R_inorder(const Expr_ptr expr)
{ return true; }

void Nnfizer::walk_R_postorder(const Expr_ptr expr)
{
    Expr_ptr rhs
        (f_expr_stack.back());
    f_expr_stack.pop_back();

    Expr_ptr lhs
        (f_expr_stack.back());
    f_expr_stack.pop_back();

    bool polarity
        (f_polarity_stack.back());
    f_polarity_stack.pop_back();

    f_expr_stack.push_back(
        polarity
        ? f_em.make_R(lhs, rhs)
        : f_em.make_U(lhs, rhs)) ;
}

bool Nnfizer::walk_at_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_at_inorder(const Expr_ptr expr)
{ return true; }
void Nnfizer::walk_at_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_interval_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_interval_inorder(const Expr_ptr expr)
{ return true; }
void Nnfizer::walk_interval_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_next_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
void Nnfizer::walk_next_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_neg_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
void Nnfizer::walk_neg_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_not_preorder(const Expr_ptr expr)
{
    bool polarity
        (f_polarity_stack.back());
    f_polarity_stack.push_back(! polarity);
    return true;
}
void Nnfizer::walk_not_postorder(const Expr_ptr expr)
{
    f_polarity_stack.pop_back();
}

bool Nnfizer::walk_bw_not_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
void Nnfizer::walk_bw_not_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_add_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_add_inorder(const Expr_ptr expr)
{ return false; }
void Nnfizer::walk_add_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_sub_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_sub_inorder(const Expr_ptr expr)
{ return false; }
void Nnfizer::walk_sub_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_div_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_div_inorder(const Expr_ptr expr)
{ return false; }
void Nnfizer::walk_div_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_mul_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_mul_inorder(const Expr_ptr expr)
{ return false; }
void Nnfizer::walk_mul_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_mod_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_mod_inorder(const Expr_ptr expr)
{ return false; }
void Nnfizer::walk_mod_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_and_preorder(const Expr_ptr expr)
{ return walk_binary_preorder(expr); }
bool Nnfizer::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void Nnfizer::walk_and_postorder(const Expr_ptr expr)
{
    Expr_ptr rhs
        (f_expr_stack.back());
    f_expr_stack.pop_back();

    Expr_ptr lhs
        (f_expr_stack.back());
    f_expr_stack.pop_back();

    bool polarity
        (f_polarity_stack.back());
    f_polarity_stack.pop_back();

    f_expr_stack.push_back(
        polarity
        ? f_em.make_and(lhs, rhs)
        : f_em.make_or(lhs, rhs)) ;
}

bool Nnfizer::walk_bw_and_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_bw_and_inorder(const Expr_ptr expr)
{ return false; }
void Nnfizer::walk_bw_and_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_or_preorder(const Expr_ptr expr)
{ return walk_binary_preorder(expr); }
bool Nnfizer::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void Nnfizer::walk_or_postorder(const Expr_ptr expr)
{
    Expr_ptr rhs
        (f_expr_stack.back());
    f_expr_stack.pop_back();

    Expr_ptr lhs
        (f_expr_stack.back());
    f_expr_stack.pop_back();

    bool polarity
        (f_polarity_stack.back());
    f_polarity_stack.pop_back();

    f_expr_stack.push_back(
        polarity
        ? f_em.make_or(lhs, rhs)
        : f_em.make_and(lhs, rhs)) ;
}

bool Nnfizer::walk_bw_or_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_bw_or_inorder(const Expr_ptr expr)
{ return false; }
void Nnfizer::walk_bw_or_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_bw_xor_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_bw_xor_inorder(const Expr_ptr expr)
{ return false; }
void Nnfizer::walk_bw_xor_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_bw_xnor_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_bw_xnor_inorder(const Expr_ptr expr)
{ return false; }
void Nnfizer::walk_bw_xnor_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_guard_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_guard_inorder(const Expr_ptr expr)
{ return false; }
void Nnfizer::walk_guard_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_implies_preorder(const Expr_ptr expr)
{
    bool polarity
        (f_polarity_stack.back());

    f_polarity_stack.push_back(! polarity);
    f_polarity_stack.push_back(polarity);
    return true;
}
bool Nnfizer::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void Nnfizer::walk_implies_postorder(const Expr_ptr expr)
{
    Expr_ptr rhs
        (f_expr_stack.back());
    f_expr_stack.pop_back();

    Expr_ptr lhs
        (f_expr_stack.back());
    f_expr_stack.pop_back();

    bool polarity
        (f_polarity_stack.back());
    f_polarity_stack.pop_back();

    f_expr_stack.push_back(
        polarity
        ? f_em.make_or(lhs, rhs)
        : f_em.make_and(lhs, rhs)) ;
}

bool Nnfizer::walk_cast_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_cast_inorder(const Expr_ptr expr)
{ return false; }
void Nnfizer::walk_cast_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_type_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_type_inorder(const Expr_ptr expr)
{ return false; }
void Nnfizer::walk_type_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_lshift_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_lshift_inorder(const Expr_ptr expr)
{ return false; }
void Nnfizer::walk_lshift_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_rshift_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_rshift_inorder(const Expr_ptr expr)
{ return false; }
void Nnfizer::walk_rshift_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_assignment_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_assignment_inorder(const Expr_ptr expr)
{ return false; }
void Nnfizer::walk_assignment_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_eq_preorder(const Expr_ptr expr)
{
    bool polarity
        (f_polarity_stack.back());
    f_polarity_stack.pop_back();

    f_expr_stack.push_back(
        polarity
        ? expr
        : f_em.make_ne(expr->lhs(), expr->rhs())) ;

    return false; /* do not recur */
}
bool Nnfizer::walk_eq_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Nnfizer::walk_eq_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_ne_preorder(const Expr_ptr expr)
{
    bool polarity
        (f_polarity_stack.back());
    f_polarity_stack.pop_back();

    f_expr_stack.push_back(
        polarity
        ? expr
        : f_em.make_eq(expr->lhs(), expr->rhs())) ;

    return false; /* do not recur */

}
bool Nnfizer::walk_ne_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Nnfizer::walk_ne_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_gt_preorder(const Expr_ptr expr)
{
    bool polarity
        (f_polarity_stack.back());
    f_polarity_stack.pop_back();

    f_expr_stack.push_back(
        polarity
        ? expr
        : f_em.make_le(expr->lhs(), expr->rhs())) ;

    return false; /* do not recur */
}
bool Nnfizer::walk_gt_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Nnfizer::walk_gt_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_ge_preorder(const Expr_ptr expr)
{
    bool polarity
        (f_polarity_stack.back());
    f_polarity_stack.pop_back();

    f_expr_stack.push_back(
        polarity
        ? expr
        : f_em.make_lt(expr->lhs(), expr->rhs())) ;

    return false; /* do not recur */
}
bool Nnfizer::walk_ge_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Nnfizer::walk_ge_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_lt_preorder(const Expr_ptr expr)
{
    bool polarity
        (f_polarity_stack.back());
    f_polarity_stack.pop_back();

    f_expr_stack.push_back(
        polarity
        ? expr
        : f_em.make_ge(expr->lhs(), expr->rhs())) ;

    return false; /* do not recur */
}
bool Nnfizer::walk_lt_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Nnfizer::walk_lt_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_le_preorder(const Expr_ptr expr)
{
    bool polarity
        (f_polarity_stack.back());
    f_polarity_stack.pop_back();

    f_expr_stack.push_back(
        polarity
        ? expr
        : f_em.make_gt(expr->lhs(), expr->rhs())) ;

    return false; /* do not recur */
}
bool Nnfizer::walk_le_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Nnfizer::walk_le_postorder(const Expr_ptr expr)
{}

// FIXME: what needs to happen here?
bool Nnfizer::walk_ite_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_ite_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Nnfizer::walk_ite_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_cond_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_cond_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Nnfizer::walk_cond_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_dot_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_dot_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Nnfizer::walk_dot_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_params_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_params_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Nnfizer::walk_params_postorder(const Expr_ptr expr)
{ }

bool Nnfizer::walk_params_comma_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_params_comma_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Nnfizer::walk_params_comma_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_subscript_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_subscript_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Nnfizer::walk_subscript_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_array_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
void Nnfizer::walk_array_postorder(const Expr_ptr expr)
{ assert(false); }

bool Nnfizer::walk_array_comma_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_array_comma_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Nnfizer::walk_array_comma_postorder(const Expr_ptr expr)
{}

bool Nnfizer::walk_set_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
void Nnfizer::walk_set_postorder(const Expr_ptr expr)
{ assert(false); }

bool Nnfizer::walk_set_comma_preorder(const Expr_ptr expr)
{ return internal_error(expr); }
bool Nnfizer::walk_set_comma_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Nnfizer::walk_set_comma_postorder(const Expr_ptr expr)
{}

void Nnfizer::walk_instant(const Expr_ptr expr)
{ f_expr_stack.push_back(expr); }

void Nnfizer::walk_leaf(const Expr_ptr expr)
{
    const bool polarity
        (f_polarity_stack.back());
    f_polarity_stack.pop_back();

    /* only predicates allowed here */
    f_expr_stack.push_back(
        polarity
        ? expr
        : f_em.make_not(expr));
}

bool Nnfizer::internal_error(const Expr_ptr expr)
{
    ERR
        << "Expression `"
        << expr
        << "` was not supposed to be reached."
        << std::endl;

    throw new InternalError("NNF conversion aborted");
    return false;
}

};
