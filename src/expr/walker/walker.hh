/**
 * @file expr_walker.hh
 * @brief Expression walker pattern implementation
 *
 * This header file contains the declarations required by the Expression
 * Walker class.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/

#ifndef EXPR_WALKER_H
#define EXPR_WALKER_H

#include <common/common.hh>

#include <sstream>
#include <stack>

#include <expr/expr.hh>
#include <expr/walker/typedefs.hh>
#include <expr/walker/exceptions.hh>
#include <expr/walker/helpers.hh>

class ExprWalker {
public:
    ExprWalker()
    {}

    virtual ~ExprWalker()
    {}

    ExprWalker& operator() (const Expr_ptr expr);

protected:
    /* global hooks */
    virtual void pre_hook()
    {}
    virtual void post_hook()
    {}

    /* step-by-step hooks */
    virtual void pre_node_hook(Expr_ptr expr)
    {}
    virtual void post_node_hook(Expr_ptr expr)
    {}

    virtual void walk();
    void rewrite(const Expr_ptr expr);

    walker_stack f_recursion_stack;
    bool f_rewritten;

    // -- hooks ----------------------------------------------------------------

    // LTL temporal ops
    virtual bool walk_F_preorder(const Expr_ptr expr) =0;
    virtual void walk_F_postorder(const Expr_ptr expr) =0;

    virtual bool walk_G_preorder(const Expr_ptr expr) =0;
    virtual void walk_G_postorder(const Expr_ptr expr) =0;

    virtual bool walk_X_preorder(const Expr_ptr expr) =0;
    virtual void walk_X_postorder(const Expr_ptr expr) =0;

    virtual bool walk_U_preorder(const Expr_ptr expr) =0;
    virtual bool walk_U_inorder(const Expr_ptr expr) =0;
    virtual void walk_U_postorder(const Expr_ptr expr) =0;

    virtual bool walk_R_preorder(const Expr_ptr expr) =0;
    virtual bool walk_R_inorder(const Expr_ptr expr) =0;
    virtual void walk_R_postorder(const Expr_ptr expr) =0;

    // temporal ops
    virtual bool walk_at_preorder(const Expr_ptr expr) =0;
    virtual bool walk_at_inorder(const Expr_ptr expr) =0;
    virtual void walk_at_postorder(const Expr_ptr expr) =0;

    virtual bool walk_next_preorder(const Expr_ptr expr) =0;
    virtual void walk_next_postorder(const Expr_ptr expr) =0;

    // unary ops
    virtual bool walk_neg_preorder(const Expr_ptr expr) =0;
    virtual void walk_neg_postorder(const Expr_ptr expr) =0;

    virtual bool walk_not_preorder(const Expr_ptr expr) =0;
    virtual void walk_not_postorder(const Expr_ptr expr) =0;

    virtual bool walk_bw_not_preorder(const Expr_ptr expr) =0;
    virtual void walk_bw_not_postorder(const Expr_ptr expr) =0;

    // arithmetical binary ops
    virtual bool walk_add_preorder(const Expr_ptr expr) =0;
    virtual bool walk_add_inorder(const Expr_ptr expr) =0;
    virtual void walk_add_postorder(const Expr_ptr expr) =0;

    virtual bool walk_sub_preorder(const Expr_ptr expr) =0;
    virtual bool walk_sub_inorder(const Expr_ptr expr) =0;
    virtual void walk_sub_postorder(const Expr_ptr expr) =0;

    virtual bool walk_div_preorder(const Expr_ptr expr) =0;
    virtual bool walk_div_inorder(const Expr_ptr expr) =0;
    virtual void walk_div_postorder(const Expr_ptr expr) =0;

    virtual bool walk_mul_preorder(const Expr_ptr expr) =0;
    virtual bool walk_mul_inorder(const Expr_ptr expr) =0;
    virtual void walk_mul_postorder(const Expr_ptr expr) =0;

    virtual bool walk_mod_preorder(const Expr_ptr expr) =0;
    virtual bool walk_mod_inorder(const Expr_ptr expr) =0;
    virtual void walk_mod_postorder(const Expr_ptr expr) =0;

    virtual bool walk_and_preorder(const Expr_ptr expr) =0;
    virtual bool walk_and_inorder(const Expr_ptr expr) =0;
    virtual void walk_and_postorder(const Expr_ptr expr) =0;

    virtual bool walk_bw_and_preorder(const Expr_ptr expr) =0;
    virtual bool walk_bw_and_inorder(const Expr_ptr expr) =0;
    virtual void walk_bw_and_postorder(const Expr_ptr expr) =0;

    virtual bool walk_or_preorder(const Expr_ptr expr) =0;
    virtual bool walk_or_inorder(const Expr_ptr expr) =0;
    virtual void walk_or_postorder(const Expr_ptr expr) =0;

    virtual bool walk_bw_or_preorder(const Expr_ptr expr) =0;
    virtual bool walk_bw_or_inorder(const Expr_ptr expr) =0;
    virtual void walk_bw_or_postorder(const Expr_ptr expr) =0;

    virtual bool walk_bw_xor_preorder(const Expr_ptr expr) =0;
    virtual bool walk_bw_xor_inorder(const Expr_ptr expr) =0;
    virtual void walk_bw_xor_postorder(const Expr_ptr expr) =0;

    virtual bool walk_bw_xnor_preorder(const Expr_ptr expr) =0;
    virtual bool walk_bw_xnor_inorder(const Expr_ptr expr) =0;
    virtual void walk_bw_xnor_postorder(const Expr_ptr expr) =0;

    virtual bool walk_guard_preorder(const Expr_ptr expr) =0;
    virtual bool walk_guard_inorder(const Expr_ptr expr) =0;
    virtual void walk_guard_postorder(const Expr_ptr expr) =0;

    virtual bool walk_implies_preorder(const Expr_ptr expr) =0;
    virtual bool walk_implies_inorder(const Expr_ptr expr) =0;
    virtual void walk_implies_postorder(const Expr_ptr expr) =0;

    virtual bool walk_lshift_preorder(const Expr_ptr expr) =0;
    virtual bool walk_lshift_inorder(const Expr_ptr expr) =0;
    virtual void walk_lshift_postorder(const Expr_ptr expr) =0;

    virtual bool walk_rshift_preorder(const Expr_ptr expr) =0;
    virtual bool walk_rshift_inorder(const Expr_ptr expr) =0;
    virtual void walk_rshift_postorder(const Expr_ptr expr) =0;

    virtual bool walk_assignment_preorder(const Expr_ptr expr) =0;
    virtual bool walk_assignment_inorder(const Expr_ptr expr) =0;
    virtual void walk_assignment_postorder(const Expr_ptr expr) =0;

    virtual bool walk_eq_preorder(const Expr_ptr expr) =0;
    virtual bool walk_eq_inorder(const Expr_ptr expr) =0;
    virtual void walk_eq_postorder(const Expr_ptr expr) =0;

    virtual bool walk_ne_preorder(const Expr_ptr expr) =0;
    virtual bool walk_ne_inorder(const Expr_ptr expr) =0;
    virtual void walk_ne_postorder(const Expr_ptr expr) =0;

    virtual bool walk_gt_preorder(const Expr_ptr expr) =0;
    virtual bool walk_gt_inorder(const Expr_ptr expr) =0;
    virtual void walk_gt_postorder(const Expr_ptr expr) =0;

    virtual bool walk_ge_preorder(const Expr_ptr expr) =0;
    virtual bool walk_ge_inorder(const Expr_ptr expr) =0;
    virtual void walk_ge_postorder(const Expr_ptr expr) =0;

    virtual bool walk_lt_preorder(const Expr_ptr expr) =0;
    virtual bool walk_lt_inorder(const Expr_ptr expr) =0;
    virtual void walk_lt_postorder(const Expr_ptr expr) =0;

    virtual bool walk_le_preorder(const Expr_ptr expr) =0;
    virtual bool walk_le_inorder(const Expr_ptr expr) =0;
    virtual void walk_le_postorder(const Expr_ptr expr) =0;

    virtual bool walk_ite_preorder(const Expr_ptr expr) =0;
    virtual bool walk_ite_inorder(const Expr_ptr expr) =0;
    virtual void walk_ite_postorder(const Expr_ptr expr) =0;

    virtual bool walk_cond_preorder(const Expr_ptr expr) =0;
    virtual bool walk_cond_inorder(const Expr_ptr expr) =0;
    virtual void walk_cond_postorder(const Expr_ptr expr) =0;

    virtual bool walk_dot_preorder(const Expr_ptr expr) =0;
    virtual bool walk_dot_inorder(const Expr_ptr expr) =0;
    virtual void walk_dot_postorder(const Expr_ptr expr) =0;

    virtual bool walk_params_preorder(const Expr_ptr expr) =0;
    virtual bool walk_params_inorder(const Expr_ptr expr) =0;
    virtual void walk_params_postorder(const Expr_ptr expr) =0;

    virtual bool walk_params_comma_preorder(const Expr_ptr expr) =0;
    virtual bool walk_params_comma_inorder(const Expr_ptr expr) =0;
    virtual void walk_params_comma_postorder(const Expr_ptr expr) =0;

    virtual bool walk_subscript_preorder(const Expr_ptr expr) =0;
    virtual bool walk_subscript_inorder(const Expr_ptr expr) =0;
    virtual void walk_subscript_postorder(const Expr_ptr expr) =0;

    virtual bool walk_array_preorder(const Expr_ptr expr) =0;
    virtual void walk_array_postorder(const Expr_ptr expr) =0;

    virtual bool walk_array_comma_preorder(const Expr_ptr expr) =0;
    virtual bool walk_array_comma_inorder(const Expr_ptr expr) =0;
    virtual void walk_array_comma_postorder(const Expr_ptr expr) =0;

    virtual bool walk_set_preorder(const Expr_ptr expr) =0;
    virtual void walk_set_postorder(const Expr_ptr expr) =0;

    virtual bool walk_set_comma_preorder(const Expr_ptr expr) =0;
    virtual bool walk_set_comma_inorder(const Expr_ptr expr) =0;
    virtual void walk_set_comma_postorder(const Expr_ptr expr) =0;

    virtual bool walk_cast_preorder(const Expr_ptr expr) =0;
    virtual bool walk_cast_inorder(const Expr_ptr expr) =0;
    virtual void walk_cast_postorder(const Expr_ptr expr) =0;

    virtual bool walk_type_preorder(const Expr_ptr expr) =0;
    virtual bool walk_type_inorder(const Expr_ptr expr) =0;
    virtual void walk_type_postorder(const Expr_ptr expr) =0;

    // leaves
    virtual void walk_instant(const Expr_ptr expr) =0;
    virtual void walk_leaf(const Expr_ptr expr) =0;
};

#endif /* EXPR_WALKER_H */
