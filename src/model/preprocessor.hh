/**
 *  @file preprocessor.hh
 *  @brief Expr preprocessor used in Define w/ param substitution
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

#ifndef PREPROCESSOR_H
#define PREPROCESSOR_H

#include <model.hh>
#include <expr_walker.hh>

// NOTE: here we're using a vector in order to bypass STL stack
// interface limitations. (i.e. absence of clear())
typedef vector< pair< Expr_ptr, Expr_ptr> > ExprPairStack;
typedef vector<Expr_ptr> ExprStack;
typedef vector<IDefine_ptr> DefinesStack;

/* shortcuts to simplify manipulation of the internal expr stack */
#define POP_EXPR(op)                              \
    const Expr_ptr op = f_expr_stack.back();      \
    f_expr_stack.pop_back()

#define PUSH_EXPR(tp)                             \
    f_expr_stack.push_back(tp)

/* shortcuts to simplify manipulation of the internal define stack */
#define POP_DEFINE(op)                              \
    const Define_ptr op = f_define_stack.back();    \
    f_define_stack.pop_back()

#define PUSH_DEFINE(tp)                             \
    f_define_stack.push_back(tp)

class ModelMgr;
class Preprocessor : public ExprWalker {
public:
    Preprocessor(ModelMgr& owner);
    ~Preprocessor();

    // walker toplevel
    Expr_ptr process(Expr_ptr ctx, Expr_ptr expr);

protected:
    void pre_hook();
    void post_hook();

    void pre_node_hook(Expr_ptr expr);
    void post_node_hook(Expr_ptr expr);

    // walker interface
    bool walk_next_preorder(const Expr_ptr expr);
    void walk_next_postorder(const Expr_ptr expr);
    bool walk_neg_preorder(const Expr_ptr expr);
    void walk_neg_postorder(const Expr_ptr expr);
    bool walk_not_preorder(const Expr_ptr expr);
    void walk_not_postorder(const Expr_ptr expr);
    bool walk_add_preorder(const Expr_ptr expr);
    bool walk_add_inorder(const Expr_ptr expr);
    void walk_add_postorder(const Expr_ptr expr);
    bool walk_sub_preorder(const Expr_ptr expr);
    bool walk_sub_inorder(const Expr_ptr expr);
    void walk_sub_postorder(const Expr_ptr expr);
    bool walk_div_preorder(const Expr_ptr expr);
    bool walk_div_inorder(const Expr_ptr expr);
    void walk_div_postorder(const Expr_ptr expr);
    bool walk_mul_preorder(const Expr_ptr expr);
    bool walk_mul_inorder(const Expr_ptr expr);
    void walk_mul_postorder(const Expr_ptr expr);
    bool walk_mod_preorder(const Expr_ptr expr);
    bool walk_mod_inorder(const Expr_ptr expr);
    void walk_mod_postorder(const Expr_ptr expr);
    bool walk_and_preorder(const Expr_ptr expr);
    bool walk_and_inorder(const Expr_ptr expr);
    void walk_and_postorder(const Expr_ptr expr);
    bool walk_or_preorder(const Expr_ptr expr);
    bool walk_or_inorder(const Expr_ptr expr);
    void walk_or_postorder(const Expr_ptr expr);
    bool walk_xor_preorder(const Expr_ptr expr);
    bool walk_xor_inorder(const Expr_ptr expr);
    void walk_xor_postorder(const Expr_ptr expr);
    bool walk_xnor_preorder(const Expr_ptr expr);
    bool walk_xnor_inorder(const Expr_ptr expr);
    void walk_xnor_postorder(const Expr_ptr expr);
    bool walk_implies_preorder(const Expr_ptr expr);
    bool walk_implies_inorder(const Expr_ptr expr);
    void walk_implies_postorder(const Expr_ptr expr);
    bool walk_iff_preorder(const Expr_ptr expr);
    bool walk_iff_inorder(const Expr_ptr expr);
    void walk_iff_postorder(const Expr_ptr expr);
    bool walk_lshift_preorder(const Expr_ptr expr);
    bool walk_lshift_inorder(const Expr_ptr expr);
    void walk_lshift_postorder(const Expr_ptr expr);
    bool walk_rshift_preorder(const Expr_ptr expr);
    bool walk_rshift_inorder(const Expr_ptr expr);
    void walk_rshift_postorder(const Expr_ptr expr);
    bool walk_eq_preorder(const Expr_ptr expr);
    bool walk_eq_inorder(const Expr_ptr expr);
    void walk_eq_postorder(const Expr_ptr expr);
    bool walk_ne_preorder(const Expr_ptr expr);
    bool walk_ne_inorder(const Expr_ptr expr);
    void walk_ne_postorder(const Expr_ptr expr);
    bool walk_gt_preorder(const Expr_ptr expr);
    bool walk_gt_inorder(const Expr_ptr expr);
    void walk_gt_postorder(const Expr_ptr expr);
    bool walk_ge_preorder(const Expr_ptr expr);
    bool walk_ge_inorder(const Expr_ptr expr);
    void walk_ge_postorder(const Expr_ptr expr);
    bool walk_lt_preorder(const Expr_ptr expr);
    bool walk_lt_inorder(const Expr_ptr expr);
    void walk_lt_postorder(const Expr_ptr expr);
    bool walk_le_preorder(const Expr_ptr expr);
    bool walk_le_inorder(const Expr_ptr expr);
    void walk_le_postorder(const Expr_ptr expr);
    bool walk_ite_preorder(const Expr_ptr expr);
    bool walk_ite_inorder(const Expr_ptr expr);
    void walk_ite_postorder(const Expr_ptr expr);
    bool walk_cond_preorder(const Expr_ptr expr);
    bool walk_cond_inorder(const Expr_ptr expr);
    void walk_cond_postorder(const Expr_ptr expr);
    bool walk_dot_preorder(const Expr_ptr expr);
    bool walk_dot_inorder(const Expr_ptr expr);
    void walk_dot_postorder(const Expr_ptr expr);
    bool walk_params_preorder(const Expr_ptr expr);
    bool walk_params_inorder(const Expr_ptr expr);
    void walk_params_postorder(const Expr_ptr expr);
    bool walk_subscript_preorder(const Expr_ptr expr);
    bool walk_subscript_inorder(const Expr_ptr expr);
    void walk_subscript_postorder(const Expr_ptr expr);
    bool walk_comma_preorder(const Expr_ptr expr);
    bool walk_comma_inorder(const Expr_ptr expr);
    void walk_comma_postorder(const Expr_ptr expr);

    void walk_leaf(const Expr_ptr expr);

private:
    // probably not really necessary, we keep it for now
    ExprStack f_ctx_stack;

    // Results stack
    ExprStack f_expr_stack;

    // Not terribly efficient but easier to implement nested envs with
    ExprPairStack f_env;

    // managers
    ModelMgr& f_owner;

    // Expr Mgr
    ExprMgr& f_em;

    /* internals */
    void substitute_expression(const Expr_ptr expr);
    void traverse_param_list(ExprVector& params, const Expr_ptr expr);
};

#endif