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
    Expr_ptr process(Expr_ptr expr, Expr_ptr ctx);

protected:
    void pre_hook();
    void post_hook();

    void pre_node_hook(Expr_ptr expr);
    void post_node_hook(Expr_ptr expr);

    LTL_HOOKS; OP_HOOKS;
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
