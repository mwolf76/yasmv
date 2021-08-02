/**
 * @file preprocessor.hh
 * @brief Expr preprocessor used in Define w/ param substitution
 *
 * This header file contains the declarations required by the
 * Preprocessor class.
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

#ifndef PREPROCESSOR_H
#define PREPROCESSOR_H

#include <common/common.hh>

#include <utility>
#include <vector>

#include <model/model.hh>

#include <expr/expr_mgr.hh>
#include <expr/walker/walker.hh>

namespace expr::preprocessor {

// NOTE: here we're using a vector in order to bypass STL stack
// interface limitations. (i.e. absence of clear())
typedef std::vector< std::pair<expr::Expr_ptr, expr::Expr_ptr> > ExprPairStack;
typedef std::vector<expr::Expr_ptr> ExprStack;
typedef std::vector<symb::Define_ptr> DefinesStack;

class Preprocessor : public expr::ExprWalker {
public:
    Preprocessor();
    ~Preprocessor();

    // walker toplevel
    expr::Expr_ptr process(expr::Expr_ptr expr, expr::Expr_ptr ctx);

protected:
    void pre_hook();
    void post_hook();

    void pre_node_hook(expr::Expr_ptr expr);
    void post_node_hook(expr::Expr_ptr expr);

    LTL_HOOKS; OP_HOOKS;

    void walk_instant(const expr::Expr_ptr expr);
    void walk_leaf(const expr::Expr_ptr expr);

private:
    ExprMgr& f_em;

    // probably not really necessary, we keep it for now
    ExprStack f_ctx_stack;

    // Results stack
    ExprStack f_expr_stack;

    // Not terribly efficient but easier to implement nested envs with
    ExprPairStack f_env;

    /* internals */
    // void substitute_expression(const expr::Expr_ptr expr);
    void traverse_param_list(expr::ExprVector& params, const expr::Expr_ptr expr);
};

} // namespace compiler

#endif /* PREPROCESSOR_H */
