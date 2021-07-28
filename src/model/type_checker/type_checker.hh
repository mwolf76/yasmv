/**
 * @file type_checker.hh
 * @brief Expr type checker
 *
 * This header file contains the declarations required to implement
 * the type checking of temporal logic expressions.
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

#ifndef TYPE_CHECKER_H
#define TYPE_CHECKER_H

#include <expr/walker/walker.hh>

#include <type/type.hh>
#include <type/type_mgr.hh>

#include <boost/unordered_map.hpp>

namespace model {

typedef boost::unordered_map<expr::Expr_ptr, Type_ptr, utils::PtrHash, utils::PtrEq> TypeReg;

/* enable the following macro to debug the TypeChecker */
// #define DEBUG_TYPE_CHECKER

class ModelMgr;
class TypeChecker : public expr::ExprWalker {
public:
    TypeChecker(ModelMgr& owner);
    ~TypeChecker();

    /** @brief Returns Type object for given FQExpr (memoized). */
    Type_ptr type(expr::Expr_ptr expr, expr::Expr_ptr ctx);

    // walker toplevel
    Type_ptr process(expr::Expr_ptr expr, expr::Expr_ptr ctx);

    inline ModelMgr& owner()
    { return f_owner; }

protected:
    void pre_hook();
    void post_hook();

    void pre_node_hook(expr::Expr_ptr expr);
    void post_node_hook(expr::Expr_ptr expr);

    LTL_HOOKS; OP_HOOKS;

    void walk_instant(const expr::Expr_ptr expr);
    void walk_leaf(const expr::Expr_ptr expr);

private:
    TypeReg f_map; // cache

    TypeVector f_type_stack;
    expr::ExprVector f_ctx_stack;

    // managers
    ModelMgr& f_owner;

    bool cache_miss(const expr::Expr_ptr expr);
    void memoize_result(expr::Expr_ptr expr);

    Type_ptr arithmetical_result_type(Type_ptr lhs, Type_ptr rhs);
    Type_ptr relational_result_type(Type_ptr lhs, Type_ptr rhs);
    Type_ptr logical_result_type(Type_ptr lhs, Type_ptr rhs);
    Type_ptr ite_result_type(Type_ptr lhs, Type_ptr rhs);
    Type_ptr cast_result_type(Type_ptr lhs, Type_ptr rhs);

    Type_ptr check_any(expr::Expr_ptr expr);
    Type_ptr check_timed(expr::Expr_ptr expr);
    Type_ptr check_logical(expr::Expr_ptr expr);
    Type_ptr check_arithmetical(expr::Expr_ptr expr);
    Type_ptr check_scalar(expr::Expr_ptr expr);
    Type_ptr check_array(expr::Expr_ptr expr);

    // post-orders only
    void walk_unary_fsm_postorder(const expr::Expr_ptr expr);
    void walk_unary_ltl_postorder(const expr::Expr_ptr expr);

    void walk_binary_fsm_postorder(const expr::Expr_ptr expr);
    void walk_binary_ltl_postorder(const expr::Expr_ptr expr);

    void walk_unary_arithmetical_postorder(const expr::Expr_ptr expr);
    void walk_binary_arithmetical_postorder(const expr::Expr_ptr expr);
    void walk_binary_timed_postorder(const expr::Expr_ptr expr);

    void walk_unary_logical_postorder(const expr::Expr_ptr expr);
    void walk_unary_bitwise_postorder(const expr::Expr_ptr expr);

    void walk_binary_logical_postorder(const expr::Expr_ptr expr);
    void walk_binary_bitwise_postorder(const expr::Expr_ptr expr);

    void walk_binary_shift_postorder(const expr::Expr_ptr expr);
    void walk_binary_relational_postorder(const expr::Expr_ptr expr);
    void walk_binary_equality_postorder(const expr::Expr_ptr expr);
    void walk_binary_ite_postorder(const expr::Expr_ptr expr);
    void walk_binary_boolean_or_relational_postorder(const expr::Expr_ptr expr);
    void walk_binary_cast_postorder(const expr::Expr_ptr expr);
};

};

#endif /* TYPE_CHECKER_H */
