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
typedef boost::unordered_map<Expr_ptr, Type_ptr, PtrHash, PtrEq> TypeReg;

/* enable the following macro to debug the TypeChecker */
// #define DEBUG_TYPE_CHECKER

class ModelMgr;
class TypeChecker : public ExprWalker {
public:
    TypeChecker(ModelMgr& owner);
    ~TypeChecker();

    /** @brief Returns Type object for given FQExpr (memoized). */
    Type_ptr type(Expr_ptr expr, Expr_ptr ctx);

    // walker toplevel
    Type_ptr process(Expr_ptr expr, Expr_ptr ctx);

    inline ModelMgr& owner()
    { return f_owner; }

protected:
    void pre_hook();
    void post_hook();

    void pre_node_hook(Expr_ptr expr);
    void post_node_hook(Expr_ptr expr);

    LTL_HOOKS; OP_HOOKS;

    void walk_instant(const Expr_ptr expr);
    void walk_leaf(const Expr_ptr expr);

private:
    TypeReg f_map; // cache

    TypeVector f_type_stack;
    ExprVector f_ctx_stack;

    // managers
    ModelMgr& f_owner;

    bool cache_miss(const Expr_ptr expr);
    void memoize_result(Expr_ptr expr);

    Type_ptr arithmetical_result_type(Type_ptr lhs, Type_ptr rhs);
    Type_ptr relational_result_type(Type_ptr lhs, Type_ptr rhs);
    Type_ptr logical_result_type(Type_ptr lhs, Type_ptr rhs);
    Type_ptr ite_result_type(Type_ptr lhs, Type_ptr rhs);
    Type_ptr cast_result_type(Type_ptr lhs, Type_ptr rhs);

    Type_ptr check_any(Expr_ptr expr);
    Type_ptr check_timed(Expr_ptr expr);
    Type_ptr check_logical(Expr_ptr expr);
    Type_ptr check_arithmetical(Expr_ptr expr);
    Type_ptr check_scalar(Expr_ptr expr);
    Type_ptr check_array(Expr_ptr expr);

    // post-orders only
    void walk_unary_fsm_postorder(const Expr_ptr expr);
    void walk_unary_ltl_postorder(const Expr_ptr expr);

    void walk_binary_fsm_postorder(const Expr_ptr expr);
    void walk_binary_ltl_postorder(const Expr_ptr expr);

    void walk_unary_arithmetical_postorder(const Expr_ptr expr);
    void walk_binary_arithmetical_postorder(const Expr_ptr expr);
    void walk_binary_timed_postorder(const Expr_ptr expr);

    void walk_unary_logical_postorder(const Expr_ptr expr);
    void walk_unary_bitwise_postorder(const Expr_ptr expr);

    void walk_binary_logical_postorder(const Expr_ptr expr);
    void walk_binary_bitwise_postorder(const Expr_ptr expr);

    void walk_binary_shift_postorder(const Expr_ptr expr);
    void walk_binary_relational_postorder(const Expr_ptr expr);
    void walk_binary_equality_postorder(const Expr_ptr expr);
    void walk_binary_ite_postorder(const Expr_ptr expr);
    void walk_binary_boolean_or_relational_postorder(const Expr_ptr expr);
    void walk_binary_cast_postorder(const Expr_ptr expr);
};

#endif /* TYPE_CHECKER_H */
