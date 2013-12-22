/**
 *  @file inferrer.hh
 *  @brief Expr type inferrer
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

#ifndef INFERRER_H
#define INFERRER_H

#include <type.hh>
#include <type_mgr.hh>

#include <model.hh>
#include <expr_walker.hh>

// NOTE: here we're using a vector in order to bypass STL stack
// interface limitations. (i.e. absence of clear())
typedef vector<Type_ptr> TypeStack;
typedef vector<Expr_ptr> ExprStack;

typedef unordered_map<FQExpr, Type_ptr, FQExprHash, FQExprEq> TypeReg;
typedef pair<TypeReg::iterator, bool> TypeRegHit;

/* shortcuts to to simplify manipulation of the internal type stack */
#define POP_TYPE(op)                              \
    const Type_ptr op = f_type_stack.back();      \
    f_type_stack.pop_back()

#define PUSH_TYPE(tp)                             \
        f_type_stack.push_back(tp)

class ModelMgr;
class Inferrer : public ExprWalker {
public:
    Inferrer(ModelMgr& owner);
    ~Inferrer();

    /** @brief Returns Type object for given FQExpr (memoized). */
    Type_ptr type(FQExpr& fqexpr);

    // walker toplevel
    Type_ptr process(Expr_ptr ctx, Expr_ptr body);

protected:
    void pre_hook();
    void post_hook();

    void pre_node_hook(Expr_ptr expr);
    void post_node_hook(Expr_ptr expr);

    OP_HOOKS;
    void walk_leaf(const Expr_ptr expr);

private:
    TypeReg f_map; // cache

    TypeStack f_type_stack;
    ExprStack f_ctx_stack;

    // managers
    ModelMgr& f_owner;

    // services
    inline bool cache_miss(const Expr_ptr expr)
    {
        FQExpr key(f_ctx_stack.back(), expr);
        TypeReg::iterator eye = f_map.find(key);

        if (eye != f_map.end()) {
            Type_ptr res = (*eye).second;
            PUSH_TYPE(res);
            return false;
        }

        return true;
    }

    Type_ptr check_logical();
    Type_ptr check_arithmetical();
    Type_ptr check_logical_or_arithmetical();
    Type_ptr check_enum();
    Type_ptr check_scalar();

    Type_ptr check_array();

    // post-orders only
    void walk_unary_fsm_postorder(const Expr_ptr expr);
    void walk_binary_fsm_postorder(const Expr_ptr expr);
    void walk_unary_arithmetical_postorder(const Expr_ptr expr);
    void walk_binary_arithmetical_postorder(const Expr_ptr expr);
    void walk_unary_logical_postorder(const Expr_ptr expr);
    void walk_binary_logical_postorder(const Expr_ptr expr);
    void walk_binary_logical_or_bitwise_postorder(const Expr_ptr expr);
    void walk_binary_shift_postorder(const Expr_ptr expr);
    void walk_binary_relational_postorder(const Expr_ptr expr);
    void walk_binary_boolean_or_relational_postorder(const Expr_ptr expr);
    void walk_binary_cast_postorder(const Expr_ptr expr);
    void walk_ternary_ite_postorder(const Expr_ptr expr);
    void walk_ternary_cond_postorder(const Expr_ptr expr);

    // useful for better caching
    Expr_ptr find_canonical_expr(Expr_ptr expr);
    void memoize_result(Expr_ptr expr);
};

#endif
