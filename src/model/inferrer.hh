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
    Type_ptr process(Expr_ptr ctx, Expr_ptr body, expected_t expected = TP_BOOLEAN);

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

    bool walk_set_preorder(const Expr_ptr expr);
    void walk_set_postorder(const Expr_ptr expr);

    bool walk_comma_preorder(const Expr_ptr expr);
    bool walk_comma_inorder(const Expr_ptr expr);
    void walk_comma_postorder(const Expr_ptr expr);

    bool walk_range_preorder(const Expr_ptr expr);
    bool walk_range_inorder(const Expr_ptr expr);
    void walk_range_postorder(const Expr_ptr expr);

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

    /* throws a BadType exception if toplevel type does not match any
       of the expected. Returns type if succesful. */
    Type_ptr check_expected_type(expected_t expected);

    /* common special cases */
    inline Type_ptr check_boolean()
    { return check_expected_type(TP_BOOLEAN); }

    inline Type_ptr check_arithmetical()
    {
        return check_expected_type(TP_INT_CONST    |
                                   TP_UNSIGNED_INT |
                                   TP_SIGNED_INT ) ;
    }

    inline Type_ptr check_arithmetical_enumerative()
    {
        return check_expected_type(TP_INT_CONST    |
                                   TP_UNSIGNED_INT |
                                   TP_SIGNED_INT   |
                                   TP_ENUM );
    }

    inline Type_ptr check_arithmetical_integer()
    {
        return check_expected_type(TP_INT_CONST    |
                                   TP_UNSIGNED_INT |
                                   TP_SIGNED_INT ) ;
    }

    inline Type_ptr check_boolean_or_integer()
    {
        return check_expected_type(TP_BOOLEAN      |
                                   TP_INT_CONST    |
                                   TP_UNSIGNED_INT |
                                   TP_SIGNED_INT ) ;
    }

    inline Type_ptr check_array()
    {
        return check_expected_type(TP_ARRAY);
    }

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

    void walk_ternary_ite_postorder(const Expr_ptr expr);
    void walk_ternary_cond_postorder(const Expr_ptr expr);

    // useful for better caching
    Expr_ptr find_canonical_expr(Expr_ptr expr);
    void memoize_result(Expr_ptr expr);
};

#endif
