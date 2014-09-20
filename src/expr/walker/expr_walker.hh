/**
 *  @file expr_walker.hh
 *  @brief Expression algorithm-unaware walk pattern implementation
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
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

#ifndef EXPR_WALKER_H
#define EXPR_WALKER_H

#include <common.hh>
#include <expr.hh>

/* helper macros to declare walker hooks */
#define UNARY_HOOK(op)                                       \
    bool walk_## op ## _preorder(const Expr_ptr expr);       \
    void walk_## op ## _postorder(const Expr_ptr expr)

#define BINARY_HOOK(op)                                      \
    bool walk_## op ## _preorder(const Expr_ptr expr);       \
    bool walk_## op ## _inorder(const Expr_ptr expr);        \
    void walk_## op ## _postorder(const Expr_ptr expr)

#define OP_HOOKS                                   \
    UNARY_HOOK(next); UNARY_HOOK(prev);            \
    UNARY_HOOK(neg); UNARY_HOOK(not);              \
    UNARY_HOOK(bw_not);                            \
                                                   \
    BINARY_HOOK(add); BINARY_HOOK(sub);            \
    BINARY_HOOK(div); BINARY_HOOK(mod);            \
    BINARY_HOOK(mul);                              \
                                                   \
    BINARY_HOOK(and); BINARY_HOOK(or);             \
    BINARY_HOOK(bw_and); BINARY_HOOK(bw_or);       \
    BINARY_HOOK(bw_xor); BINARY_HOOK(implies);     \
    BINARY_HOOK(bw_xnor); BINARY_HOOK(iff);        \
    BINARY_HOOK(lshift); BINARY_HOOK(rshift);      \
                                                   \
    BINARY_HOOK(type); BINARY_HOOK(cast);          \
                                                   \
    BINARY_HOOK(eq); BINARY_HOOK(ne);              \
    BINARY_HOOK(le); BINARY_HOOK(lt);              \
    BINARY_HOOK(ge); BINARY_HOOK(gt);              \
    BINARY_HOOK(ite); BINARY_HOOK(cond);           \
                                                   \
    BINARY_HOOK(dot);                              \
    BINARY_HOOK(params);                           \
    BINARY_HOOK(subscript);                        \
    UNARY_HOOK(set);                               \
    BINARY_HOOK(comma)

#define LTL_HOOKS                                       \
    UNARY_HOOK(F); UNARY_HOOK(G); UNARY_HOOK(X);        \
    BINARY_HOOK(R); BINARY_HOOK(U)

#define UNARY_STUB(op)                                       \
    bool walk_## op ## _preorder(const Expr_ptr expr)        \
    { assert(false); return false; }                         \
    void walk_## op ## _postorder(const Expr_ptr expr) {}

#define BINARY_STUB(op)                                      \
    bool walk_## op ## _preorder(const Expr_ptr expr)        \
    { assert(false); return false; }                         \
    bool walk_## op ## _inorder(const Expr_ptr expr)         \
    { assert(false); return false; }                         \
    void walk_## op ## _postorder(const Expr_ptr expr) {}

#define LTL_STUBS                                       \
    UNARY_STUB(F); UNARY_STUB(G); UNARY_STUB(X);        \
    BINARY_STUB(R); BINARY_STUB(U)

// enums in C++ are non-extensible, thus we have to keep all possible
// values together in one place.
typedef enum {
    DEFAULT,
    RETURN,

    // -- LTL ops
    F_1,
    G_1,
    X_1,
    U_1, U_2,
    R_1, R_2,

    // -- Simple walkers
    NEXT_1, PREV_1, NEG_1, NOT_1, BW_NOT_1,

    PLUS_1, PLUS_2,
    SUB_1, SUB_2,
    MUL_1, MUL_2,
    DIV_1, DIV_2,
    MOD_1, MOD_2,

    AND_1, AND_2,
    BW_AND_1, BW_AND_2,

    OR_1, OR_2,
    BW_OR_1, BW_OR_2,

    BW_XOR_1, BW_XOR_2,
    BW_XNOR_1, BW_XNOR_2,

    IMPLIES_1, IMPLIES_2,
    IFF_1, IFF_2,

    RSHIFT_1, RSHIFT_2,
    LSHIFT_1, LSHIFT_2,

    EQ_1, EQ_2,
    NE_1, NE_2,
    GT_1, GT_2,
    GE_1, GE_2,
    LT_1, LT_2,
    LE_1, LE_2,

    // ite
    ITE_1, ITE_2,
    COND_1, COND_2,

    // dot notation for identifiers
    DOT_1, DOT_2,

    // subscripts ([])
    SUBSCRIPT_1, SUBSCRIPT_2,

    // sets ({})
    SET_1,

    // params (())
    PARAMS_1, PARAMS_2,

    COMMA_1, COMMA_2,

    CAST_1, CAST_2,
    TYPE_1, TYPE_2,

} entry_point;

// reserved for walkers
struct activation_record {
    entry_point pc;
    Expr_ptr expr;

    activation_record(const Expr_ptr e)
        : pc(DEFAULT) , expr(e)
    {}
};

typedef stack<struct activation_record> walker_stack;

class WalkerException : public Exception
{
public:
    virtual const char* what() const throw() =0;
};

// raised when the walker has encountered an unsupported entry point
class UnsupportedEntryPointException : public WalkerException {
public:
    UnsupportedEntryPointException(entry_point ep)
        : f_ep(ep)
    {}

    virtual const char* what() const throw() {
        ostringstream oss;
        oss << "Unsupported entry point (" << f_ep << ")";
        return oss.str().c_str();
    }

private:
    entry_point f_ep;
};

// raised when the walker has encountered an unsupported operator
class UnsupportedOperatorException : public WalkerException {
public:
    UnsupportedOperatorException(ExprType et)
        : f_et(et)
    {}

    virtual const char* what() const throw() {
        ostringstream oss;
        oss << "Unsupported operator (" << f_et << ")";
        return oss.str().c_str();
    }

private:
    ExprType f_et;
};

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
    walker_stack f_recursion_stack;

    // -- hooks ----------------------------------------------------------------

    // ltl temporal op
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

    // unary temporal ops
    virtual bool walk_next_preorder(const Expr_ptr expr) =0;
    virtual void walk_next_postorder(const Expr_ptr expr) =0;

    virtual bool walk_prev_preorder(const Expr_ptr expr) =0;
    virtual void walk_prev_postorder(const Expr_ptr expr) =0;

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

    virtual bool walk_implies_preorder(const Expr_ptr expr) =0;
    virtual bool walk_implies_inorder(const Expr_ptr expr) =0;
    virtual void walk_implies_postorder(const Expr_ptr expr) =0;

    virtual bool walk_iff_preorder(const Expr_ptr expr) =0;
    virtual bool walk_iff_inorder(const Expr_ptr expr) =0;
    virtual void walk_iff_postorder(const Expr_ptr expr) =0;

    virtual bool walk_lshift_preorder(const Expr_ptr expr) =0;
    virtual bool walk_lshift_inorder(const Expr_ptr expr) =0;
    virtual void walk_lshift_postorder(const Expr_ptr expr) =0;

    virtual bool walk_rshift_preorder(const Expr_ptr expr) =0;
    virtual bool walk_rshift_inorder(const Expr_ptr expr) =0;
    virtual void walk_rshift_postorder(const Expr_ptr expr) =0;

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

    // ITE chains
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

    virtual bool walk_subscript_preorder(const Expr_ptr expr) =0;
    virtual bool walk_subscript_inorder(const Expr_ptr expr) =0;
    virtual void walk_subscript_postorder(const Expr_ptr expr) =0;

    virtual bool walk_set_preorder(const Expr_ptr expr) =0;
    virtual void walk_set_postorder(const Expr_ptr expr) =0;

    virtual bool walk_comma_preorder(const Expr_ptr expr) =0;
    virtual bool walk_comma_inorder(const Expr_ptr expr) =0;
    virtual void walk_comma_postorder(const Expr_ptr expr) =0;

    virtual bool walk_cast_preorder(const Expr_ptr expr) =0;
    virtual bool walk_cast_inorder(const Expr_ptr expr) =0;
    virtual void walk_cast_postorder(const Expr_ptr expr) =0;

    virtual bool walk_type_preorder(const Expr_ptr expr) =0;
    virtual bool walk_type_inorder(const Expr_ptr expr) =0;
    virtual void walk_type_postorder(const Expr_ptr expr) =0;

    // leaves
    virtual void walk_leaf(const Expr_ptr expr) =0;

};

#endif
