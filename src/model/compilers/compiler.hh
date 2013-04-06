/**
 *  @file compiler.hh
 *  @brief Boolean expressions compiler
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

#ifndef COMPILER_H
#define COMPILER_H
#include <simple_expr_walker.hh>

#include <type.hh>

#include <model.hh>
#include <model_mgr.hh>

#include <enc.hh>

#include <dd_walker.hh>

// NOTE: here we're using a vector in order to bypass STL stack
// interface limitations. (i.e. absence of clear())
typedef vector<ADD> ADDStack; // ouput of Stage 1
// typedef vector<YDD_ptr> YDDStack;  // output of Stage 2

typedef vector<Expr_ptr> ExprStack;
typedef vector<step_t>   TimeStack;

typedef unordered_map<FQExpr, DDVector, FQExprHash, FQExprEq> ADDMap;
typedef pair<ADDMap::iterator, bool> ADDHit;

typedef unordered_map<DdNode *, YDD_ptr, PtrHash, PtrEq> YDDMap;
typedef pair<YDDMap::iterator, bool> YDDHit;

typedef unordered_map<FQExpr, IEncoding_ptr, FQExprHash, FQExprEq> ENCMap;
typedef pair<ENCMap::iterator, bool> ENCHit;

/* shortcuts to to simplify manipulation of the internal ADD stack */
#define POP_ADD(op)                             \
    const ADD op = f_add_stack.back();          \
    f_add_stack.pop_back()

#define POP_TWO(rhs,lhs)                        \
    POP_ADD(rhs); POP_ADD(lhs)

#define POP_ALGEBRAIC(vec, width)               \
    ADD vec[width];                             \
    for (unsigned i = 0; i < width ; ++ i) {    \
        vec[i] = f_add_stack.back();            \
        f_add_stack.pop_back();                 \
    }

/* shortcut for pushing */
#define PUSH_ADD(add) f_add_stack.push_back(add)

class Compiler : public SimpleWalker {
public:
    Compiler();
    virtual ~Compiler();

    ADD process(Expr_ptr ctx, Expr_ptr body);

protected:
    clock_t f_elapsed; /* for benchmarking */
    void pre_hook();
    void post_hook();

    void pre_node_hook(Expr_ptr expr);
    void post_node_hook(Expr_ptr expr);

    // expr walker interface
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
    void walk_leaf(const Expr_ptr expr);

    unsigned f_temp_auto_index; // autoincr temp index

    ADDMap f_map;                 // FQDN -> DD cache
    ENCMap f_temp_encodings;      // FQDN -> DD encoding (for temporaries)

    // type look-ahead for operands promotion
    TypeStack f_type_stack;

    // partial results
    ADDStack f_add_stack;

    // current ctx stack, for symbol resolution
    ExprStack f_ctx_stack;

    // current time frame, for unrolling
    TimeStack f_time_stack;

    // experimental, FAR for integers
    // (fractioned algebraic representation)
    unsigned f_wwidth; // word width, default is 8 nibbles (=32 bits)

    // managers
    ModelMgr& f_owner;
    EncodingMgr& f_enc;

    /* -- expr inspectors ---------------------------------------------------- */
    bool is_binary_boolean(const Expr_ptr expr);
    bool is_unary_boolean(const Expr_ptr expr);
    bool is_ite_boolean(const Expr_ptr expr);

    bool is_binary_integer(const Expr_ptr expr);
    bool is_unary_integer(const Expr_ptr expr);
    bool is_ite_integer(const Expr_ptr expr);

    bool is_binary_fixed(const Expr_ptr expr);
    bool is_unary_fixed(const Expr_ptr expr);
    bool is_ite_fixed(const Expr_ptr expr);

    bool is_binary_enumerative(const Expr_ptr expr);
    bool is_unary_enumerative(const Expr_ptr expr);
    bool is_ite_enumerative(const Expr_ptr expr);

    bool is_binary_algebraic(const Expr_ptr expr);
    bool is_unary_algebraic(const Expr_ptr expr);
    bool is_ite_algebraic(const Expr_ptr expr);

    /* -- boolean exprs ----------------------------------------------------- */
    void boolean_not(const Expr_ptr expr);
    void boolean_and(const Expr_ptr expr);
    void boolean_or(const Expr_ptr expr);
    void boolean_xor(const Expr_ptr expr);
    void boolean_xnor(const Expr_ptr expr);
    void boolean_implies(const Expr_ptr expr);
    void boolean_equals(const Expr_ptr expr);
    void boolean_not_equals(const Expr_ptr expr);
    void boolean_ite(const Expr_ptr expr);

    /* -- const exprs ------------------------------------------------------- */
    void integer_neg(const Expr_ptr expr);
    void integer_not(const Expr_ptr expr);
    void integer_plus(const Expr_ptr expr);
    void integer_sub(const Expr_ptr expr);
    void integer_div(const Expr_ptr expr);
    void integer_mul(const Expr_ptr expr);
    void integer_mod(const Expr_ptr expr);
    void integer_and(const Expr_ptr expr);
    void integer_or(const Expr_ptr expr);
    void integer_xor(const Expr_ptr expr);
    void integer_xnor(const Expr_ptr expr);
    void integer_implies(const Expr_ptr expr);
    void integer_lshift(const Expr_ptr expr);
    void integer_rshift(const Expr_ptr expr);
    void integer_equals(const Expr_ptr expr);
    void integer_not_equals(const Expr_ptr expr);
    void integer_gt(const Expr_ptr expr);
    void integer_ge(const Expr_ptr expr);
    void integer_lt(const Expr_ptr expr);
    void integer_le(const Expr_ptr expr);
    void integer_ite(const Expr_ptr expr);

    void fixed_neg(const Expr_ptr expr);
    void fixed_plus(const Expr_ptr expr);
    void fixed_sub(const Expr_ptr expr);
    void fixed_div(const Expr_ptr expr);
    void fixed_mul(const Expr_ptr expr);
    void fixed_mod(const Expr_ptr expr);
    void fixed_equals(const Expr_ptr expr);
    void fixed_not_equals(const Expr_ptr expr);
    void fixed_gt(const Expr_ptr expr);
    void fixed_ge(const Expr_ptr expr);
    void fixed_lt(const Expr_ptr expr);
    void fixed_le(const Expr_ptr expr);
    void fixed_ite(const Expr_ptr expr);

    /* -- enumeratives ------------------------------------------------------ */
    void enumerative_equals(const Expr_ptr expr);
    void enumerative_not_equals(const Expr_ptr expr);
    void enumerative_ite(const Expr_ptr expr);

    /* -- algebraic exprs --------------------------------------------------- */
    void algebraic_neg(const Expr_ptr expr);
    void algebraic_not(const Expr_ptr expr);
    void algebraic_plus(const Expr_ptr expr);
    void algebraic_sub(const Expr_ptr expr);
    void algebraic_div(const Expr_ptr expr);
    void algebraic_mul(const Expr_ptr expr);
    void algebraic_mod(const Expr_ptr expr);
    void algebraic_and(const Expr_ptr expr);
    void algebraic_or(const Expr_ptr expr);
    void algebraic_xor(const Expr_ptr expr);
    void algebraic_xnor(const Expr_ptr expr);
    void algebraic_implies(const Expr_ptr expr);
    void algebraic_lshift(const Expr_ptr expr);
    void algebraic_rshift(const Expr_ptr expr);
    void algebraic_equals(const Expr_ptr expr);
    void algebraic_not_equals(const Expr_ptr expr);
    void algebraic_gt(const Expr_ptr expr);
    void algebraic_ge(const Expr_ptr expr);
    void algebraic_lt(const Expr_ptr expr);
    void algebraic_le(const Expr_ptr expr);
    void algebraic_ite(const Expr_ptr expr);

    /* -- internals --------------------------------------------------------- */
    bool cache_miss(const Expr_ptr expr);
    void memoize_result(const Expr_ptr expr);
    void flush_operands();

    /* push dds and type information for variables (used by walk_leaf) */
    void push_variable(IEncoding_ptr enc, Type_ptr type);

    ADD optimize_and_chain(ADD* dds, unsigned len);

    void algebraic_from_fxd_const(unsigned width);
    void algebraic_from_int_const(unsigned width);

    void algebraic_padding(unsigned old_width, unsigned new_width, bool is_signed);
    void algebraic_discard_op();

    /** @brief Determines type width */
    unsigned type_width(Type_ptr type);

    /** @brief Adjusts operand */
    void algebrize_operand(Type_ptr type, unsigned final_width);

    /** @brief Converts a fxd type into the corresponding int type,
        the new type width is equals to int_digits + fract_digits */
    Type_ptr algebraic_make_int_of_fxd_type(Type_ptr type);

    /** @brief Determines the width of an algebraic type */
    unsigned algebraic_type_width(Type_ptr type);

    /** @brief ITEs */
    unsigned algebrize_ternary_ite();

    /** @brief Binary arithmetical ops */
    unsigned algebrize_binary_arithmetical();

    /** @brief Binary relational ops */
    unsigned algebrize_binary_relational();

    /** @brief Subscripts */
    unsigned algebrize_unary_subscript();

    /* temporaries */
    Expr_ptr make_temporary_encoding(ADD dds[], unsigned width);
};

#endif
