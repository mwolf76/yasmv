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
#include <expr_walker.hh>

#include <type.hh>

#include <model.hh>
#include <model_mgr.hh>

#include <enc.hh>

#include <dd_walker.hh>

// NOTE: here we're using a vector in order to bypass STL stack
// interface limitations. (i.e. absence of clear())
typedef vector<ADD> ADDStack; // ouput of Stage 1
// typedef vector<YDD_ptr> YDDStack;  // output of Stage 2

/* local typedefs */
typedef vector<Expr_ptr> ExprStack;
typedef vector<step_t>   TimeStack;

typedef unordered_map<FQExpr, DDVector, FQExprHash, FQExprEq> ADDMap;
typedef pair<ADDMap::iterator, bool> ADDHit;

typedef unordered_map<FQExpr, IEncoding_ptr, FQExprHash, FQExprEq> ENCMap;
typedef pair<ENCMap::iterator, bool> ENCHit;

typedef unordered_map<ADD, DDVector, ADDHash, ADDEq> ACMap; // and-chain
typedef pair<ACMap::iterator, bool> ACHit;

/* shortcuts to to simplify manipulation of the internal ADD stack */
#define POP_ADD(op)                             \
    const ADD op = f_add_stack.back();          \
    f_add_stack.pop_back()

#define POP_ALGEBRAIC(vec, width)               \
    ADD vec[width];                             \
    for (unsigned i = 0; i < width ; ++ i) {    \
        vec[i] = f_add_stack.back();            \
        f_add_stack.pop_back();                 \
    }

/* shortcut for pushing */
#define PUSH_ADD(add) f_add_stack.push_back(add)

class Compiler : public ExprWalker {
public:
    Compiler();
    virtual ~Compiler();

    void process(Expr_ptr ctx, Expr_ptr body, bool first_pass);

    /* implicit conjunctive chain returning protocol */
    bool has_next();
    ADD  next();

protected:
    clock_t f_elapsed; /* for benchmarking */
    void pre_hook();
    void post_hook();

    void pre_node_hook(Expr_ptr expr);
    void post_node_hook(Expr_ptr expr);

    OP_HOOKS;
    void walk_leaf(const Expr_ptr expr);

    unsigned f_temp_auto_index; // autoincr temp index

    ADDMap f_map;                 // FQDN -> DD cache
    ENCMap f_temp_encodings;      // FQDN -> DD encoding (for temporaries)

    DDVector f_roots;             // ADD chain roots
    ACMap  f_chains;              // chain root -> DD vector

    // type look-ahead for operands promotion
    TypeStack f_type_stack;

    // type look-ahead for relationals (used by ITEs)
    TypeStack f_rel_type_stack;

    // partial results
    ADDStack f_add_stack;

    // current ctx stack, for symbol resolution
    ExprStack f_ctx_stack;

    // current time frame, for unrolling
    TimeStack f_time_stack;

    // managers
    ModelMgr& f_owner;
    EncodingMgr& f_enc;

    // for profiling
    clock_t f_ticks;

    /* -- expr inspectors ---------------------------------------------------- */
    bool is_binary_boolean(const Expr_ptr expr);
    bool is_unary_boolean(const Expr_ptr expr);
    bool is_ite_boolean(const Expr_ptr expr);

    bool is_binary_integer(const Expr_ptr expr);
    bool is_unary_integer(const Expr_ptr expr);
    bool is_ite_integer(const Expr_ptr expr);
    bool is_subscript_integer(const Expr_ptr expr);

    bool is_binary_enumerative(const Expr_ptr expr);
    bool is_unary_enumerative(const Expr_ptr expr);
    bool is_ite_enumerative(const Expr_ptr expr);

    bool is_binary_algebraic(const Expr_ptr expr);
    bool is_unary_algebraic(const Expr_ptr expr);
    bool is_ite_algebraic(const Expr_ptr expr);

    bool is_binary_constant(const Expr_ptr expr);
    bool is_unary_constant(const Expr_ptr expr);
    bool is_ite_constant(const Expr_ptr expr);
    bool is_subscript_algebraic(const Expr_ptr expr);

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

    /* -- subscripts -------------------------------------------------------- */
    void integer_subscript(const Expr_ptr expr);
    void algebraic_subscript(const Expr_ptr expr);

    /* -- enumeratives ------------------------------------------------------ */
    void enumerative_equals(const Expr_ptr expr);
    void enumerative_not_equals(const Expr_ptr expr);
    void enumerative_ite(const Expr_ptr expr);

    /* -- algebraic exprs --------------------------------------------------- */
    void algebraic_neg(const Expr_ptr expr);
    void algebraic_not(const Expr_ptr expr);
    void algebraic_plus(const Expr_ptr expr);
    void algebraic_mul(const Expr_ptr expr);
    void algebraic_sub(const Expr_ptr expr);
    void algebraic_div(const Expr_ptr expr);
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

private:
    // Two pass compiler
    bool f_first;

    // karatsuba multiplication algorithm (EXPERIMENTAL)
    void karatsuba_mul(unsigned width);
    void karatsuba_mul_aux(unsigned width);
    void karatsuba_add_high_and_low(unsigned width);

    // recursive multiplication algorithm
    void recursive_mul_prepare_shift_and_pad(unsigned width, unsigned shift);
    void recursive_mul(unsigned width, bool extra);

    // traditional multiplication algorithm (fallback case)
    void longhand_mul(unsigned width, bool extra);

    /* casts */
    void algebraic_cast_from_boolean(const Expr_ptr expr);
    void boolean_cast_from_algebraic(const Expr_ptr expr);
    void algebraic_cast_from_algebraic(const Expr_ptr expr);

    /* -- internals --------------------------------------------------------- */
    bool cache_miss(const Expr_ptr expr);
    void memoize_result(const Expr_ptr expr);
    void relational_type_lookahead(const Expr_ptr expr);
    void relational_type_cleanup();
    void build_subscript_selector();
    void flush_operands();

    /* push dds and type information for variables (used by walk_leaf) */
    void push_variable(IEncoding_ptr enc, Type_ptr type);

    ADD book_and_chain(ADD* dds, unsigned len);
    void finalize_and_chains();

    void algebraic_from_constant(unsigned width);

    void algebraic_padding(unsigned old_width, unsigned new_width, bool is_signed);
    void algebraic_discard_op();

    /** @brief Determines type width */
    unsigned type_width(Type_ptr type);

    /** @brief Adjusts operand */
    void algebrize_operand(Type_ptr type, unsigned final_width);

    inline unsigned algebrize_binary_arithmetical()
    { return algebrize_operation(); }

    inline unsigned algebrize_binary_relational()
    { return algebrize_operation(false, true); }

    inline unsigned algebrize_ternary_ite()
    { return algebrize_operation(true, false); }

    /* core algebrization functions */
    unsigned algebrize_operation(bool ternary = false, bool relational = false);

    /* temporaries */
    Expr_ptr make_temporary_encoding(ADD dds[], unsigned width);
    BooleanEncoding_ptr make_chain_encoding();
};

#endif
