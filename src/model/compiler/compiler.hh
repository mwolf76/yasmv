/**
 *  @file compiler.hh
 *  @brief Basic expressions compiler
 *
 *  This module contains definitions and services that implement the
 *  booolean expressions compilation into a form which is suitable for
 *  the SAT analysis. Current implementation uses ADDs to perform
 *  expression manipulation. Expressions are assumed to be type-safe,
 *  The final result of expression compilation shall be a 0-1 ADD_
 *  suitable for CNF clauses injection directly into the SAT
 *  solver. In previous versione, the compiler used ADDs also to
 *  perform booleanization of algebraic expressions. Experimental
 *  results proved this approach unfeasible for realistic (i.e. >= 32)
 *  word sizes, at least for certain operators. To circumvent this
 *  limitation a different approach is needed. Therefore, for binary
 *  algebraic operators (i.e. SUB, PLUS, MUL, MOD, DIV) all we do here
 *  is (1) pushing bit results ADDs representing boolean formulas for
 *  the results and (2) register in a supporting complementary
 *  structure the information necessary to fully express those results
 *  at a later stage. The compilation engine is implemented using a
 *  simple walker pattern: (a) on preorder, return true if the node
 *  has not yet been visited; (b) always do in-order (for binary
 *  nodes); (c) perform proper compilation in post-order hooks.
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
#include <enc_mgr.hh>

#include <micro.hh>

#include <dd_walker.hh>

#include <compiler/term.hh>

// NOTE: here we're using a vector in order to bypass STL stack
// interface limitations. (i.e. absence of clear())
typedef vector<ADD> ADDStack; // ouput of Stage 1

/* local typedefs */
typedef vector<Expr_ptr> ExprStack;
typedef vector<step_t>   TimeStack;

typedef unordered_map<FQExpr, pair<DDVector, MicroDescriptors>, FQExprHash, FQExprEq> ADDMap;
typedef unordered_map<ADD, DDVector, ADDHash, ADDEq> ANDChainMap;

/* shortcuts to to simplify manipulation of the internal ADD stack */
#define POP_ADD(op)                             \
    const ADD op = f_add_stack.back();          \
    f_add_stack.pop_back()

#define POP_ALGEBRAIC(vec, width)               \
    DDVector vec;                               \
    for (unsigned i = 0; i < width ; ++ i) {    \
        vec.push_back(f_add_stack.back());      \
        f_add_stack.pop_back();                 \
    }

#define FRESH_DV(vec, width)                    \
    DDVector vec;                               \
    make_auto_ddvect(vec, width);               \
    /* push DD vector in reversed order */      \
    for (unsigned i = 0; i < width; ++ i) {     \
        unsigned ndx = width - i - 1;           \
        PUSH_ADD(vec[ndx]);                     \
    }

#define FRESH_DD(var)                           \
    ADD var = make_auto_dd()

/* shortcut for pushing */
#define PUSH_ADD(add)                           \
    f_add_stack.push_back(add)

/** Exception classes */
class CompilerException : public Exception {
public:
    virtual const char* what() const throw() =0;
};

/** Raised when a constant could not fit into a native word */
class ConstantTooLarge : public CompilerException {
    Expr_ptr f_repr;

public:
    ConstantTooLarge(Expr_ptr expr);

    const char* what() const throw();
    ~ConstantTooLarge() throw();
};

class Compiler : public ExprWalker {
public:
    Compiler();
    virtual ~Compiler();

    Term process(Expr_ptr ctx, Expr_ptr body);

protected:
    clock_t f_elapsed; /* for benchmarking */
    void pre_hook();
    void post_hook();

    void pre_node_hook(Expr_ptr expr);
    void post_node_hook(Expr_ptr expr);

    /* Model compiler does NOT support LTL ops. To enable verification
     of temporal properties, the LTL operators needs to be rewritten
     by the bmc algorithms before feeding the formula into the
     compiler. */
    LTL_STUBS;

    /* basic expr operators support */
    OP_HOOKS;

    void walk_leaf(const Expr_ptr expr);

    unsigned f_temp_auto_index; // autoincr temp index

    // FQDN -> DD cache
    ADDMap f_map;

    // FQDN -> temporarry DD encodings
    FQExpr2EncMap f_temp_encodings;

    // microcode descriptors
    MicroDescriptors f_descriptors;

    // look-ahead for type checking
    TypeStack f_type_stack;

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

    bool is_subscript_algebraic(const Expr_ptr expr);

    /* -- boolean exprs ----------------------------------------------------- */
    void boolean_not(const Expr_ptr expr);
    void boolean_and(const Expr_ptr expr);
    void boolean_or(const Expr_ptr expr);
    void boolean_implies(const Expr_ptr expr);
    void boolean_iff(const Expr_ptr expr);
    void boolean_equals(const Expr_ptr expr);
    void boolean_not_equals(const Expr_ptr expr);
    void boolean_ite(const Expr_ptr expr);

    /* -- int const exprs ---------------------------------------------------- */
    void integer_neg(const Expr_ptr expr);
    void integer_bw_not(const Expr_ptr expr);
    void integer_plus(const Expr_ptr expr);
    void integer_sub(const Expr_ptr expr);
    void integer_div(const Expr_ptr expr);
    void integer_mul(const Expr_ptr expr);
    void integer_mod(const Expr_ptr expr);
    void integer_bw_and(const Expr_ptr expr);
    void integer_bw_or(const Expr_ptr expr);
    void integer_bw_xor(const Expr_ptr expr);
    void integer_bw_xnor(const Expr_ptr expr);
    void integer_lshift(const Expr_ptr expr);
    void integer_rshift(const Expr_ptr expr);
    void integer_equals(const Expr_ptr expr);
    void integer_not_equals(const Expr_ptr expr);
    void integer_gt(const Expr_ptr expr);
    void integer_ge(const Expr_ptr expr);
    void integer_lt(const Expr_ptr expr);
    void integer_le(const Expr_ptr expr);
    void integer_ite(const Expr_ptr expr);

    /* -- algebraic exprs --------------------------------------------------- */
    void algebraic_neg(const Expr_ptr expr);
    void algebraic_bw_not(const Expr_ptr expr);
    void algebraic_plus(const Expr_ptr expr);
    void algebraic_mul(const Expr_ptr expr);
    void algebraic_sub(const Expr_ptr expr);
    void algebraic_div(const Expr_ptr expr);
    void algebraic_mod(const Expr_ptr expr);
    void algebraic_bw_and(const Expr_ptr expr);
    void algebraic_bw_or(const Expr_ptr expr);
    void algebraic_bw_xor(const Expr_ptr expr);
    void algebraic_bw_xnor(const Expr_ptr expr);
    void algebraic_lshift(const Expr_ptr expr);
    void algebraic_rshift(const Expr_ptr expr);
    void algebraic_equals(const Expr_ptr expr);
    void algebraic_not_equals(const Expr_ptr expr);
    void algebraic_gt(const Expr_ptr expr);
    void algebraic_ge(const Expr_ptr expr);
    void algebraic_lt(const Expr_ptr expr);
    void algebraic_le(const Expr_ptr expr);
    void algebraic_ite(const Expr_ptr expr);

    /* -- subscripts -------------------------------------------------------- */
    void integer_subscript(const Expr_ptr expr);
    void algebraic_subscript(const Expr_ptr expr);

    /* -- enumeratives ------------------------------------------------------ */
    void enumerative_equals(const Expr_ptr expr);
    void enumerative_not_equals(const Expr_ptr expr);
    void enumerative_ite(const Expr_ptr expr);

private:
    mutex f_process_mutex;
    bool f_preprocess;

    /* casts */
    void algebraic_cast_from_boolean(const Expr_ptr expr);
    void boolean_cast_from_algebraic(const Expr_ptr expr);
    void algebraic_cast_from_algebraic(const Expr_ptr expr);

    /* -- internals --------------------------------------------------------- */
    void clear_internals();
    bool cache_miss(const Expr_ptr expr);
    void memoize_result(const Expr_ptr expr);
    void build_subscript_selector();
    void flush_operands();

    /* microcode-based algebraic binary ops: supports PLUS, SUB, MUL, DIV, MOD */
    void algebraic_binary_microcode_operation(const Expr_ptr expr);

    /* microcode-based relationals: supports EQ, NE, GE, GT, LE, LT */
    void algebraic_binary_microcode_relational(const Expr_ptr expr);

    /* push dds and type information for variables (used by walk_leaf) */
    void push_variable(IEncoding_ptr enc, Type_ptr type);

    void algebraic_from_constant(Expr_ptr expr, unsigned width);

    /** @brief Determines type width */
    unsigned type_width(Type_ptr type);

    // aliases for algebrize_operation
    // inline void algebrize_binary_arithmetical(unsigned& width, bool& signedness)
    // { algebrize_operation(false, false, width, signedness); }

    // inline void algebrize_binary_relational(unsigned& width, bool& signedness)
    // { algebrize_operation(false, true, width, signedness); }

    // inline void algebrize_ternary_ite(unsigned& width, bool& signedness)
    // { algebrize_operation(true, false, width, signedness); }

    // /** critical low-level service */
    // void algebrize_operation(bool ternary, bool relational,
    //                          unsigned& width, bool& signedness);

    /* Auto expressions and DDs */
    Expr_ptr make_auto_id();
    Expr_ptr make_temporary_expr(ADD dds[], unsigned width);
    void make_auto_ddvect(DDVector& dv, unsigned width);
    ADD  make_auto_dd();

    void algebraic_binary(const Expr_ptr expr);
    void algebraic_relational(const Expr_ptr expr);
    void register_microdescriptor( bool signedness, ExprType symb, unsigned width,
                                   DDVector& z, DDVector& x, DDVector &y );
};

#endif
