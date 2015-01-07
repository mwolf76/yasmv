/**
 *  @file compiler.hh
 *  @brief Propositional logic compiler
 *
 *  This module contains definitions and services that implement the
 *  compilation of propositional logic expressions into a form which
 *  is suitable for subsequent phases of the model checking
 *  process. Current implementation uses DDs to perform expression
 *  manipulation. The compilation engine is implemented using a simple
 *  walker pattern: (a) on preorder, return true if the node has not
 *  yet been visited; (b) always do in-order (for binary nodes); (c)
 *  perform proper compilation in post-order hooks. Expressions are
 *  checked to be type safe, The final result of expression
 *  compilation shall be the conjunction of DDs suitable for CNF
 *  injection directly into the SAT solver. In previous versions, the
 *  compiler used DDs also to perform booleanization of algebraic
 *  expressions. Experimental results proved this approach unfeasible
 *  for realistic (i.e. >= 32) word sizes, at least for certain
 *  operators. To circumvent this limitation a different approach is
 *  needed. Therefore, for unary and binary algebraic operators as
 *  well as relational operators all we do here is (1) pushing bit
 *  results DDs representing boolean formulas for the results and (2)
 *  register in a supporting complementary structure the information
 *  necessary to fully express those results at a later stage.
 *
 *  Copyright (C) 2011-2015 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License as
 *  published by the Free Software Foundation; either version 2.1 of
 *  the License, or (at your option) any later version.
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

#include <compiler/unit.hh>

// NOTE: here we're using a vector in order to bypass STL stack
// interface limitations. (i.e. absence of clear())
typedef vector<ADD> ADDStack;

/* local typedefs */
typedef vector<Expr_ptr> ExprList;
typedef vector<step_t>   TimeStack;

typedef unordered_map<FQExpr, CompilationUnit, FQExprHash, FQExprEq> CompilationMap;

/* -- shortcuts to simplify the manipulation of the internal DD stack ------- */

/** Fetch a single DD */
#define POP_DD(op)                              \
    const ADD op = f_add_stack.back();          \
    f_add_stack.pop_back()

/** Declare a fresh DD */
#define FRESH_DD(var)                           \
    ADD var = make_auto_dd()

/** Push a single DD */
#define PUSH_DD(add)                            \
    f_add_stack.push_back(add)

/** Fetch a DD vector of given width */
#define POP_DV(vec, width)                      \
    DDVector vec;                               \
    for (unsigned i = 0; i < width ; ++ i) {    \
        vec.push_back(f_add_stack.back());      \
        f_add_stack.pop_back();                 \
    }

/** Declare a DD vector of given width */
#define FRESH_DV(vec, width)                    \
    DDVector vec;                               \
    make_auto_ddvect(vec, width);               \
    /* push DD vector in reversed order */      \
    for (unsigned i = 0; i < width; ++ i) {     \
        unsigned ndx = width - i - 1;           \
        PUSH_DD(vec[ndx]);                      \
    }

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

    CompilationUnit process(Expr_ptr ctx, Expr_ptr body);

private:
    /* Remark: the compiler does NOT support LTL ops. To enable
       verification of temporal properties, the LTL operators needs to
       be rewritten by the bmc algorithms before feeding the formula
       into the compiler. */
    LTL_STUBS;

    /* basic expr operators support */
    OP_HOOKS;

    void walk_leaf(const Expr_ptr expr);

    /* push DDs and type information for variables (used by walk_leaf) */
    void push_dds(IEncoding_ptr enc, Type_ptr type);

    /* -- expr inspectors ---------------------------------------------------- */
    bool is_binary_boolean(const Expr_ptr expr);
    bool is_unary_boolean(const Expr_ptr expr);
    bool is_ite_boolean(const Expr_ptr expr);

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
    void algebraic_subscript(const Expr_ptr expr);

    /* -- enumeratives ------------------------------------------------------ */
    void enumerative_equals(const Expr_ptr expr);
    void enumerative_not_equals(const Expr_ptr expr);
    void enumerative_ite(const Expr_ptr expr);

    /* casts */
    void algebraic_cast_from_boolean(const Expr_ptr expr);
    void boolean_cast_from_algebraic(const Expr_ptr expr);
    void algebraic_cast_from_algebraic(const Expr_ptr expr);

    /* -- internals --------------------------------------------------------- */
    void clear_internals();
    bool cache_miss(const Expr_ptr expr);
    void memoize_result(const Expr_ptr expr);

    void algebraic_from_constant(Expr_ptr expr, unsigned width);

    /** @brief Determines type width */
    // unsigned type_width(Type_ptr type);

    Expr_ptr make_auto_id();
    Expr_ptr make_temporary_expr(ADD dds[], unsigned width);
    void make_auto_ddvect(DDVector& dv, unsigned width);
    ADD  make_auto_dd();

    void algebraic_unary(const Expr_ptr expr);
    void algebraic_binary(const Expr_ptr expr);
    void algebraic_relational(const Expr_ptr expr);

    /* microcode support */
    void register_microdescriptor( bool signedness, ExprType symb, unsigned width,
                                   DDVector& z, DDVector& x );
    void register_microdescriptor( bool signedness, ExprType symb, unsigned width,
                                   DDVector& z, DDVector& x, DDVector &y );

    /* MUX support */
    void register_muxdescriptor( unsigned width, DDVector& z, ADD a,
                                 DDVector& x, DDVector &y );

    // FQDN -> ( DD, micros, mux ) cache
    CompilationMap f_cache;

    // FQDN -> temporary DD encodings
    FQExpr2EncMap f_temp_encodings;

    // microcode descriptors
    MicroDescriptors f_micro_descriptors;

    // mux descriptors
    MuxDescriptors f_mux_descriptors;

    // look-ahead for type checking
    TypeStack f_type_stack;

    // partial results
    ADDStack f_add_stack;

    // current ctx stack, for symbol resolution
    ExprList f_ctx_stack;

    // current time frame, for unrolling
    TimeStack f_time_stack;

    // managers
    ModelMgr& f_owner;
    EncodingMgr& f_enc;

    /* Auto expressions and DDs */
    unsigned f_temp_auto_index;

    // TODO: can we get rid of this?
    bool f_preprocess;

    /* synchronization */
    mutex f_process_mutex;

    clock_t f_elapsed; /* for benchmarking */

    void pre_hook();
    void post_hook();

    void pre_node_hook(Expr_ptr expr);
    void post_node_hook(Expr_ptr expr);

};

#endif
