/**
 * @file compiler.hh
 * @brief Propositional logic compiler
 *
 * This header file contains the declarations required to implement
 * the compilation of propositional logic expressions.
 *
 * Copyright (C) 2011-2015 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2.1 of
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

#ifndef COMPILER_H
#define COMPILER_H

/**
 * Current implementation uses DDs to perform expression
 * manipulation. The compilation engine is implemented using a simple
 * walker pattern: (a) on preorder, return true if the node has not
 * yet been visited; (b) always do in-order (for binary nodes); (c)
 * perform proper compilation in post-order hooks. Expressions are
 * checked to be type safe, The final result of expression compilation
 * shall be the conjunction of DDs suitable for CNF injection directly
 * into the SAT solver. In previous versions, the compiler used DDs
 * also to perform booleanization of algebraic
 * expressions. Experimental results proved this approach unfeasible
 * for realistic (i.e. >= 32) word sizes, at least for certain
 * operators. To circumvent this limitation a different approach is
 * needed. Therefore, for unary and binary algebraic operators as well
 * as relational operators all we do here is (1) pushing bit results
 * DDs representing boolean formulas for the results and (2) register
 * in a supporting complementary structure the information necessary
 * to fully express those results at a later stage.
 */

#include <dd/dd.hh>
#include <dd/dd_walker.hh>

#include <expr/walker/walker.hh>

#include <type/type.hh>

#include <enc/enc.hh>
#include <enc/enc_mgr.hh>

// #include <sat/helpers.hh>
#include <model/model.hh>
#include <model/model_mgr.hh>

#include <model/compiler/exceptions.hh>
#include <model/compiler/unit.hh>

#include <utils/time.hh>

#include <boost/unordered_map.hpp>
#include <boost/thread/mutex.hpp>

namespace model {

typedef boost::unordered_map<expr::TimedExpr, CompilationUnit,
                             expr::TimedExprHash, expr::TimedExprEq> CompilationMap;

typedef boost::unordered_map<expr::Expr_ptr, expr::Expr_ptr,
                             utils::PtrHash, utils::PtrEq> BinarySelectionUnionFindMap;


enum ECompilerStatus {
    READY,
    ENCODING,
    COMPILING,
    CHECKING,
    ACTIVATING_ITE_MUXES,
    ACTIVATING_ARRAY_MUXES
};

/* decl only */
ECompilerStatus& operator++(ECompilerStatus& status);

class Compiler : public expr::ExprWalker {
public:
    Compiler();
    virtual ~Compiler();

    CompilationUnit process(expr::Expr_ptr ctx, expr::Expr_ptr body);

private:
    /* Remark: the compiler does NOT support LTL ops. To enable
       verification of temporal properties, the LTL operators needs to
       be rewritten by the checking algorithm before feeding the
       formula into the compiler. */
    LTL_STUBS;

    /* basic expr operators support */
    OP_HOOKS;

    void walk_instant(const expr::Expr_ptr expr);
    void walk_leaf(const expr::Expr_ptr expr);

    /* push DDs and type information for variables (used by walk_leaf) */
    void push_dds(enc::Encoding_ptr enc, Type_ptr type);

    /* -- expr inspectors ---------------------------------------------------- */
    bool is_binary_boolean(const expr::Expr_ptr expr);
    bool is_unary_boolean(const expr::Expr_ptr expr);
    bool is_ite_boolean(const expr::Expr_ptr expr);

    bool is_binary_enumerative(const expr::Expr_ptr expr);
    bool is_unary_enumerative(const expr::Expr_ptr expr);
    bool is_ite_enumerative(const expr::Expr_ptr expr);

    bool is_binary_algebraic(const expr::Expr_ptr expr);
    bool is_unary_algebraic(const expr::Expr_ptr expr);
    bool is_ite_algebraic(const expr::Expr_ptr expr);

    bool is_binary_array(const expr::Expr_ptr expr);
    bool is_ite_array(const expr::Expr_ptr expr);

    bool is_subscript_boolean(const expr::Expr_ptr expr);
    bool is_subscript_enumerative(const expr::Expr_ptr expr);
    bool is_subscript_algebraic(const expr::Expr_ptr expr);

    /* -- boolean exprs ----------------------------------------------------- */
    void boolean_not(const expr::Expr_ptr expr);
    void boolean_and(const expr::Expr_ptr expr);
    void boolean_or(const expr::Expr_ptr expr);
    void boolean_xor(const expr::Expr_ptr expr);
    void boolean_implies(const expr::Expr_ptr expr);
    void boolean_iff(const expr::Expr_ptr expr);
    void boolean_equals(const expr::Expr_ptr expr);
    void boolean_not_equals(const expr::Expr_ptr expr);
    void boolean_ite(const expr::Expr_ptr expr);
    void boolean_subscript(const expr::Expr_ptr expr);

    /* -- algebraic exprs --------------------------------------------------- */
    void algebraic_neg(const expr::Expr_ptr expr);
    void algebraic_bw_not(const expr::Expr_ptr expr);
    void algebraic_plus(const expr::Expr_ptr expr);
    void algebraic_mul(const expr::Expr_ptr expr);
    void algebraic_sub(const expr::Expr_ptr expr);
    void algebraic_div(const expr::Expr_ptr expr);
    void algebraic_mod(const expr::Expr_ptr expr);
    void algebraic_bw_and(const expr::Expr_ptr expr);
    void algebraic_bw_or(const expr::Expr_ptr expr);
    void algebraic_bw_xor(const expr::Expr_ptr expr);
    void algebraic_bw_xnor(const expr::Expr_ptr expr);
    void algebraic_lshift(const expr::Expr_ptr expr);
    void algebraic_rshift(const expr::Expr_ptr expr);
    void algebraic_equals(const expr::Expr_ptr expr);
    void algebraic_not_equals(const expr::Expr_ptr expr);
    void algebraic_gt(const expr::Expr_ptr expr);
    void algebraic_ge(const expr::Expr_ptr expr);
    void algebraic_lt(const expr::Expr_ptr expr);
    void algebraic_le(const expr::Expr_ptr expr);
    void algebraic_ite(const expr::Expr_ptr expr);
    void algebraic_subscript(const expr::Expr_ptr expr);

    /* -- enumeratives ------------------------------------------------------ */
    void enumerative_equals(const expr::Expr_ptr expr);
    void enumerative_not_equals(const expr::Expr_ptr expr);
    void enumerative_ite(const expr::Expr_ptr expr);
    void enumerative_subscript(const expr::Expr_ptr expr);

    /* -- arrays ------------------------------------------------------------ */
    void array_equals(const expr::Expr_ptr expr);
    void array_ite(const expr::Expr_ptr expr);

    /* -- casts ------------------------------------------------------------- */
    void algebraic_cast_from_boolean(const expr::Expr_ptr expr);
    void boolean_cast_from_algebraic(const expr::Expr_ptr expr);
    void algebraic_cast_from_algebraic(const expr::Expr_ptr expr);

    /* -- internals --------------------------------------------------------- */

    /* algebraic manipulations */
    void algebraic_unary(const expr::Expr_ptr expr);
    void algebraic_binary(const expr::Expr_ptr expr);
    void algebraic_relational(const expr::Expr_ptr expr);
    void algebraic_constant(expr::Expr_ptr expr, unsigned width);

    /* cache management */
    void clear_internals();
    bool cache_miss(const expr::Expr_ptr expr);
    void memoize_result(const expr::Expr_ptr expr);

    /* encoding management */
    enc::Encoding_ptr find_encoding(const expr::TimedExpr& timed_expr, const Type_ptr type);

    /* automatic inner variables (determinization, muxes, etc...) */
    expr::Expr_ptr make_auto_id();
    void make_auto_ddvect(dd::DDVector& dv, unsigned width);
    ADD  make_auto_dd();

    void pre_hook();
    void post_hook();

    void pre_node_hook(expr::Expr_ptr expr);
    void post_node_hook(expr::Expr_ptr expr);

    /* compilation passes: building encodings, compilation */
    void build_encodings(expr::Expr_ptr ctx, expr::Expr_ptr body);
    void compile(expr::Expr_ptr ctx, expr::Expr_ptr body);

    /* post-processing stages */
    void check_internals(expr::Expr_ptr ctx, expr::Expr_ptr body);
    void activate_ite_muxes(expr::Expr_ptr ctx, expr::Expr_ptr body);
    void activate_array_muxes(expr::Expr_ptr ctx, expr::Expr_ptr body);

    /* -- data -------------------------------------------------------------- */

   /* TimedExpr -> Compilation Unit cache */
    CompilationMap f_compilation_cache;

    /* microcode descriptors */
    InlinedOperatorDescriptors f_inlined_operator_descriptors;

    /* Binary selection descriptors */
    Expr2BinarySelectionDescriptorsMap f_expr2bsd_map;

    /* Binary selection (ITEs) toplevels */
    BinarySelectionUnionFindMap f_bsuf_map;

    /* Multiway selection (Arrays) descriptors */
    MultiwaySelectionDescriptors f_multiway_selection_descriptors;

    /* type checking */
    TypeVector f_type_stack;

    /* compilation results */
    dd::DDVector f_add_stack;

    /* current ctx stack, for symbol resolution */
    expr::ExprVector f_ctx_stack;

    /* current time frame stack */
    utils::TimeVector f_time_stack;

    /* managers */
    ModelMgr& f_owner;
    enc::EncodingMgr& f_enc;

    /* Auto expressions and DDs */
    unsigned f_temp_auto_index;

    /* Compiler status (see above) */
    ECompilerStatus f_status;

    /* Time polarity (see above) */
    ECompilerTimePolarity f_time_polarity;

    const expr::Expr_ptr f_empty; /* debug only */

    /* synchronization */
    boost::mutex f_process_mutex;
};

};

#endif
