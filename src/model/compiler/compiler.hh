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

#include <dd/dd.hh>
#include <dd/dd_walker.hh>

#include <expr/walker/walker.hh>

#include <type/type.hh>

#include <enc/enc.hh>
#include <enc/enc_mgr.hh>

#include <micro/micro.hh>
#include <model/model.hh>
#include <model/model_mgr.hh>

#include <model/compiler/exceptions.hh>
#include <model/compiler/unit.hh>

#include <boost/unordered_map.hpp>
typedef boost::unordered_map<TimedExpr, CompilationUnit, TimedExprHash, TimedExprEq> CompilationMap;
typedef boost::unordered_map<Expr_ptr, Expr_ptr, PtrHash, PtrEq> ITEUnionFindMap;

#include <boost/thread/mutex.hpp>

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
    void push_dds(Encoding_ptr enc, Type_ptr type);

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
    void boolean_xor(const Expr_ptr expr);
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

    /* -- casts ------------------------------------------------------------- */
    void algebraic_cast_from_boolean(const Expr_ptr expr);
    void boolean_cast_from_algebraic(const Expr_ptr expr);
    void algebraic_cast_from_algebraic(const Expr_ptr expr);

    /* -- internals --------------------------------------------------------- */
    void clear_internals();
    bool cache_miss(const Expr_ptr expr);
    void memoize_result(const Expr_ptr expr);
    Encoding_ptr find_encoding( const TimedExpr& timed_expr, const Type_ptr type);

    void algebraic_from_constant(Expr_ptr expr, unsigned width);

    Expr_ptr make_auto_id();
    void make_auto_ddvect(DDVector& dv, unsigned width);
    ADD  make_auto_dd();

    void algebraic_unary(const Expr_ptr expr);
    void algebraic_binary(const Expr_ptr expr);
    void algebraic_relational(const Expr_ptr expr);

    void pre_hook();
    void post_hook();

    void pre_node_hook(Expr_ptr expr);
    void post_node_hook(Expr_ptr expr);

    /* TimedExpr -> < DD, micros, imuxes, amuxes > cache */
    CompilationMap f_cache;

    /* microcode descriptors */
    InlinedOperatorDescriptors f_inlined_operator_descriptors;

    /* mux descriptors */
    Expr2BSDMap f_expr2bsd_map;
    MultiwaySelectionDescriptors f_multiway_selection_descriptors;

    /* ITE toplevels */
    ITEUnionFindMap f_ite_uf_map;

    /* type checking */
    TypeVector f_type_stack;

    /* compilation results */
    DDVector f_add_stack;

    /* current ctx stack, for symbol resolution */
    ExprVector f_ctx_stack;

    /* current time frame stack */
    TimeVector f_time_stack;

    /* managers */
    ModelMgr& f_owner;
    EncodingMgr& f_enc;

    /* Auto expressions and DDs */
    unsigned f_temp_auto_index;

    // TODO: can we get rid of this?
    bool f_preprocess;

    /* synchronization */
    boost::mutex f_process_mutex;
};

#endif
