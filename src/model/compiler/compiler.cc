/**
 *  @file compiler.cc
 *  @brief Boolean expressions compiler
 *
 *  This module contains definitions and services that implement the
 *  booolean expressions compilation into a form which is suitable for
 *  subsequent phases of the model checking process. Current
 *  implementation uses CUDD ADDs to perform expression manipulation
 *  and booleanization. Expressions are assumed to be type-safe, only
 *  boolean expressions on arithmetic predicates are supported. The
 *  result of the compilation process must be a 0-1 ADD. This format
 *  is then suitable for Time-instantiation and then CNFization of the
 *  clauses injection directly into the SAT solver.
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

// comment this out to disable debug
// #define DEBUG_COMPILER

// comment this out to disable benchmarking
#define BENCHMARK_COMPILER

#include <common.hh>

#include <expr.hh>
#include <compiler.hh>

#include <proxy.hh>

Compiler::Compiler()
    : f_temp_auto_index(0)
    , f_map()
    , f_temp_encodings()
    , f_micro_descriptors()
    , f_type_stack()
    , f_add_stack()
    , f_ctx_stack()
    , f_time_stack()
    , f_owner(ModelMgr::INSTANCE())
    , f_enc(EncodingMgr::INSTANCE())
{
    DEBUG
        << "Created Compiler @"
        << this
        << endl;
}

Compiler::~Compiler()
{
    DEBUG
        << "Destroying Compiler @"
        << this
        << endl;
}

/* TODO: refactor pre and post hooks, they're pretty useless like this :-/ */
void Compiler::pre_hook()
{
}
void Compiler::post_hook()
{}

CompilationUnit Compiler::process(Expr_ptr ctx, Expr_ptr body)
{
    mutex::scoped_lock lock(f_process_mutex);

    f_elapsed = clock();

    /* pass 1: preprocessing */
    clear_internals();
    f_preprocess = true;

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);

    // toplevel (time is assumed at 0, arbitraryly nested next allowed)
    f_time_stack.push_back(0);

    /* Invoke walker on the body of the expr to be processed */
    (*this)(body);

    /* pass 2: compilation */
    clear_internals();
    f_preprocess = false;

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);

    // toplevel (time is assumed at 0, arbitraryly nested next allowed)
    f_time_stack.push_back(0);

    /* Invoke walker on the body of the expr to be processed */
    (*this)(body);

    // sanity conditions
    assert(1 == f_add_stack.size());
    assert(1 == f_type_stack.size());
    assert(1 == f_ctx_stack.size());
    assert(1 == f_time_stack.size());

    // Exactly one 0-1 ADD.
    ADD res = f_add_stack.back();
    assert( res.FindMin().Equals(f_enc.zero()) );
    assert( res.FindMax().Equals(f_enc.one()) );

    unsigned res_sz (f_add_stack.size());
    unsigned mcr_sz (f_micro_descriptors.size());
    unsigned mux_sz (f_mux_descriptors.size());

    f_elapsed = clock() - f_elapsed;
    double secs = (double) f_elapsed / (double) CLOCKS_PER_SEC;

    DEBUG
        << "Compilation of " << ctx << "::" << body
        << " took " << secs << " seconds, "
        << res_sz << " DDs, "
        << mcr_sz << " Microcode descriptors, "
        << mux_sz << " Multiplexer descriptors."
        << endl;

    return CompilationUnit( f_add_stack, f_micro_descriptors, f_mux_descriptors);
}

/*  Compilation engine is implemented using a simple expression walker
 *  pattern: (a) on preorder, return true if the node has not yet been
 *  visited; (b) always do in-order (for binary nodes); (c) perform
 *  proper compilation in post-order hooks. */
bool Compiler::walk_next_preorder(const Expr_ptr expr)
{
    step_t curr_time = f_time_stack.back();
    f_time_stack.push_back(curr_time + 1);
    return true;
}
void Compiler::walk_next_postorder(const Expr_ptr expr)
{
    assert (0 < f_time_stack.size());
    f_time_stack.pop_back(); // reset time stack
}

bool Compiler::walk_neg_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Compiler::walk_neg_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_unary_algebraic(expr)) {
        algebraic_neg(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Compiler::walk_not_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_unary_boolean(expr)) {
        boolean_not(expr);
    }
    else assert(false); // unreachable
}

bool Compiler::walk_bw_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Compiler::walk_bw_not_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_unary_algebraic(expr)) {
        algebraic_bw_not(expr); // bitwise
    }
    else assert(false); // unreachable
}

bool Compiler::walk_add_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_add_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_add_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_algebraic(expr)) {
        algebraic_plus(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_sub_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_sub_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_sub_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_algebraic(expr)) {
        algebraic_sub(expr);
    }
    else assert( false ); // unexpected
}

bool Compiler::walk_div_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_div_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_div_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_algebraic(expr)) {
        algebraic_div(expr);
    }
    else assert( false ); // unexpected
}

bool Compiler::walk_mul_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_mul_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_mul_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_algebraic(expr)) {
        algebraic_mul(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_mod_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_mod_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_mod_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_algebraic(expr)) {
        algebraic_mod(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_and_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_and_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_boolean(expr)) {
        boolean_and(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_bw_and_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_bw_and_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_bw_and_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_algebraic(expr)) {
        algebraic_bw_and(expr); // bitwise
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_or_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_boolean(expr)) {
        boolean_or(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_bw_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_bw_or_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_bw_or_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_algebraic(expr)) {
        algebraic_bw_or(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_bw_xor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_bw_xor_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_bw_xor_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_algebraic(expr)) {
        algebraic_bw_xor(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_bw_xnor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_bw_xnor_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_bw_xnor_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_algebraic(expr)) {
        algebraic_bw_xnor(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_implies_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_implies_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_boolean(expr)) {
        boolean_implies(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_iff_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_iff_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_iff_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_boolean(expr)) {
        boolean_iff(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_type_preorder(const Expr_ptr expr)
{
    Type_ptr tp = f_owner.tm().find_type_by_def(expr);
    f_type_stack.push_back( tp);
    return false;
}
bool Compiler::walk_type_inorder(const Expr_ptr expr)
{
    assert( false ); /* unreachable */
    return false;
}
void Compiler::walk_type_postorder(const Expr_ptr expr)
{
    assert( false ); /* unreachable */
}

bool Compiler::walk_cast_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_cast_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_cast_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    Expr_ptr ctx (f_ctx_stack.back());
    Type_ptr tgt_type = f_owner.type( expr->lhs(), ctx);
    Type_ptr src_type = f_owner.type( expr->rhs(), ctx);

    assert (f_type_stack.back() == src_type);
    f_type_stack.pop_back();
    f_type_stack.pop_back();
    f_type_stack.push_back( tgt_type);

    if (src_type -> is_boolean() &&
        tgt_type -> is_boolean()) {
        return; /* nop */
    }
    else if (src_type -> is_boolean() &&
        tgt_type -> is_algebraic()) {
        algebraic_cast_from_boolean(expr);
    }
    else if (src_type -> is_algebraic() &&
             tgt_type -> is_boolean()) {
        boolean_cast_from_algebraic(expr);
    }
    else if (src_type -> is_algebraic() &&
             tgt_type -> is_algebraic()) {
        algebraic_cast_from_algebraic(expr);
    }
    else assert (false); // unreachable
}

bool Compiler::walk_lshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_lshift_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_lshift_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_algebraic(expr)) {
        algebraic_lshift(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_rshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_rshift_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_rshift_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_algebraic(expr)) {
        algebraic_rshift(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_eq_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_eq_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_eq_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_boolean(expr)) {
        boolean_equals(expr);
    }
    if (is_binary_enumerative(expr)) {
        enumerative_equals(expr);
    }
    else if (is_binary_algebraic(expr)) {
        algebraic_equals(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_ne_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_ne_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_ne_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_boolean(expr)) {
        boolean_not_equals(expr);
    }
    if (is_binary_enumerative(expr)) {
        enumerative_not_equals(expr);
    }
    else if (is_binary_algebraic(expr)) {
        algebraic_not_equals(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_gt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_gt_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_gt_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_algebraic(expr)) {
        algebraic_gt(expr);
    }
    else assert( false );
}

bool Compiler::walk_ge_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_ge_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_ge_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_algebraic(expr)) {
        algebraic_ge(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_lt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_lt_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_lt_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_algebraic(expr)) {
        algebraic_lt(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_le_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_le_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_le_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_binary_algebraic(expr)) {
        algebraic_le(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_ite_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_ite_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_ite_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    if (is_ite_boolean(expr)) {
        boolean_ite(expr);
    }
    else if (is_ite_enumerative(expr)) {
        enumerative_ite(expr);
    }
    else if (is_ite_algebraic(expr)) {
        algebraic_ite(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_cond_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_cond_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_cond_postorder(const Expr_ptr expr)
{
    Expr_ptr cnd (expr->lhs());
    DEBUG
        << cnd
        << endl;


}

bool Compiler::walk_dot_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_dot_inorder(const Expr_ptr expr)
{
    // ADD tmp = f_add_stack.back();
    // Expr_ptr ctx = tmp->get_repr();
    // f_ctx_stack.push_back(ctx);
    return true;
}
void Compiler::walk_dot_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;

    // ADD rhs_add;

    // { // RHS, no checks necessary/possible
    //     const ADD top = f_add_stack.back(); f_add_stack.pop_back();
    //     rhs_add = top;
    // }

    // { // LHS, must be an instance (by assertion, otherwise leaf would have fail)
    //     const ADD top = f_add_stack.back(); f_add_stack.pop_back();
    //     assert(tm.is_instance(top));
    // }

    // // propagate rhs add
    // f_add_stack.push_back(rhs_add);

    // // restore previous ctx
    // f_ctx_stack.pop_back();
}

/* on-demand preprocessing to expand defines delegated to Preprocessor */
bool Compiler::walk_params_preorder(const Expr_ptr expr)
{
    Expr_ptr ctx = f_ctx_stack.back();
    (*this)( f_owner.preprocess( expr, ctx));

    return false;
}
bool Compiler::walk_params_inorder(const Expr_ptr expr)
{ assert( false ); return false; /* unreachable */ }
void Compiler::walk_params_postorder(const Expr_ptr expr)
{ assert( false ); return ; /* unreachable */ }

bool Compiler::walk_subscript_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_subscript_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_subscript_postorder(const Expr_ptr expr)
{
    if (f_preprocess)
        return;
    if (is_subscript_algebraic(expr)) {
        algebraic_subscript(expr);
    }
    else assert( false ); // unreachable
}

bool Compiler::walk_set_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Compiler::walk_set_postorder(const Expr_ptr expr)
{ assert (false); /* TODO support inlined non-determinism */ }

bool Compiler::walk_comma_preorder(const Expr_ptr expr)
{  return cache_miss(expr); }

bool Compiler::walk_comma_inorder(const Expr_ptr expr)
{ return true; }

void Compiler::walk_comma_postorder(const Expr_ptr expr)
{ assert (false); /* TODO support inlined non-determinism */ }

/* private service of walk_leaf */
void Compiler::push_variable(IEncoding_ptr enc, Type_ptr type)
{
    assert (NULL != enc);
    DDVector& dds = enc->dv();
    unsigned width = dds.size();
    assert( 0 < width );

    // push into type stack
    f_type_stack.push_back(type);

    /* booleans, monoliths are just one DD */
    if (type->is_monolithical())
        f_add_stack.push_back(dds[0]);

    /* algebraics, reversed list of encoding DDs */
    else if (type->is_algebraic()) {
        // type and enc width info has to match
        assert( type -> as_algebraic()-> width() == width );
        for (DDVector::reverse_iterator ri = dds.rbegin();
             ri != dds.rend(); ++ ri) {
            f_add_stack.push_back(*ri);
        }
    }

    /* array of algebraics, same as above, times nelems (!) */
    else if (type->is_array()) {

        // type and enc width info has to match
        assert( type -> as_array() -> of() -> as_algebraic()-> width() ==
                width / type -> as_array() -> nelems());

        for (DDVector::reverse_iterator ri = dds.rbegin();
             ri != dds.rend(); ++ ri) {
            f_add_stack.push_back(*ri);
        }
    }

    else assert( false ); // unexpected
}

void Compiler::walk_leaf(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* cached? */
    if (! cache_miss(expr)) return;

    Expr_ptr ctx = f_ctx_stack.back();
    step_t time = f_time_stack.back();

    FQExpr2EncMap::const_iterator eye;
    IEncoding_ptr enc = NULL;

    // 1. Explicit integer consts, perform booleanization immediately using
    // word-width property to determine the number of bits to be used.
    if (em.is_numeric(expr)) {
        unsigned ww (OptsMgr::INSTANCE().word_width());
        f_type_stack.push_back(tm.find_unsigned(ww));
        algebraic_from_constant( expr, ww);
        return;
    }

    ResolverProxy resolver;
    ISymbol_ptr symb = resolver.symbol(ctx, expr);;

    // 2. Temporary symbols are maintained internally by the compiler
    ITemporary_ptr temp;
    if (NULL != (temp = dynamic_cast<ITemporary_ptr>(symb))) {
        Type_ptr type = NULL;

        type = symb->as_variable().type();
        assert(type->is_algebraic());

        // temporary encodings must be already defined.
        FQExpr key(ExprMgr::INSTANCE().make_main(), expr, time);

        eye = f_temp_encodings.find(key);
        if (eye != f_temp_encodings.end()) {
            enc = eye -> second;
        }
        else assert(false); // unexpected

        push_variable(enc, type);
        return;
    } /* Temporary symbols */

    // 3. bool/integer constant leaves
    if (symb->is_const()) {
        IConstant& konst = symb->as_const();

        f_type_stack.push_back(konst.type());
        f_add_stack.push_back(f_enc.constant(konst.value()));
        return;
    }

    // 4. enum literals
    if (symb->is_literal()) {
        ILiteral& konst =  symb->as_literal();

        // push into type stack
        Type_ptr type = konst.type();

        // if encoding for variable is available reuse it,
        // otherwise create and cache it.
        FQExpr key(ctx, expr, time);

        /* build a new encoding for this symbol if none is available. */
        if (NULL == (enc = f_enc.find_encoding(key))) {
            assert (NULL != type);
            enc = f_enc.make_encoding(type);
            f_enc.register_encoding(key, enc);
        }

        EnumEncoding_ptr eenc = dynamic_cast<EnumEncoding_ptr>( enc );
        assert( NULL != eenc );

        f_type_stack.push_back(konst.type());
        f_add_stack.push_back(f_enc.constant(eenc -> value( expr )));
        return;
    }

    // 5.  variables
    else if (symb->is_variable()) {

        // push into type stack
        Type_ptr type = symb->as_variable().type();

        // if encoding for variable is available reuse it,
        // otherwise create and cache it.
        FQExpr key(ctx, expr, time);

        /* build a new encoding for this symbol if none is available. */
        if (NULL == (enc = f_enc.find_encoding(key))) {
            if (f_preprocess) {
                assert (NULL != type);
                enc = f_enc.make_encoding(type);
                f_enc.register_encoding(key, enc);
            }
            else assert( false ); // unexpected
        }

        push_variable(enc, type);
        return;
    } /* variables */

    // 6 Defines. Simply compile it recursively.  We keep this to
    // retain the old lazy behavior with nullary defines since it
    // comes at no extra cost at all.
    else if (symb->is_define()) {
        (*this)(symb->as_define().body());
        return;
    }

    assert( false ); /* give up, TODO: exception */
}
