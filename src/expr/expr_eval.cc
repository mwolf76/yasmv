/**
 *  @file expr_eval.cc
 *  @brief Expr evaluator
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

#include <common.hh>

#include <expr.hh>
#include <expr_eval.hh>

Evaluator::Evaluator()
{
    DEBUG << "Created Evaluator @" << this << endl;
}

Evaluator::~Evaluator()
{
    DEBUG << "Destroying Evaluator @" << this << endl;
}

void Evaluator::pre_hook()
{}

void Evaluator::post_hook()
{}

Expr_ptr Evaluator::process(Expr_ptr ctx, Expr_ptr body, step_t time)
{
    // remove previous results
    f_expr_stack.clear();
    f_ctx_stack.clear();
    f_time_stack.clear();

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);

    // toplevel (time is assumed at 0, arbitraryly nested next allowed)
    f_time_stack.push_back(time);

    FQExpr key(ctx, body);
    TRACE << "Evaluating " << key << endl;

    f_elapsed = clock();

    /* Invoke walker on the body of the expr to be processed */
    (*this)(body);

    // sanity conditions
    assert(1 == f_expr_stack.size());
    assert(1 == f_ctx_stack.size());
    assert(1 == f_time_stack.size());

    // Exactly one expression
    ADD res = f_expr_stack.back();

    f_elapsed = clock() - f_elapsed;
    double secs = (double) f_elapsed / (double) CLOCKS_PER_SEC;
    TRACE << "Done. Took " << secs << " seconds" << endl;

    return res;
}

/*  Evaluation engine is implemented using a simple expression walker
 *  pattern: (a) on preorder, return true if the node has not yet been
 *  visited; (b) always do in-order (for binary nodes); (c) perform
 *  proper compilation in post-order hooks. */

bool Evaluator::walk_next_preorder(const Expr_ptr expr)
{
    step_t curr_time = f_time_stack.back();
    f_time_stack.push_back(1 + curr_time);
    return true;
}
void Evaluator::walk_next_postorder(const Expr_ptr expr)
{
    assert (0 < f_time_stack.size());
    f_time_stack.pop_back(); // reset time stack
}

bool Evaluator::walk_neg_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Evaluator::walk_neg_postorder(const Expr_ptr expr)
{
    if (is_unary_integer(expr)) {
        integer_neg(expr);
    }
    else if (is_unary_algebraic(expr)) {
        algebraic_neg(expr);
    }
    else assert( false ); // unreachable
}

bool Evaluator::walk_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Evaluator::walk_not_postorder(const Expr_ptr expr)
{
    POP_VALUE(lhs);

    value_t res = ! lhs;
    PUSH_VALUE(res);
}

bool Evaluator::walk_add_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_add_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_add_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = lhs + rhs;
    PUSH_VALUE(res);
}

bool Evaluator::walk_sub_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_sub_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_sub_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = lhs - rhs;
    PUSH_VALUE(res);
}

bool Evaluator::walk_div_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_div_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_div_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = lhs / rhs;
    PUSH_VALUE(res);
}

bool Evaluator::walk_mul_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_mul_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_mul_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = lhs / rhs;
    PUSH_VALUE(res);
}

bool Evaluator::walk_mod_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_mod_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_mod_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = lhs % rhs;
    PUSH_VALUE(res);
}

bool Evaluator::walk_and_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_and_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = lhs & rhs;
    PUSH_VALUE(res);
}

bool Evaluator::walk_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_or_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = lhs | rhs;
    PUSH_VALUE(res);
}

bool Evaluator::walk_xor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_xor_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_xor_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = lhs ^ rhs;
    PUSH_VALUE(res);
}

bool Evaluator::walk_xnor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_xnor_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_xnor_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = ( ! lhs | rhs ) & ( ! rhs | lhs );
    PUSH_VALUE(res);
}

bool Evaluator::walk_implies_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_implies_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = ( ! lhs | rhs );
    PUSH_VALUE(res);
}

bool Evaluator::walk_iff_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_iff_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_iff_postorder(const Expr_ptr expr)
{ /* just a fancy name for xnor :-) */ walk_xnor_postorder(expr); }

bool Evaluator::walk_lshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_lshift_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_lshift_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = ( lhs << rhs );
    PUSH_VALUE(res);
}

bool Evaluator::walk_rshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_rshift_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_rshift_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = ( lhs << rhs );
    PUSH_VALUE(res);
}

bool Evaluator::walk_eq_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_eq_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_eq_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = ( lhs == rhs );
    PUSH_VALUE(res);
}

bool Evaluator::walk_ne_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_ne_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_ne_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = ( lhs != rhs );
    PUSH_VALUE(res);
}

bool Evaluator::walk_gt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_gt_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_gt_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = ( lhs > rhs );
    PUSH_VALUE(res);
}

bool Evaluator::walk_ge_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_ge_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_ge_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = ( lhs >= rhs );
    PUSH_VALUE(res);
}

bool Evaluator::walk_lt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_lt_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_lt_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = ( lhs < rhs );
    PUSH_VALUE(res);
}

bool Evaluator::walk_le_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_le_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_le_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);

    value_t res = ( lhs <= rhs );
    PUSH_VALUE(res);
}

bool Evaluator::walk_ite_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_ite_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_ite_postorder(const Expr_ptr expr)
{
    POP_VALUE(rhs);
    POP_VALUE(lhs);
    POP_VALUE(cnd);

    value_t res = ( cnd ? lhs : rhs );
    PUSH_VALUE(res);
}

bool Evaluator::walk_cond_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_cond_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_cond_postorder(const Expr_ptr expr)
{ /* nop */ }

bool Evaluator::walk_dot_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_dot_inorder(const Expr_ptr expr)
{
    // ADD tmp = f_add_stack.back();
    // Expr_ptr ctx = tmp->get_repr();
    // f_ctx_stack.push_back(ctx);
    return true;
}
void Evaluator::walk_dot_postorder(const Expr_ptr expr)
{
    ADD rhs_add;

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

bool Evaluator::walk_params_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_params_inorder(const Expr_ptr expr)
{ return true; }
void Evaluator::walk_params_postorder(const Expr_ptr expr)
{ assert (false); /* not yet implemented */ }

bool Evaluator::walk_subscript_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Evaluator::walk_subscript_inorder(const Expr_ptr expr)
{ return true; }

bool Evaluator::walk_comma_preorder(const Expr_ptr expr)
{  return cache_miss(expr); }

bool Evaluator::walk_comma_inorder(const Expr_ptr expr)
{ return true; }

void Evaluator::walk_comma_postorder(const Expr_ptr expr)
{ assert (false); /* TODO support inlined non-determinism */ }

/* Array selector builder: for arrays subscription, a chain of ITE is
   built out of the encodings for each element which are assumed to be
   present in dd stack in reversed order (walk_leaf took care of
   this). */
void Evaluator::walk_subscript_postorder(const Expr_ptr expr)
{
    unsigned base = Cudd_V(f_enc.base().getNode());

    const Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();

    /* algebrize selection expr (rhs), using machine width */
    assert (rhs_type->is_algebraic());
    // algebrize_unary_subscript();
    assert(false); // tODO

    ADD selector[2]; // TODO
    for (unsigned i = 0; i < 2; ++ i) {
        selector[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    const Type_ptr lhs_type = f_type_stack.back(); f_type_stack.pop_back();
    unsigned size = lhs_type -> size();

    const Type_ptr scalar_type = lhs_type -> as_array() ->of();
    unsigned width = scalar_type->size();

    /* fetch DDs from the stack */
    ADD dds[width * size];
    for (unsigned i = 0; i < width * size; ++ i) {
        dds[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    ADD res; /* one digit at a time */
    for (unsigned i = 0; i < width; ++ i) {
        unsigned ndx = width - i - 1;
        res = f_enc.zero(); // TODO: FAILURE here

        for (unsigned j = 0; j < size; ++ j) {

            /* selected index */
            unsigned selection = size - j -1;

            ADD cond = f_enc.one();
            value_t value = ndx;

            /* encode the case selection as a conjunction of
               Equals ADD digit-by-digit (inlined) */
            for (unsigned k = 0; k < width; ++ k) {

                ADD digit = f_enc.constant(value % base);
                f_add_stack.push_back(digit);
                value /= base;

                /* case selection */
                cond *= selector[ndx].Equals(digit);
            }
            assert (value == 0); // not overflowing

            /* chaining */
            res = cond.Ite( dds[width * selection + i], res);
        }

        f_add_stack.push_back(res);
    }
}

/* private service of walk_leaf */
void Evaluator::push_variable(IEncoding_ptr enc, Type_ptr type)
{
    assert (NULL != enc);
    DDVector& dds = enc->dv();
    unsigned width = dds.size();

    // push into type stack
    f_type_stack.push_back(type);

    /* booleans, monoliths are just one DD */
    if (type->is_monolithical()) {
        f_add_stack.push_back(dds[0]);
    }

    /* algebraics, reversed list of encoding DDs */
    else if (type->is_algebraic()) {
        assert( type -> as_algebraic()-> size() == width ); // type and enc width info has to match
        for (DDVector::reverse_iterator ri = dds.rbegin();
             ri != dds.rend(); ++ ri) {
            f_add_stack.push_back(*ri);
        }
    }

    else if (type->is_array()) {
        abort(); // TODO
    }

    else assert( false ); // unexpected
}

void Evaluator::walk_leaf(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* cached? */
    if (! cache_miss(expr)) return;

    Expr_ptr ctx = f_ctx_stack.back();
    step_t time = f_time_stack.back();

    ENCMap::iterator eye;
    IEncoding_ptr enc = NULL;

    // 1.1. explicit constants are integer consts (e.g. 42) ..
    if (em.is_numeric(expr)) {
        f_expr_stack.push_back(expr);
        return;
    }

    // 2. Module-managed symbols
    ResolverProxy resolver;
    ISymbol_ptr symb = resolver.symbol(ctx, expr);;

    // 2. 1. Temporary symbols are maintained internally by the compiler
    ITemporary_ptr temp;
    if (NULL != (temp = dynamic_cast<ITemporary_ptr>(symb))) {
        Type_ptr type = NULL;

        type = symb->as_variable().type();
        assert(type->is_algebraic());

        // temporary encodings must be already defined.
        FQExpr key(ExprMgr::INSTANCE().make_main(), expr, time);

        ENCMap::iterator eye = f_temp_encodings.find(key);
        if (eye != f_temp_encodings.end()) {
            enc = (*eye).second;
        }
        else assert(false); // unexpected

        push_variable(enc, type);
        return;
    } /* Temporary symbols */

    // 2. 2. 1. bool/integer constant leaves
    if (symb->is_const()) {
        IConstant& konst =  symb->as_const();

        f_type_stack.push_back(konst.type());
        f_add_stack.push_back(f_enc.constant(konst.value()));
        return;
    }

    // 2. 2. 2. variables
    else if (symb->is_variable()) {

        // push into type stack
        Type_ptr type = symb->as_variable().type();

        // if encoding for variable is available reuse it,
        // otherwise create and cache it.
        FQExpr key(ctx, expr, time);

        /* build a new encoding for this symbol if none is available. */
        if (NULL == (enc = f_enc.find_encoding(key))) {
            assert (NULL != type);
            enc = f_enc.make_encoding(type);
            f_enc.register_encoding(key, enc);
        }

        push_variable(enc, type);
        return;
    } /* variables */

    // 2. 3. define? Simply evaluate it recursively.
    else if (symb->is_define()) {
        (*this)(symb->as_define().body());
        return;
    }

    // 3. TypeMgr symbols
    { /* try enums */
        IEnum_ptr enm;
        if (NULL != (enm = dynamic_cast<IEnum_ptr>(symb))) {
            f_ctx_stack.push_back(enm->expr());
            return;
        }
    }

    { /* try arrays */
        IArray_ptr arr;
        if (NULL != (arr = dynamic_cast<IArray_ptr>(symb))) {
            f_ctx_stack.push_back(arr->expr());
            return;
        }
    }

    assert( false ); /* give up, TODO: exception */
}
