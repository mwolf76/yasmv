/**
 *  @file inferrer.cc
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
 *  This module contains definitions and services that implement a
 *  type inference engine. The type inference engine is implemented
 *  using a simple walker pattern: (a) on preorder, return true if the
 *  node has not yet been visited; (b) always do in-order (for binary
 *  nodes); (c) perform proper type checking in post-order
 *  hooks. Implicit conversion rules are designed to follow as closely
 *  as possible section 6.3.1 of iso/iec 9899:1999 (aka C99)
 *  standard. Type rules are implemented in the result_type methods of
 *  the TypeMgr class.
 *
 **/

#include <common.hh>

#include <expr.hh>
#include <type.hh>
#include <proxy.hh>

#include <inferrer.hh>
#include <model_mgr.hh>

// uncommment following line to enable post_node_hook debug (verbose!)
// #define DEBUG_INFERRER

Inferrer::Inferrer(ModelMgr& owner)
    : f_map()
    , f_type_stack()
    , f_ctx_stack()
    , f_owner(owner)
{ /* DEBUG << "Created Inferrer @" << this << endl; */ }

Inferrer::~Inferrer()
{ /* DEBUG << "Destroying Inferrer @" << this << endl; */ }

/* this function is not memoized by design, for a memoized wrapper use type() */
Type_ptr Inferrer::process(Expr_ptr expr, Expr_ptr ctx)
{
    // remove previous results
    f_type_stack.clear();
    f_ctx_stack.clear();

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);

    // invoke walker on the body of the expr to be processed
    (*this)(expr);

    assert(1 == f_type_stack.size());

    POP_TYPE(res);
    assert(NULL != res);

    return res;
}

void Inferrer::pre_hook()
{}
void Inferrer::post_hook()
{}

void Inferrer::pre_node_hook(Expr_ptr expr)
{}

void Inferrer::post_node_hook(Expr_ptr expr)
{
    memoize_result(expr);

#ifdef DEBUG_INFERRER
    activation_record curr = f_recursion_stack.top();
    DEBUG << "inferrer post-node hook, expr = " << curr.expr << endl;

    DEBUG << "Type Stack" << endl;
    for (TypeStack::reverse_iterator i = f_type_stack.rbegin();
         i != f_type_stack.rend(); ++ i) {
        DEBUG << *i << endl;
    }
    DEBUG << "--------------------" << endl;
#endif
}

Type_ptr Inferrer::check_logical()
{
    POP_TYPE(res);
    assert (NULL != res);

    if (res -> is_boolean()) {
        return res;
    }

    throw BadType(res);
    return NULL; /* unreachable */
}

Type_ptr Inferrer::check_arithmetical()
{
    POP_TYPE(res);
    assert (NULL != res);

    if (res -> is_algebraic()) {
        return res;
    }

    throw BadType(res);
    return NULL; /* unreachable */
}

Type_ptr Inferrer::check_enum()
{
    POP_TYPE(res);
    assert (NULL != res);

    if (res -> is_enum()) {
        return res;
    }

    throw BadType(res);
    return NULL; /* unreachable */
}

Type_ptr Inferrer::check_scalar()
{
    POP_TYPE(res);
    assert (NULL != res);

    if (res -> is_scalar()) {
        return res;
    }

    throw BadType(res);
    return NULL; /* unreachable */
}

Type_ptr Inferrer::check_array()
{
    POP_TYPE(res);
    assert (NULL != res);

    if (res -> is_array()) {
        return res;
    }

    throw BadType(res);
    return NULL; /* unreachable */
}

bool Inferrer::walk_F_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_F_postorder(const Expr_ptr expr)
{ walk_unary_ltl_postorder(expr); }

bool Inferrer::walk_G_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_G_postorder(const Expr_ptr expr)
{ walk_unary_ltl_postorder(expr); }

bool Inferrer::walk_X_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_X_postorder(const Expr_ptr expr)
{ walk_unary_ltl_postorder(expr); }

bool Inferrer::walk_U_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_U_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_U_postorder(const Expr_ptr expr)
{ walk_binary_ltl_postorder(expr); }

bool Inferrer::walk_R_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_R_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_R_postorder(const Expr_ptr expr)
{ walk_binary_ltl_postorder(expr); }

bool Inferrer::walk_next_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_next_postorder(const Expr_ptr expr)
{ walk_unary_fsm_postorder(expr); }

bool Inferrer::walk_neg_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_neg_postorder(const Expr_ptr expr)
{ walk_unary_arithmetical_postorder(expr); }

bool Inferrer::walk_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_not_postorder(const Expr_ptr expr)
{ walk_unary_logical_postorder(expr); }

bool Inferrer::walk_bw_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_bw_not_postorder(const Expr_ptr expr)
{ walk_unary_logical_postorder(expr); }

bool Inferrer::walk_add_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_add_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_add_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool Inferrer::walk_sub_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_sub_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_sub_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool Inferrer::walk_div_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_div_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_div_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool Inferrer::walk_mul_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_mul_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_mul_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool Inferrer::walk_mod_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_mod_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_mod_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool Inferrer::walk_and_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_and_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool Inferrer::walk_bw_and_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_bw_and_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_bw_and_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }


bool Inferrer::walk_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_or_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool Inferrer::walk_bw_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_bw_or_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_bw_or_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool Inferrer::walk_bw_xor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_bw_xor_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_bw_xor_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool Inferrer::walk_bw_xnor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_bw_xnor_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_bw_xnor_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool Inferrer::walk_implies_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_implies_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool Inferrer::walk_iff_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_iff_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_iff_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool Inferrer::walk_cast_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_cast_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_cast_postorder(const Expr_ptr expr)
{ walk_binary_cast_postorder(expr); }

bool Inferrer::walk_type_preorder(const Expr_ptr expr)
{
    Type_ptr tp = f_owner.tm().find_type_by_def(expr);
    f_type_stack.push_back( tp);
    return false;
}
bool Inferrer::walk_type_inorder(const Expr_ptr expr)
{
    assert( false ); /* unreachable */
    return false;
}
void Inferrer::walk_type_postorder(const Expr_ptr expr)
{
    assert( false ); /* unreachable */
}

bool Inferrer::walk_lshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_lshift_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_lshift_postorder(const Expr_ptr expr)
{ walk_binary_shift_postorder(expr); }

bool Inferrer::walk_rshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_rshift_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_rshift_postorder(const Expr_ptr expr)
{ walk_binary_shift_postorder(expr); }

bool Inferrer::walk_eq_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_eq_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_eq_postorder(const Expr_ptr expr)
{ walk_binary_boolean_or_relational_postorder(expr); }

bool Inferrer::walk_ne_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_ne_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_ne_postorder(const Expr_ptr expr)
{ walk_binary_boolean_or_relational_postorder(expr); }

bool Inferrer::walk_gt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_gt_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_gt_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool Inferrer::walk_ge_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_ge_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_ge_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool Inferrer::walk_lt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_lt_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_lt_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool Inferrer::walk_le_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_le_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_le_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool Inferrer::walk_ite_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_ite_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_ite_postorder(const Expr_ptr expr)
{ walk_ternary_ite_postorder(expr); }

bool Inferrer::walk_cond_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_cond_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_cond_postorder(const Expr_ptr expr)
{ walk_ternary_cond_postorder(expr); }

bool Inferrer::walk_dot_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_dot_inorder(const Expr_ptr expr)
{
    assert( false ); // TODO
    // Type_ptr tmp = f_type_stack.back(); // TODO: review this
    // Expr_ptr ctx = f_owner.em().make_dot( f_ctx_stack.back(), expr->lhs());
    // f_ctx_stack.push_back(ctx);

    return true;
}
void Inferrer::walk_dot_postorder(const Expr_ptr expr)
{
    Type_ptr type = f_type_stack.back(); f_type_stack.pop_back();
    EnumType_ptr enm;

    if (NULL != (enm = dynamic_cast<EnumType_ptr> (type))) {
        const ExprSet& lits = enm->literals();
        Expr_ptr rhs = expr->rhs();

        if (lits.find(rhs) != lits.end()) {
            ResolverProxy proxy;
            ISymbol_ptr symb = proxy.symbol(f_ctx_stack.back(), rhs);

            PUSH_TYPE(symb->as_literal().type());
        }
    }

    else assert(false);


    // restore previous ctx
    f_ctx_stack.pop_back();
}

/* on-demand preprocessing to expand defines delegated to Preprocessor */
bool Inferrer::walk_params_preorder(const Expr_ptr expr)
{
    Expr_ptr ctx = f_ctx_stack.back();
    (*this)( f_owner.preprocess( expr, ctx));

    return false;
}
bool Inferrer::walk_params_inorder(const Expr_ptr expr)
{ assert( false ); return false; /* unreachable */ }
void Inferrer::walk_params_postorder(const Expr_ptr expr)
{ assert( false ); return ; /* unreachable */ }

bool Inferrer::walk_subscript_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_subscript_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_subscript_postorder(const Expr_ptr expr)
{
    POP_TYPE(index);
    if (! index -> is_algebraic() &&
        ! index -> is_constant()) {
        throw BadType(index);
    }

    /* return wrapped type */
    PUSH_TYPE(check_array() -> as_array() -> of());
}

bool Inferrer::walk_set_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_set_postorder(const Expr_ptr expr)
{
    assert(false); // TODO
}

bool Inferrer::walk_comma_preorder(Expr_ptr expr)
{ return cache_miss(expr); }

bool Inferrer::walk_comma_inorder(Expr_ptr expr)
{ return true; }

void Inferrer::walk_comma_postorder(Expr_ptr expr)
{
    POP_TYPE(rhs);
    POP_TYPE(lhs);
    if (lhs != rhs) {
        throw TypeMismatch(lhs, rhs);
    }

    PUSH_TYPE(lhs);
}

void Inferrer::walk_leaf(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();
    ExprMgr& em = f_owner.em();

    // cache miss took care of the stack already
    if (! cache_miss(expr)) return;

    // is an integer const ..
    if (em.is_numeric(expr)) {
        PUSH_TYPE(tm.find_constant());
        return;
    }

    // .. or a symbol
    if (em.is_identifier(expr)) {
        Expr_ptr ctx = f_ctx_stack.back();

        ResolverProxy proxy;
        ISymbol_ptr symb = proxy.symbol(ctx, expr);

        if (symb->is_const()) {
            Type_ptr res = symb->as_const().type();
            PUSH_TYPE(res);
            return;
        }
        else if (symb->is_literal()) {
            Type_ptr res = symb->as_literal().type();
            PUSH_TYPE(res);
            return;
        }
        else if (symb->is_enum()) { // meta type
            Type_ptr res = symb->as_enum().type();
            PUSH_TYPE(res);
            return;
        }
        // else if (symb->is_array()) { // meta type
        //     Type_ptr res = symb->as_array().type();
        //     PUSH_TYPE(res);
        //     return;
        // }
        else if (symb->is_variable()) {
            Type_ptr res = symb->as_variable().type();
            PUSH_TYPE(res);
            return;
        }
        // we keep this to retain the old lazy behavior with nullary defines
        // since it comes at no extra cost at all.
        else if (symb->is_define()) {
            IDefine& define = symb->as_define();
            assert( 0 == define.formals().size());
            (*this)(define.body());
            return;
        }
    }

    assert(false); // unexpected
}

// fun: T -> T
void Inferrer::walk_unary_fsm_postorder(const Expr_ptr expr)
{ /* no checks */ }

void Inferrer::walk_unary_ltl_postorder(const Expr_ptr expr)
{ /* no checks */ }

// fun: arithm -> arithm
void Inferrer::walk_unary_arithmetical_postorder(const Expr_ptr expr)
{
    PUSH_TYPE( check_arithmetical() );
}

// fun: logical -> logical
void Inferrer::walk_unary_logical_postorder(const Expr_ptr expr)
{
    PUSH_TYPE( check_logical() );
}

// fun: arithm, arithm -> arithm
void Inferrer::walk_binary_arithmetical_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();
    PUSH_TYPE( tm.result_type( expr,
                               check_arithmetical(),
                               check_arithmetical()));
}

// fun: logical x logical -> logical
void Inferrer::walk_binary_fsm_postorder(const Expr_ptr expr)
{
    check_logical();
    PUSH_TYPE( check_logical() );
}

void Inferrer::walk_binary_ltl_postorder(const Expr_ptr expr)
{
    check_logical();
    PUSH_TYPE( check_logical() );
}

// fun: logical x logical -> logical
void Inferrer::walk_binary_logical_postorder(const Expr_ptr expr)
{
    check_logical();
    PUSH_TYPE( check_logical() );
}

void Inferrer::walk_binary_cast_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();
    PUSH_TYPE( tm.result_type( expr,
                               check_arithmetical(),
                               check_arithmetical()));
}

/* specialized for shift ops (use rhs) */
void Inferrer::walk_binary_shift_postorder(const Expr_ptr expr)
{
    Type_ptr rhs = check_arithmetical();
    check_arithmetical(); // discard lhs
    PUSH_TYPE( rhs );
}

// fun: arithmetical x arithmetical -> boolean
void Inferrer::walk_binary_relational_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();
    PUSH_TYPE( tm.result_type( expr,
                               check_arithmetical(),
                               check_arithmetical()));
}

// fun: A/B/E x A/B/E -> B
void Inferrer::walk_binary_boolean_or_relational_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();
    Type_ptr rhs = check_scalar();
    Type_ptr lhs = check_scalar();

    /* constants can be promoted */
    if (lhs != rhs  && ! lhs -> is_constant() && ! rhs -> is_constant()) {
        throw TypeMismatch( lhs, rhs);
    }

    PUSH_TYPE( tm.result_type( expr, lhs, rhs));
}


// fun:  boolean x T -> T
void Inferrer::walk_ternary_cond_postorder(const Expr_ptr expr)
{
    Type_ptr rhs = f_type_stack.back(); f_type_stack.pop_back();
    check_logical(); // condition

    PUSH_TYPE( rhs );
}

// fun: (boolean ? T) x T -> T
void Inferrer::walk_ternary_ite_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();
    POP_TYPE(rhs);
    POP_TYPE(lhs);
    PUSH_TYPE( tm.result_type( expr, tm.find_boolean(), lhs, rhs));
}

void Inferrer::memoize_result (Expr_ptr expr)
{
    Type_ptr type = f_type_stack.back();
    f_map[ FQExpr(f_ctx_stack.back(),
                  find_canonical_expr(expr)) ] = type;
}

/* This is used to attempt for a better memoization, but it's not
   really critical */
Expr_ptr Inferrer::find_canonical_expr(Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();

    /* time is not relevant here */
    while (em.is_next(expr)) {
        expr = expr->lhs();
    }

    if (em.is_unary_ltl(expr)) {
        return em.make_F(expr->lhs());
    }
    else if (em.is_binary_relational(expr)) {
        return em.make_lt(expr->lhs(), expr->rhs());
    }
    else if (em.is_binary_arithmetical(expr)) {
        return em.make_add(expr->lhs(), expr->rhs());
    }
    else if (em.is_binary_logical(expr)) {
        return em.make_and(expr->lhs(), expr->rhs());
    }
    else if (em.is_subscript(expr)) {
        return em.make_subscript(expr->lhs(),
                                 find_canonical_expr( expr->rhs()));
    }
    else if (em.is_params(expr)) {
        return em.make_subscript(expr->lhs(),
                                 find_canonical_expr( expr->rhs()));
    }
    else if (em.is_binary_ltl(expr)) {
        return em.make_U(find_canonical_expr( expr->lhs()),
                         find_canonical_expr( expr->rhs()));
    }
    else if (em.is_comma(expr)) {
        return em.make_comma(find_canonical_expr( expr->lhs()),
                             find_canonical_expr( expr->rhs()));
    }
    else if (em.is_cast(expr)) {
        return em.make_cast( find_canonical_expr( expr->lhs()),
                             find_canonical_expr( expr->rhs()));
    }
    else if (em.is_type(expr)) {
        return em.make_type( find_canonical_expr( expr->lhs()),
                             find_canonical_expr( expr->rhs()));
    }

    /* no rewrites */
    else if (em.is_dot(expr) ||
             em.is_unary_arithmetical(expr) ||
             em.is_unary_logical(expr) ||
             em.is_ite(expr) ||
             em.is_cond(expr) ||
             em.is_identifier(expr) ||
             em.is_numeric(expr)) {
        return expr;
    }

    DEBUG << expr << endl;
    assert ( false ); // unreachable
}

Type_ptr Inferrer::type(Expr_ptr expr, Expr_ptr ctx)
{
    /* to avoid a number of cache misses due to compiler rewrites,
       we squeeze types in equivalence classes: Relationals -> lhs
       '<' rhs, Arithmetical -> lhs '+' rhs */
    FQExpr key( ctx, find_canonical_expr( expr));

    TypeReg::const_iterator eye = f_map.find(key);
    Type_ptr res = NULL;

    // cache miss, fallback to walker
    if (eye == f_map.end()) {
        res = process( expr, ctx);
    }
    else {
        res = (*eye).second;
    }

    assert(NULL != res);
    return res;
}
