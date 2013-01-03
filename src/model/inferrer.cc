/**
 *  @file inferrer.cc
 *  @brief Expr type inferrer
 *
 *  This module contains definitions and services that implement a
 *  type inference engine. The type inference engine is implemented
 *  using a simple walker pattern: (a) on preorder, return true if the
 *  node has not yet been visited; (b) always do in-order (for binary
 *  nodes); (c) perform proper type checking in post-order hooks.
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
#include <inferrer.hh>

#include <model_mgr.hh>

#include <type_exceptions.hh>

Inferrer::Inferrer(ModelMgr& owner)
    : f_map()
    , f_type_stack()
    , f_ctx_stack()
    , f_owner(owner)
{
    ExprMgr& em = f_owner.em();

    /* build predefined type sets, used in error reporting */
    f_integer_or_boolean.push_back(em.make_integer_type());
    f_integer_or_boolean.push_back(em.make_boolean_type());

    f_boolean = em.make_boolean_type();
    f_integer = em.make_integer_type();

    DEBUG << "Created Inferrer @" << this << endl;
}

Inferrer::~Inferrer()
{ DEBUG << "Destroying Inferrer @" << this << endl; }

/* this function is not memoized by design, for a memoized wrapper use type() */
Type_ptr Inferrer::process(Expr_ptr ctx, Expr_ptr body)
{
    Type_ptr res = NULL;

    // remove previous results
    f_type_stack.clear();
    f_ctx_stack.clear();

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);

    // invoke walker on the body of the expr to be processed
    // DRIVEL << "Determining type for expression " << ctx << "::" << body << endl;
    (*this)(body);

    assert(1 == f_type_stack.size());
    res = f_type_stack.back();

    // DRIVEL << "Type for " << ctx << "::" << body
    //        << " is " << res << endl;

    return res;
}

void Inferrer::pre_hook()
{}
void Inferrer::post_hook()
{}

void Inferrer::debug_hook()
{
#if 0
    activation_record curr = f_recursion_stack.top();
    DEBUG << "inferrer debug hook, expr = " << curr.expr << endl;

    DEBUG << "Type Stack" << endl;
    for (TypeStack::reverse_iterator i = f_type_stack.rbegin();
         i != f_type_stack.rend(); ++ i) {
        DEBUG << *i << endl;
    }
    DEBUG << "--------------------" << endl;
#endif
}

bool Inferrer::walk_F_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_F_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Inferrer::walk_G_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_G_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Inferrer::walk_X_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_X_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Inferrer::walk_U_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_U_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_U_postorder(const Expr_ptr expr)
{ walk_binary_temporal_postorder(expr); }

bool Inferrer::walk_R_preorder(const Expr_ptr expr)
{ return cache_miss(expr);  }
bool Inferrer::walk_R_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_R_postorder(const Expr_ptr expr)
{ walk_binary_temporal_postorder(expr); }

bool Inferrer::walk_AF_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_AF_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Inferrer::walk_AG_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_AG_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Inferrer::walk_AX_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_AX_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Inferrer::walk_AU_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_AU_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_AU_postorder(const Expr_ptr expr)
{ walk_binary_temporal_postorder(expr); }

bool Inferrer::walk_AR_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_AR_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_AR_postorder(const Expr_ptr expr)
{ walk_binary_temporal_postorder(expr); }

bool Inferrer::walk_EF_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_EF_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Inferrer::walk_EG_preorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_EG_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Inferrer::walk_EX_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_EX_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Inferrer::walk_EU_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_EU_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_EU_postorder(const Expr_ptr expr)
{ walk_binary_temporal_postorder(expr); }

bool Inferrer::walk_ER_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_ER_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_ER_postorder(const Expr_ptr expr)
{ walk_binary_temporal_postorder(expr); }

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
{ walk_binary_logical_or_bitwise_postorder(expr); }

bool Inferrer::walk_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_or_postorder(const Expr_ptr expr)
{ walk_binary_logical_or_bitwise_postorder(expr); }

bool Inferrer::walk_xor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_xor_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_xor_postorder(const Expr_ptr expr)
{ walk_binary_logical_or_bitwise_postorder(expr); }

bool Inferrer::walk_xnor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_xnor_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_xnor_postorder(const Expr_ptr expr)
{ walk_binary_logical_or_bitwise_postorder(expr); }

bool Inferrer::walk_implies_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_implies_postorder(const Expr_ptr expr)
{ walk_binary_logical_or_bitwise_postorder(expr); }

bool Inferrer::walk_iff_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_iff_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_iff_postorder(const Expr_ptr expr)
{ walk_binary_logical_or_bitwise_postorder(expr); }

bool Inferrer::walk_lshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_lshift_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_lshift_postorder(const Expr_ptr expr)
{ walk_binary_bitwise_postorder(expr); }

bool Inferrer::walk_rshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_rshift_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_rshift_postorder(const Expr_ptr expr)
{ walk_binary_bitwise_postorder(expr); }

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
    Type_ptr tmp = f_type_stack.back();
    Expr_ptr ctx = tmp->repr();

    f_ctx_stack.push_back(ctx);
    return true;
}
void Inferrer::walk_dot_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();
    Type_ptr rhs_type;

    { // RHS, no checks necessary/possible
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        rhs_type = top;
    }

    { // LHS, must be an instance (by assertion, otherwise leaf would have fail)
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        assert(tm.is_instance(top));
    }

    // propagate rhs type
    f_type_stack.push_back(rhs_type);

    // restore previous ctx
    f_ctx_stack.pop_back();
}

bool Inferrer::walk_params_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_params_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_params_postorder(const Expr_ptr expr)
{ assert( false ); /* not yet implemented */ }

bool Inferrer::walk_subscript_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_subscript_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_subscript_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    Type_ptr rhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!tm.is_integer(rhs) &&
        !tm.is_algebraic(rhs))
            throw BadType(rhs->repr(), f_integer, expr);

    Type_ptr lhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!tm.is_array(lhs))
            throw BadType(lhs->repr(), "array", expr);

    /* return wrapped type */
    f_type_stack.push_back(tm.as_array(lhs)->of());
}

void Inferrer::walk_leaf(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();
    ExprMgr& em = f_owner.em();

    // cache miss took care of the stack already
    if (! cache_miss(expr)) return;

    // a numeric constant is an integer
    if (em.is_numeric(expr)) {
        Type_ptr res = tm.find_integer();
        f_type_stack.push_back(res);
    }

    else if (em.is_identifier(expr)) {
        ISymbol_ptr symb = resolve(f_ctx_stack.back(), expr);
        assert(symb);

        // 1. bool/integer constant leaves
        if (symb->is_const()) {
            Type_ptr res = symb->as_const().type();
            f_type_stack.push_back(res);
        }

        // 2. variable
        else if (symb->is_variable()) {
            Type_ptr res = symb->as_variable().type();
            f_type_stack.push_back(res);
        }

        // 3. define? needs to be compiled (re-entrant invocation)
        else if (symb->is_define()) {
            (*this)(symb->as_define().body());
        }
    }

    else {
        assert(0);
    }
}

// one step of resolution returns a const or variable
ISymbol_ptr Inferrer::resolve(const Expr_ptr ctx, const Expr_ptr frag)
{
    ISymbol_ptr symb = f_owner.resolver()->fetch_symbol(ctx, frag);

    // is this a constant or variable?
    if (symb->is_const() ||
        symb->is_temporary() ||
        symb->is_variable()) {
        return symb;
    }

    // ... or a define?
    else if (symb->is_define()) {
        while (symb->is_define()) {
            Expr_ptr body = symb->as_define().body();
            symb = f_owner.resolver()->fetch_symbol(ctx, body);
        }
        return symb;
    }

    // or what?!?
    else assert(0);
}

// fun: temporal -> temporal
void Inferrer::walk_unary_temporal_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();

    if (!tm.is_boolean(top)) {
        throw BadType(top->repr(), f_boolean, expr);
    }

    // f_type_stack.push_back(tm.find_boolean());
    memoize_canonical_result( expr, tm.find_boolean());
}

// fun: temporal x temporal -> temporal
void Inferrer::walk_binary_temporal_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    { // RHS
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!tm.is_boolean(top))
            throw BadType(top->repr(), f_boolean, expr);
    }

    { // LHS
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!tm.is_boolean(top))
            throw BadType(top->repr(), f_boolean, expr);
    }

    // f_type_stack.push_back(tm.find_boolean());
    memoize_canonical_result( expr, tm.find_boolean());
}

// fun: T -> T
void Inferrer::walk_unary_fsm_postorder(const Expr_ptr expr)
{ /* no checks */ }

// fun: arithm -> arithm
void Inferrer::walk_unary_arithmetical_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
    if (!tm.is_integer(top) &&
        !tm.is_algebraic(top)) {
        throw BadType(top->repr(), f_integer, expr);
    }

    if (tm.is_integer(top)) {
        // f_type_stack.push_back(tm.find_integer());
        memoize_canonical_result( expr, tm.find_integer());
        return;
    }

    if (tm.is_algebraic(top)) {
        memoize_canonical_result( expr, top);
        return;
    }

    assert( false ); // unreachable
}

// fun: logical -> logical
void Inferrer::walk_unary_logical_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
    if (!tm.is_boolean(top)) {
        throw BadType(top->repr(), f_boolean, expr);
    }

    memoize_canonical_result( expr, tm.find_boolean());
}

// fun: arithm, arithm -> arithm
void Inferrer::walk_binary_arithmetical_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    const Type_ptr rhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!tm.is_integer(rhs) && !tm.is_algebraic(rhs)) {
        throw BadType(rhs->repr(), f_integer, expr);
    }

    const Type_ptr lhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!tm.is_integer(lhs) && !tm.is_algebraic(lhs)) {
        throw BadType(lhs->repr(), f_integer, expr);
    }

    // both ops integers -> integer
    if (tm.is_integer(lhs) && (tm.is_integer(rhs))) {
        memoize_canonical_result(expr, tm.find_integer());
        return;
    }

        // one op algebraic, possibly both.
    unsigned rhs_width = tm.is_algebraic(rhs)
        ? tm.as_algebraic(rhs)->width()
        : 0;
    bool rhs_is_signed = tm.is_algebraic(rhs)
        ? tm.as_algebraic(rhs)->is_signed()
        : false;

    unsigned lhs_width = tm.is_algebraic(lhs)
        ? tm.as_algebraic(lhs)->width()
        : 0;
    bool lhs_is_signed = tm.is_algebraic(lhs)
        ? tm.as_algebraic(lhs)->is_signed()
        : false;

    /* max */
    unsigned width = rhs_width < lhs_width
        ? lhs_width
        : rhs_width
        ;
    bool is_signed = rhs_is_signed || lhs_is_signed;

    // if both are algebraic they have to agree on signedness too.
    if ((0 < rhs_width) && (0 < lhs_width)) {
        assert ( tm.as_algebraic(rhs)->is_signed() ==
                 tm.as_algebraic(lhs)->is_signed() );
    }

    memoize_canonical_result( expr, (is_signed
                                     ? tm.find_signed(width)
                                     : tm.find_unsigned(width)));
}

// fun: logical x logical -> logical
void Inferrer::walk_binary_logical_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    const Type_ptr rhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!tm.is_boolean(rhs)) {
        throw BadType(rhs->repr(), f_boolean, expr);
    }

    const Type_ptr lhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!tm.is_boolean(lhs)) {
        throw BadType(lhs->repr(), f_boolean, expr);
    }

    // boolean
    assert(tm.is_boolean(lhs) && tm.is_boolean(rhs));

    memoize_canonical_result(expr, tm.find_boolean());
}

void Inferrer::walk_binary_logical_or_bitwise_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    const Type_ptr rhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!tm.is_boolean(rhs) &&
        !tm.is_integer(rhs) &&
        !tm.is_algebraic(rhs)) {
        throw BadType(rhs->repr(), f_integer_or_boolean, expr);
    }

    const Type_ptr lhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!tm.is_boolean(lhs) &&
        !tm.is_integer(lhs) &&
        !tm.is_integer(rhs)) {
        throw BadType(lhs->repr(), f_integer_or_boolean, expr);
    }

    // both ops boolean -> boolean
    if (tm.is_boolean(lhs) && tm.is_boolean(rhs)) {
        memoize_canonical_result( expr, tm.find_boolean());
        return;
    }

    // both ops integers -> integer
    if (tm.is_integer(lhs) && (tm.is_integer(rhs))) {
        memoize_canonical_result( expr, tm.find_integer());
        return;
    }

        // one op algebraic, possibly both.
    unsigned rhs_width = tm.is_algebraic(rhs)
        ? tm.as_algebraic(rhs)->width()
        : 0;
    bool rhs_is_signed = tm.is_algebraic(rhs)
        ? tm.as_algebraic(rhs)->is_signed()
        : false;

    unsigned lhs_width = tm.is_algebraic(lhs)
        ? tm.as_algebraic(lhs)->width()
        : 0;
    bool lhs_is_signed = tm.is_algebraic(lhs)
        ? tm.as_algebraic(lhs)->is_signed()
        : false;

    /* max */
    unsigned width = rhs_width < lhs_width
        ? lhs_width
        : rhs_width
        ;
    bool is_signed = rhs_is_signed || lhs_is_signed;

    // if both are algebraic they have to agree on signedness too.
    if ((0 < rhs_width) && (0 < lhs_width)) {
        assert ( tm.as_algebraic(rhs)->is_signed() ==
                 tm.as_algebraic(lhs)->is_signed() );
    }

    memoize_canonical_result(expr, (is_signed
                                    ? tm.find_signed(width)
                                    : tm.find_unsigned(width)));
}


// fun: (A/L) x (A/L) -> A/L
void Inferrer::walk_binary_bitwise_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    const Type_ptr rhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!tm.is_integer(rhs) &&
        !tm.is_algebraic(rhs) &&
        !tm.is_boolean(rhs)) {
        throw BadType(rhs->repr(), f_integer, expr);
    }

    const Type_ptr lhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!tm.is_integer(lhs) &&
        !tm.is_algebraic(lhs) &&
        !tm.is_boolean(lhs)) {
        throw BadType(lhs->repr(), f_integer, expr);
    }

    // both ops boolean -> boolean
    if (tm.is_boolean(lhs) && tm.is_boolean(rhs)) {
        memoize_canonical_result( expr, tm.find_boolean());
        return;
    }

    // both ops integers -> integer
    if (tm.is_integer(lhs) && (tm.is_integer(rhs))) {
        memoize_canonical_result( expr, tm.find_integer());
        return;
    }

    // one op algebraic, possibly both.
    unsigned rhs_width = tm.is_algebraic(rhs)
        ? tm.as_algebraic(rhs)->width()
        : 0;
    bool rhs_is_signed = tm.is_algebraic(rhs)
        ? tm.as_algebraic(rhs)->is_signed()
        : false;

    unsigned lhs_width = tm.is_algebraic(lhs)
        ? tm.as_algebraic(lhs)->width()
        : 0;
    bool lhs_is_signed = tm.is_algebraic(lhs)
        ? tm.as_algebraic(lhs)->is_signed()
        : false;

    /* max */
    unsigned width = rhs_width < lhs_width
        ? lhs_width
        : rhs_width
        ;
    bool is_signed = rhs_is_signed || lhs_is_signed;

    // if both are algebraic they have to agree on signedness too.
    if ((0 < rhs_width) && (0 < lhs_width)) {
        assert ( tm.as_algebraic(rhs)->is_signed() ==
                 tm.as_algebraic(lhs)->is_signed() );
    }

    memoize_canonical_result( expr, (is_signed
                                     ? tm.find_signed(width)
                                     : tm.find_unsigned(width)));
}

// fun: arithmetical x arithmetical -> boolean
void Inferrer::walk_binary_relational_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    const Type_ptr rhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!tm.is_integer(rhs) && !tm.is_algebraic(rhs)) {
        throw BadType(rhs->repr(), f_integer, expr);
    }

    const Type_ptr lhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!tm.is_integer(lhs) && !tm.is_algebraic(lhs)) {
        throw BadType(lhs->repr(), f_integer, expr);
    }

    memoize_canonical_result( expr, tm.find_boolean());
}

// fun: A/B x A/B -> B
void Inferrer::walk_binary_boolean_or_relational_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    const Type_ptr rhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!tm.is_boolean(rhs) &&
        !tm.is_algebraic(rhs) &&
        !tm.is_integer(rhs)) {
        throw BadType(rhs->repr(), f_integer_or_boolean, expr);
    }

    const Type_ptr lhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!tm.is_boolean(lhs) &&
        !tm.is_algebraic(lhs) &&
        !tm.is_integer(lhs)) {
        throw BadType(lhs->repr(), f_integer_or_boolean, expr);
    }

    // algebraic or integer
    if ((tm.is_integer(lhs) || tm.is_algebraic(lhs)) &&
        (tm.is_integer(rhs) || tm.is_algebraic(rhs))) {
        memoize_canonical_result( expr, tm.find_boolean());
        return;
    }

    // boolean
    if (tm.is_boolean(lhs) && tm.is_boolean(rhs)) {
        memoize_canonical_result( expr, tm.find_boolean());
        return;
    }

    throw BadType(rhs->repr(), lhs->repr(), expr);
}


// fun:  boolean x T -> T
void Inferrer::walk_ternary_cond_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    const Type_ptr rhs = f_type_stack.back(); f_type_stack.pop_back();
    const Type_ptr lhs = f_type_stack.back(); f_type_stack.pop_back();

    // condition is always boolean
    if (!tm.is_boolean(lhs)) {
        throw BadType(lhs->repr(), f_boolean, expr);
    }

    memoize_canonical_result(expr, rhs);
}

// fun: (boolean ? T) x T -> T
void Inferrer::walk_ternary_ite_postorder(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    const Type_ptr rhs = f_type_stack.back(); f_type_stack.pop_back();
    const Type_ptr lhs = f_type_stack.back(); f_type_stack.pop_back();

    unsigned width =0;
    bool is_signed;

    // boolean
    if (tm.is_boolean(lhs) && tm.is_boolean(rhs)) {
        memoize_canonical_result( expr, tm.find_boolean());
        return;
    }

    // ITEs are forced to be algebraic, even when both children are
    // integers. Actual type is first customarily inferred from
    // children. If no algebraic is found among children, searches
    // backwards in the type stack.
    unsigned rhs_width = tm.is_algebraic(rhs)
        ? tm.as_algebraic(rhs)->width()
        : 0;
    bool rhs_is_signed = tm.is_algebraic(rhs)
        ? tm.as_algebraic(rhs)->is_signed()
        : false;

    unsigned lhs_width = tm.is_algebraic(lhs)
        ? tm.as_algebraic(lhs)->width()
        : 0;
    bool lhs_is_signed = tm.is_algebraic(lhs)
        ? tm.as_algebraic(lhs)->is_signed()
        : false;

    /* max */
    width = rhs_width < lhs_width
        ? lhs_width
        : rhs_width
        ;

    if (0 != width) {
        is_signed = rhs_is_signed || lhs_is_signed;

        // if both are algebraic they have to agree on signedness too.
        if ((0 < rhs_width) && (0 < lhs_width)) {
            assert ( tm.as_algebraic(rhs)->is_signed() ==
                     tm.as_algebraic(lhs)->is_signed() );
        }
    }

    /* fallback case: inspect type stack backwards */
    else {
        /* map canonicity w.r.t. compiler rewrites should help here */
        assert (0 < f_type_stack.size());

        TypeStack::reverse_iterator ri = f_type_stack.rbegin();
        do {
            Type_ptr type = (*ri);
            if (tm.is_algebraic(type)) {

                width = tm.as_algebraic(type)->width();
                is_signed = tm.as_algebraic(type)->is_signed();

                break;
            }

            ++ ri;
        } while ( ri != f_type_stack.rend() );
    }

    assert (0 < width);
    memoize_canonical_result(expr, is_signed
                             ? tm.find_signed(width)
                             : tm.find_unsigned(width));
}

/* memoize (canonical) and return */
void Inferrer::memoize_canonical_result (Expr_ptr expr, Type_ptr type)
{
    f_type_stack.push_back(type);
    f_map[ FQExpr(f_ctx_stack.back(), find_canonical_expr(expr)) ] = type;
}

Expr_ptr Inferrer::find_canonical_expr(Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();

    /* time is not relevant here */
    while (em.is_next(expr)) {
        expr = expr->lhs();
    }

    if (em.is_binary_relational(expr)) {
        return em.make_lt(expr->lhs(), expr->rhs());
    }
    else if (em.is_binary_arithmetical(expr)) {
        return em.make_add(expr->lhs(), expr->rhs());
    }
    else if (em.is_binary_logical(expr)) {
        return em.make_and(expr->lhs(), expr->rhs());
    }

    /* no rewrites */
    else if (em.is_unary_arithmetical(expr) ||
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

Type_ptr Inferrer::type(FQExpr& fqexpr)
{
    /* to avoid a number of cache misses due to compiler rewrites,
       we squeeze types in equivalence classes: Relationals -> lhs
       '<' rhs, Algebraic -> lhs '+' rhs */
    FQExpr key( fqexpr.ctx(),
                find_canonical_expr( fqexpr.expr()));

    TypeReg::const_iterator eye = f_map.find(key);
    Type_ptr res = NULL;

    // cache miss, fallback to walker
    if (eye == f_map.end()) {
        res = process(fqexpr.ctx(), fqexpr.expr());
    }
    else {
        res = (*eye).second;
    }

    assert(NULL != res);
    return res;
}
