/**
 *  @file simple_inferrer.cc
 *  @brief Expr type simple_inferrer
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
#include <simple_inferrer.hh>

SimpleInferrer::SimpleInferrer()
    : f_map()
    , f_type_stack()
    , f_ctx_stack()
    , f_mm(ModelMgr::INSTANCE())
    , f_em(ExprMgr::INSTANCE())
    , f_tm(TypeMgr::INSTANCE())
{ TRACE << "Created SimpleInferrer @" << this << endl; }

SimpleInferrer::~SimpleInferrer()
{ TRACE << "Destroying SimpleInferrer @" << this << endl; }

Type_ptr SimpleInferrer::process(Expr_ptr ctx, Expr_ptr body)
{
    Type_ptr res = NULL;
    DEBUG << "Determining type for expression " << ctx << "::" << body << endl;

    // remove previous results
    f_type_stack.clear();
    f_ctx_stack.clear();

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);

    // invoke walker on the body of the expr to be processed
    (*this)(body);

    assert(1 == f_type_stack.size());
    res = f_type_stack.back();

    DEBUG  << res << endl;
    return res;
}

void SimpleInferrer::pre_hook()
{}
void SimpleInferrer::post_hook()
{}

bool SimpleInferrer::walk_next_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void SimpleInferrer::walk_next_postorder(const Expr_ptr expr)
{ walk_unary_fsm_postorder(expr); }

bool SimpleInferrer::walk_neg_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void SimpleInferrer::walk_neg_postorder(const Expr_ptr expr)
{ walk_unary_arithmetical_postorder(expr); }

bool SimpleInferrer::walk_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void SimpleInferrer::walk_not_postorder(const Expr_ptr expr)
{ walk_unary_logical_postorder(expr); }

bool SimpleInferrer::walk_add_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_add_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_add_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool SimpleInferrer::walk_sub_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_sub_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_sub_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool SimpleInferrer::walk_div_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_div_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_div_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool SimpleInferrer::walk_mul_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_mul_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_mul_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool SimpleInferrer::walk_mod_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_mod_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_mod_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool SimpleInferrer::walk_and_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_and_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool SimpleInferrer::walk_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_or_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool SimpleInferrer::walk_xor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_xor_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_xor_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool SimpleInferrer::walk_xnor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_xnor_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_xnor_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool SimpleInferrer::walk_implies_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_implies_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool SimpleInferrer::walk_iff_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_iff_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_iff_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool SimpleInferrer::walk_lshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_lshift_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_lshift_postorder(const Expr_ptr expr)
{ walk_binary_bitwise_postorder(expr); }

bool SimpleInferrer::walk_rshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_rshift_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_rshift_postorder(const Expr_ptr expr)
{ walk_binary_bitwise_postorder(expr); }

bool SimpleInferrer::walk_eq_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_eq_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_eq_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool SimpleInferrer::walk_ne_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_ne_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_ne_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool SimpleInferrer::walk_gt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_gt_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_gt_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool SimpleInferrer::walk_ge_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_ge_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_ge_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool SimpleInferrer::walk_lt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_lt_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_lt_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool SimpleInferrer::walk_le_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_le_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_le_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool SimpleInferrer::walk_ite_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_ite_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_ite_postorder(const Expr_ptr expr)
{ walk_ternary_ite_postorder(expr); }

bool SimpleInferrer::walk_cond_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_cond_inorder(const Expr_ptr expr)
{ return true; }
void SimpleInferrer::walk_cond_postorder(const Expr_ptr expr)
{}

bool SimpleInferrer::walk_dot_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool SimpleInferrer::walk_dot_inorder(const Expr_ptr expr)
{
    Type_ptr tmp = f_type_stack.back();
    Expr_ptr ctx = tmp->get_repr();
    f_ctx_stack.push_back(ctx);
    return true;
}
void SimpleInferrer::walk_dot_postorder(const Expr_ptr expr)
{
    Type_ptr rhs_type;

    { // RHS, no checks necessary/possible
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        rhs_type = top;
    }

    { // LHS, must be an instance (by assertion, otherwise leaf would have fail)
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        assert(f_tm.is_instance(top));
    }

    // propagate rhs type
    f_type_stack.push_back(rhs_type);

    // restore previous ctx
    f_ctx_stack.pop_back();
}

/* Integer types: in general if one has a binary op between two
   integer types phi(x) op psi(y) where x and y are the number of bits
   of the encoding the result type is rho(x + y) which should cover
   the most general case.  */
void SimpleInferrer::walk_leaf(const Expr_ptr expr)
{
    ExprType symb_type = expr->f_symb;
    Type_ptr tp;

    // cache miss took care of the stack already
    if (! cache_miss(expr)) return;

    // a constants is a 0-bits unsigned type
    if (symb_type == ICONST) {
        tp = f_tm.find_unsigned(0);
    }

    // TODO: kill this?
    // else if (symb_type == UWCONST) {
    //     tp = f_tm.find_uword(f_em.make_iconst(expr->u.f_size));
    // }

    // TODO: kill this too?
    // else if (symb_type == SWCONST) {
    //     tp = f_tm.find_sword(f_em.make_iconst(expr->u.f_size));
    // }

    else if (symb_type == IDENT) {
        ISymbol_ptr symb = resolve(f_ctx_stack.back(), expr);

        assert(symb);
        tp = symb->type(); // define types are already inferred
    }

    else assert(0);

    assert(tp);
    f_type_stack.push_back(tp);
}

// one step of resolution returns a const or variable
ISymbol_ptr SimpleInferrer::resolve(const Expr_ptr ctx, const Expr_ptr frag)
{
    Model& model = static_cast <Model&> (*f_mm.model());
    ISymbol_ptr symb = model.fetch_symbol(ctx, frag);

    // is this a constant or variable?
    if (symb->is_const() ||
        symb->is_variable()) {
        return symb;
    }

    // ... or a define?
    else if (symb->is_define()) {
        while (symb->is_define()) {
            Expr_ptr body = symb->as_define().body();
            symb = model.fetch_symbol(ctx, body);
        }
        return symb;
    }

    // or what?!?
    else assert(0);
}

// fun: boolean -> boolean
void SimpleInferrer::walk_unary_fsm_postorder(const Expr_ptr expr)
{
    const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();

    if (!f_tm.is_boolean(top) &&
        !f_tm.is_integer(top) &&
        !f_tm.is_word(top)) {

        throw BadType(top->get_repr(), f_em.make_boolean_type(), expr);
    }

    f_type_stack.push_back(top); // propagate
}

// fun: int x boolean -> boolean
void SimpleInferrer::walk_binary_fsm_postorder(const Expr_ptr expr)
{
    { // RHS
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!f_tm.is_boolean(top)) {
            throw BadType(top->get_repr(), f_em.make_boolean_type(), expr);
        }

        f_type_stack.push_back(top); // propagate
    }

    { // LHS
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!f_tm.is_integer(top)) {
            throw BadType(top->get_repr(), f_em.make_unsigned_type(0), expr); // must be a const
        }
    }
}

// fun: arithm -> arithm
void SimpleInferrer::walk_unary_arithmetical_postorder(const Expr_ptr expr)
{
    const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();

    if (!f_tm.is_integer(top) &&
        !f_tm.is_word(top)) {
        throw BadType(top->get_repr(), f_em.make_boolean_type(), expr);
    }

    f_type_stack.push_back(top); // propagate
}

// fun: logical -> logical
void SimpleInferrer::walk_unary_logical_postorder(const Expr_ptr expr)
{
    const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();

    if (!f_tm.is_boolean(top)) {
        throw BadType(top->get_repr(), f_em.make_boolean_type(), expr);
    }

    f_type_stack.push_back(top); // propagate
}

// fun: arithm(x) x arithm(y) -> arithm(x+y)
void SimpleInferrer::walk_binary_arithmetical_postorder(const Expr_ptr expr)
{
    Type_ptr exp_type;

    { // RHS
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!f_tm.is_integer(top)) {
            throw BadType(top->get_repr(), f_em.make_integer_type(), expr);
        }
        exp_type = top;
    }

    { // LHS
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!f_tm.is_integer(top)) {
            throw BadType(top->get_repr(), f_em.make_integer_type(), expr);
        }

        // type matching is mandatory here
        if (top != exp_type) {
            throw BadType(exp_type->get_repr(), top->get_repr(), expr);
        }
    }

    f_type_stack.push_back(f_tm.find_integer());
}


// fun: logical x logical -> logical
void SimpleInferrer::walk_binary_logical_postorder(const Expr_ptr expr)
{
    Type_ptr exp_type;

    { // RHS
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!f_tm.is_boolean(top) &&
            !f_tm.is_word(top)) {
            throw BadType(top->get_repr(), f_em.make_boolean_type(), expr);
        }
        exp_type = top;
    }

    { // LHS
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!f_tm.is_boolean(top) &&
            !f_tm.is_word(top)) {
            throw BadType(top->get_repr(), f_em.make_integer_type(), expr);
        }

        // type matching is mandatory here
        if (top != exp_type) {
            throw BadType(exp_type->get_repr(), top->get_repr(), expr);
        }
    }

    // by design propagate lhs type it should really matter
    f_type_stack.push_back(exp_type);
}

// fun: bitwise x bitwise -> bitwise
void SimpleInferrer::walk_binary_bitwise_postorder(const Expr_ptr expr)
{
    Type_ptr exp_type;

    { // RHS
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!f_tm.is_boolean(top) &&
            !f_tm.is_word(top)) {
            throw BadType(top->get_repr(), f_em.make_boolean_type(), expr);
        }
        exp_type = top;
    }

    { // LHS
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!f_tm.is_boolean(top) &&
            !f_tm.is_word(top)) {
            throw BadType(top->get_repr(), f_em.make_integer_type(), expr);
        }

        // type matching is mandatory here
        if (top != exp_type) {
            throw BadType(exp_type->get_repr(), top->get_repr(), expr);
        }
    }

    // by design propagate lhs type it should really matter
    f_type_stack.push_back(exp_type);
}

// fun: arithmetical x arithmetical -> boolean
void SimpleInferrer::walk_binary_relational_postorder(const Expr_ptr expr)
{
    Type_ptr exp_type;

    { // RHS
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!f_tm.is_boolean(top) &&
            !f_tm.is_word(top)) {
            throw BadType(top->get_repr(), f_em.make_boolean_type(), expr);
        }
        exp_type = top;
    }

    { // LHS
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!f_tm.is_boolean(top) &&
            !f_tm.is_word(top)) {
            throw BadType(top->get_repr(), f_em.make_integer_type(), expr);
        }

        // type matching is mandatory here
        if (top != exp_type) {
            throw BadType(exp_type->get_repr(), top->get_repr(), expr);
        }
    }

    f_type_stack.push_back(f_tm.find_boolean());
}

// fun: boolean x T x T -> T
void SimpleInferrer::walk_ternary_ite_postorder(const Expr_ptr expr)
{
    Type_ptr exp_type;

    { // RHS (=else)
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!f_tm.is_boolean(top) &&
            !f_tm.is_word(top)) {
            throw BadType(top->get_repr(), f_em.make_boolean_type(), expr);
        }
        exp_type = top;
    }

    { // LHS(=then)
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!f_tm.is_boolean(top) &&
            !f_tm.is_word(top)) {
            throw BadType(top->get_repr(), f_em.make_integer_type(), expr);
        }

        // type matching is mandatory here
        if (top != exp_type) {
            throw BadType(exp_type->get_repr(), top->get_repr(), expr);
        }
    }

    { // condition is always boolean
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!f_tm.is_boolean(top)) {
            throw BadType(top->get_repr(), f_em.make_integer_type(), expr);
        }
    }

    f_type_stack.push_back(exp_type);
}
