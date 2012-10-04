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
    , f_mm(owner)
    , f_em(owner.em())
    , f_tm(owner.tm())
{
    f_integer_or_boolean.push_back(f_em.make_integer_type());
    f_integer_or_boolean.push_back(f_em.make_boolean_type());

    f_boolean = f_em.make_boolean_type();
    f_integer = f_em.make_integer_type();

    DEBUG << "Created Inferrer @" << this << endl;
}

Inferrer::~Inferrer()
{ DEBUG << "Destroying Inferrer @" << this << endl; }

Type_ptr Inferrer::process(Expr_ptr ctx, Expr_ptr body)
{
    Type_ptr res = NULL;
    INFO << "Determining type for expression " << ctx << "::" << body << endl;

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

void Inferrer::pre_hook()
{}
void Inferrer::post_hook()
{}

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

bool Inferrer::walk_init_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_init_postorder(const Expr_ptr expr)
{ walk_unary_fsm_postorder(expr); }

bool Inferrer::walk_next_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_next_postorder(const Expr_ptr expr)
{ walk_unary_fsm_postorder(expr); }

// bool Inferrer::walk_at_preorder(const Expr_ptr expr)
// { return cache_miss(expr); }
// bool Inferrer::walk_at_inorder(const Expr_ptr expr)
// { return true; }
// void Inferrer::walk_at_postorder(const Expr_ptr expr)
// { walk_binary_fsm_postorder(expr); }

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
{ walk_binary_logical_postorder(expr); }

bool Inferrer::walk_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_or_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool Inferrer::walk_xor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_xor_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_xor_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool Inferrer::walk_xnor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_xnor_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_xnor_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

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
{ walk_binary_relational_postorder(expr); }

bool Inferrer::walk_ne_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_ne_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_ne_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

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
{}

bool Inferrer::walk_set_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Inferrer::walk_set_postorder(const Expr_ptr expr)
{}

bool Inferrer::walk_comma_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_comma_inorder(const Expr_ptr expr)
{ return true; }
void Inferrer::walk_comma_postorder(const Expr_ptr expr)
{}

bool Inferrer::walk_bits_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_bits_inorder(const Expr_ptr expr)
{
    Type_ptr tmp = f_type_stack.back();
    Expr_ptr ctx = tmp->get_repr();
    f_ctx_stack.push_back(ctx);
    return true;
}
void Inferrer::walk_bits_postorder(const Expr_ptr expr)
{
    assert(0);
}

bool Inferrer::walk_dot_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Inferrer::walk_dot_inorder(const Expr_ptr expr)
{
    Type_ptr tmp = f_type_stack.back();
    Expr_ptr ctx = tmp->get_repr();
    f_ctx_stack.push_back(ctx);
    return true;
}
void Inferrer::walk_dot_postorder(const Expr_ptr expr)
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
void Inferrer::walk_leaf(const Expr_ptr expr)
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
ISymbol_ptr Inferrer::resolve(const Expr_ptr ctx, const Expr_ptr frag)
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

// fun: temporal -> temporal
void Inferrer::walk_unary_temporal_postorder(const Expr_ptr expr)
{
    const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();

    if (!f_tm.is_boolean(top) &&
        !f_tm.is_temporal(top)) {

        throw BadType(top->get_repr(),
                      f_em.make_boolean_type(), expr);
    }

    f_type_stack.push_back(f_tm.find_temporal());
}

// fun: temporal x temporal -> temporal
void Inferrer::walk_binary_temporal_postorder(const Expr_ptr expr)
{
    { // RHS
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!f_tm.is_boolean(top))
            throw BadType(top->get_repr(), f_boolean, expr);
    }

    { // LHS
        const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
        if (!f_tm.is_boolean(top))
            throw BadType(top->get_repr(), f_boolean, expr);
    }

    f_type_stack.push_back(f_tm.find_temporal());
}

// fun: T -> T
void Inferrer::walk_unary_fsm_postorder(const Expr_ptr expr)
{
    const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
    f_type_stack.push_back(top); // propagate
}

// fun: int x boolean -> boolean
// void Inferrer::walk_binary_fsm_postorder(const Expr_ptr expr)
// {
//     const Type_ptr rhs = f_type_stack.back(); f_type_stack.pop_back();
//     if (!f_tm.is_boolean(rhs)) {
//         throw BadType(rhs->get_repr(), f_em.make_boolean_type(), expr);
//     }

//     f_type_stack.push_back(rhs); // propagate

//     const Type_ptr lhs = f_type_stack.back(); f_type_stack.pop_back();
//     if (!f_tm.is_integer(lhs)) {
//         throw BadType(lhs->get_repr(), f_em.make_unsigned_type(0), expr); // must be a const
//     }
// }

// fun: arithm -> arithm
void Inferrer::walk_unary_arithmetical_postorder(const Expr_ptr expr)
{
    const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
    if (!f_tm.is_integer(top)) {
        throw BadType(top->get_repr(), f_integer, expr);
    }

    f_type_stack.push_back(top); // propagate
}

// fun: logical -> logical
void Inferrer::walk_unary_logical_postorder(const Expr_ptr expr)
{
    const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
    if (!f_tm.is_boolean(top)) {
        throw BadType(top->get_repr(), f_boolean, expr);
    }

    f_type_stack.push_back(top); // propagate
}

// fun: arithm, arithm -> arithm
void Inferrer::walk_binary_arithmetical_postorder(const Expr_ptr expr)
{
    const Type_ptr rhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!f_tm.is_integer(rhs)) {
        throw BadType(rhs->get_repr(), f_integer, expr);
    }

    const Type_ptr lhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!f_tm.is_integer(lhs)) {
        throw BadType(lhs->get_repr(), f_integer, expr);
    }

    // type matching is mandatory here
    if ((lhs != rhs) && !f_tm.is_iconst(lhs) && !f_tm.is_iconst(rhs)) {
        throw BadType(rhs->get_repr(), lhs->get_repr(), expr);
    }

    // generic integer
    f_type_stack.push_back(f_tm.find_integer());
}

// fun: logical x logical -> logical
void Inferrer::walk_binary_logical_postorder(const Expr_ptr expr)
{
    const Type_ptr rhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!f_tm.is_boolean(rhs)) {
        throw BadType(rhs->get_repr(), f_boolean, expr);
    }

    const Type_ptr lhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!f_tm.is_boolean(lhs)) {
        throw BadType(lhs->get_repr(), f_boolean, expr);
    }

    // type matching is mandatory here
    if ((lhs != rhs) && !f_tm.is_iconst(lhs) && !f_tm.is_iconst(rhs)) {
        throw BadType(rhs->get_repr(), rhs->get_repr(), expr);
    }

    f_type_stack.push_back(lhs);
}

// fun: bitwise x bitwise -> bitwise
void Inferrer::walk_binary_bitwise_postorder(const Expr_ptr expr)
{
    const Type_ptr rhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!f_tm.is_integer(rhs)) {
        throw BadType(rhs->get_repr(), f_integer, expr);
    }

    const Type_ptr lhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!f_tm.is_integer(lhs)) {
        throw BadType(lhs->get_repr(), f_integer, expr);
    }

    // type matching is mandatory here
    if ((lhs != rhs) && !f_tm.is_iconst(lhs) && !f_tm.is_iconst(rhs)) {
        throw BadType(rhs->get_repr(), rhs->get_repr(), expr);
    }

    f_type_stack.push_back(lhs);
}

// fun: arithmetical x arithmetical -> boolean
void Inferrer::walk_binary_relational_postorder(const Expr_ptr expr)
{
    const Type_ptr rhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!f_tm.is_boolean(rhs) &&
        !f_tm.is_integer(rhs)) {
        throw BadType(rhs->get_repr(), f_integer_or_boolean, expr);
    }

    const Type_ptr lhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!f_tm.is_boolean(lhs) &&
        !f_tm.is_integer(lhs)) {
        throw BadType(lhs->get_repr(), f_integer_or_boolean, expr);
    }

    // type matching is mandatory here
    if ((lhs != rhs) && !f_tm.is_iconst(lhs) && !f_tm.is_iconst(rhs)) {
        throw BadType(rhs->get_repr(), rhs->get_repr(), expr);
    }

    f_type_stack.push_back(f_tm.find_boolean());
}

// fun: boolean x T x T -> T
void Inferrer::walk_ternary_ite_postorder(const Expr_ptr expr)
{
    const Type_ptr rhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!f_tm.is_boolean(rhs) &&
        !f_tm.is_integer(rhs)) {
        throw BadType(rhs->get_repr(), f_integer_or_boolean, expr);
    }

    const Type_ptr lhs = f_type_stack.back(); f_type_stack.pop_back();
    if (!f_tm.is_boolean(lhs) &&
        !f_tm.is_integer(lhs)) {
        throw BadType(lhs->get_repr(), f_integer_or_boolean, expr);
    }

    // type matching is mandatory here
    if ((lhs != rhs) && !f_tm.is_iconst(lhs) && !f_tm.is_iconst(rhs)) {
        throw BadType(rhs->get_repr(), rhs->get_repr(), expr);
    }

    // condition is always boolean
    const Type_ptr cond = f_type_stack.back(); f_type_stack.pop_back();
    if (!f_tm.is_boolean(cond)) {
        throw BadType(cond->get_repr(), f_boolean, expr);
    }

    f_type_stack.push_back(lhs);
}
