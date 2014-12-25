/**
 *  @file normalizer.cc
 *  @brief Formula normalizer
 *
 *  The normalizer can be used to determine whether a certain formula
 *  is a pure propositional, invariant (G only), or full LTL temporal
 *  property. Formula is converted to a canonical positive normal
 *  form, by pushing negations to the leaves and rewriting temporal
 *  operators using LTL identities. This is useful in BMC algorithms
 *  to select the appropriate verification strategy depending on the
 *  particular kind of formula at hand.
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
#include <type.hh>
#include <proxy.hh>

#include <normalizer.hh>
#include <model_mgr.hh>

// uncommment following line to enable post_node_hook debug (verbose!)
// #define DEBUG_NORMALIZER

Normalizer::Normalizer(ModelMgr& owner)
    : f_owner(owner)
    , f_em(ExprMgr::INSTANCE())
{ DEBUG << "Created Normalizer @" << this << endl; }

Normalizer::~Normalizer()
{ DEBUG << "Destroying Normalizer @" << this << endl; }

Expr_ptr Normalizer::process(Expr_ptr expr)
{
    f_result_stack.clear();

    f_polarity = false;
    f_invariant = true;

    // invoke walker on the body of the expr to be processed
    (*this)(expr);

    assert(1 == f_result_stack.size());
    return f_result_stack.back();
}

void Normalizer::pre_hook()
{}

void Normalizer::post_hook()
{}

void Normalizer::pre_node_hook(Expr_ptr expr)
{}

void Normalizer::post_node_hook(Expr_ptr expr)
{}

void Normalizer::walk_leaf(const Expr_ptr expr)
{
    if (! f_polarity) {
        f_result_stack.push_back( expr );
    }
    else if (f_em.is_false( expr)) {
        f_result_stack.push_back( f_em.make_true());
    }
    else if (f_em.is_true( expr)) {
        f_result_stack.push_back( f_em.make_false());
    }
    else {
        f_result_stack.push_back( f_em.make_not( expr));
    }
}

bool Normalizer::walk_F_preorder(const Expr_ptr expr)
{
    rewrite( ! f_polarity
             ? f_em.make_U( f_em.make_true(), expr->lhs())
             : f_em.make_R( f_em.make_false(), f_em.make_not( expr->lhs())));

    return false; // don't care
}
void Normalizer::walk_F_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_G_preorder(const Expr_ptr expr)
{
    rewrite( ! f_polarity
             ? f_em.make_R( f_em.make_false(), expr->lhs())
             : f_em.make_U( f_em.make_true(), f_em.make_not( expr->lhs())));

    return false; // don't care
}
void Normalizer::walk_G_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_X_preorder(const Expr_ptr expr)
{
    if (f_polarity)
        rewrite( f_em.make_X( f_em.make_not( expr)));

    f_polarity = false;
    return true;
}

void Normalizer::walk_X_postorder(const Expr_ptr expr)
{
    Expr_ptr lhs = f_result_stack.back(); f_result_stack.pop_back();
    f_result_stack.push_back( f_em.make_X( lhs));
}

bool Normalizer::walk_U_preorder(const Expr_ptr expr)
{
    if (f_polarity)
        rewrite( f_em.make_R( f_em.make_not( expr->lhs()),
                              f_em.make_not( expr->rhs())));

    f_polarity = false;
    return true;
}

bool Normalizer::walk_U_inorder(const Expr_ptr expr)
{ return true; }
void Normalizer::walk_U_postorder(const Expr_ptr expr)
{
    Expr_ptr rhs = f_result_stack.back(); f_result_stack.pop_back();
    Expr_ptr lhs = f_result_stack.back(); f_result_stack.pop_back();

    if (f_em.is_true( lhs))
        f_result_stack.push_back( f_em.make_F( rhs));
    else
        f_result_stack.push_back( f_em.make_U( lhs, rhs));

}

bool Normalizer::walk_R_preorder(const Expr_ptr expr)
{
    if (f_polarity)
        rewrite( f_em.make_U( f_em.make_not( expr->lhs()),
                              f_em.make_not( expr->rhs())));

    f_polarity = false;
    return true;
}

bool Normalizer::walk_R_inorder(const Expr_ptr expr)
{ return true; }
void Normalizer::walk_R_postorder(const Expr_ptr expr)
{
    Expr_ptr rhs = f_result_stack.back(); f_result_stack.pop_back();
    Expr_ptr lhs = f_result_stack.back(); f_result_stack.pop_back();

    if (f_em.is_false( lhs))
        f_result_stack.push_back( f_em.make_G( rhs));
    else
        f_result_stack.push_back( f_em.make_R( lhs, rhs));
}

/* NOT operator is not rewritten, thus formula is PNF by construction */
bool Normalizer::walk_not_preorder(const Expr_ptr expr)
{
    f_polarity = ! f_polarity;
    return true;
}
void Normalizer::walk_not_postorder(const Expr_ptr expr)
{}

bool Normalizer::walk_and_preorder(const Expr_ptr expr)
{
    if (f_em.is_false( expr->lhs()) ||
        f_em.is_false( expr->rhs())) {
        f_result_stack.push_back( f_em.make_false());
        return false;
    }

    if (f_em.is_true( expr->lhs()) ||
        expr->lhs() == expr->rhs()) {
        rewrite (expr->rhs());
        return false; // don't care
    }

    if (f_em.is_true( expr->rhs())) {
        rewrite( expr->lhs());
        return false; // don't care
    }

    if (f_polarity)
        rewrite( f_em.make_or( f_em.make_not( expr->lhs()),
                               f_em.make_not( expr->rhs())));
    f_polarity = false;
    return true;
}
bool Normalizer::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void Normalizer::walk_and_postorder(const Expr_ptr expr)
{
    Expr_ptr rhs = f_result_stack.back(); f_result_stack.pop_back();
    Expr_ptr lhs = f_result_stack.back(); f_result_stack.pop_back();

    f_result_stack.push_back( f_em.make_and( lhs, rhs));
}


bool Normalizer::walk_or_preorder(const Expr_ptr expr)
{
    if (f_em.is_true( expr->lhs()) ||
        f_em.is_true( expr->rhs())) {
        f_result_stack.push_back( f_em.make_true());
        return false;
    }

    if (f_em.is_false( expr->lhs()) ||
        expr->lhs() == expr->rhs()) {
        rewrite (expr->rhs());
        return false; // don't care
    }

    if (f_em.is_false( expr->rhs())) {
        rewrite( expr->lhs());
        return false; // don't care
    }

    if (f_polarity) {
        rewrite( f_em.make_and( f_em.make_not( expr->lhs()),
                                f_em.make_not( expr->rhs())));
    }

    f_polarity = false;
    return true;
}

bool Normalizer::walk_or_inorder(const Expr_ptr expr)
{  return true; }
void Normalizer::walk_or_postorder(const Expr_ptr expr)
{
    Expr_ptr rhs = f_result_stack.back(); f_result_stack.pop_back();
    Expr_ptr lhs = f_result_stack.back(); f_result_stack.pop_back();

    f_result_stack.push_back( f_em.make_or( lhs, rhs));
}

/* ! (a -> b) === a & !b */
bool Normalizer::walk_implies_preorder(const Expr_ptr expr)
{
    if (f_em.is_false( expr->lhs()) ||
        f_em.is_true( expr->rhs())) {
        f_result_stack.push_back( f_em.make_true());
        return false;
    }

    if (f_em.is_false( expr->lhs())) {
        rewrite (expr->rhs());
        return false; // don't care
    }

    if (f_em.is_true( expr->rhs())) {
        rewrite( expr->lhs());
        return false; // don't care
    }

    if (f_polarity)
        rewrite( f_em.make_and( expr->lhs(),
                                f_em.make_not( expr->rhs())));
    f_polarity = false;
    return true;
}
bool Normalizer::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void Normalizer::walk_implies_postorder(const Expr_ptr expr)
{
    Expr_ptr rhs = f_result_stack.back(); f_result_stack.pop_back();
    Expr_ptr lhs = f_result_stack.back(); f_result_stack.pop_back();

    f_result_stack.push_back( f_em.make_implies( lhs, rhs));
}

/* ! (a <-> b) === !( a -> b && b - > a) === ! ( a-> b ) || ! ( b -> a ) */
bool Normalizer::walk_iff_preorder(const Expr_ptr expr)
{
    if (expr->lhs() == expr->rhs()) {
        f_result_stack.push_back( f_em.make_true());
        return false;
    }

    if (f_polarity)
        rewrite( f_em.make_or( f_em.make_not( f_em.make_implies( expr->lhs(), expr->rhs())),
                               f_em.make_not( f_em.make_implies( expr->rhs(), expr->lhs()))));

    f_polarity = false;
    return true;
}
bool Normalizer::walk_iff_inorder(const Expr_ptr expr)
{ return true; }
void Normalizer::walk_iff_postorder(const Expr_ptr expr)
{
    Expr_ptr rhs = f_result_stack.back(); f_result_stack.pop_back();
    Expr_ptr lhs = f_result_stack.back(); f_result_stack.pop_back();

    f_result_stack.push_back( f_em.make_iff( lhs, rhs));
}

/* -- relational operators ------------------------------------------------- */
bool Normalizer::walk_eq_preorder(const Expr_ptr expr)
{
    f_result_stack.push_back( expr );
    return false;
}
bool Normalizer::walk_eq_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_eq_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_ne_preorder(const Expr_ptr expr)
{
    f_result_stack.push_back( expr );
    return false;
}
bool Normalizer::walk_ne_inorder(const Expr_ptr expr)
{ assert(false); }
void Normalizer::walk_ne_postorder(const Expr_ptr expr)
{ assert(false);}

bool Normalizer::walk_gt_preorder(const Expr_ptr expr)
{ return false; }
bool Normalizer::walk_gt_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_gt_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_ge_preorder(const Expr_ptr expr)
{
    f_result_stack.push_back( expr );
    return false;
}
bool Normalizer::walk_ge_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_ge_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_lt_preorder(const Expr_ptr expr)
{
    f_result_stack.push_back( expr );
    return false;
}
bool Normalizer::walk_lt_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_lt_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_le_preorder(const Expr_ptr expr)
{
    f_result_stack.push_back( expr );
    return false;
}
bool Normalizer::walk_le_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_le_postorder(const Expr_ptr expr)
{ assert(false); }

/* -- unsupported operators ------------------------------------------------- */
bool Normalizer::walk_neg_preorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_neg_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_next_preorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_next_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_add_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_add_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_add_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_sub_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_sub_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_sub_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_div_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_div_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_div_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_mul_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_mul_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_mul_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_mod_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_mod_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_mod_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_bw_not_preorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_bw_not_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_bw_and_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_bw_and_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_bw_and_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_bw_or_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_bw_or_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_bw_or_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_bw_xor_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_bw_xor_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_bw_xor_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_bw_xnor_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_bw_xnor_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_bw_xnor_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_cast_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_cast_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_cast_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_type_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_type_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_type_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_lshift_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_lshift_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_lshift_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_rshift_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_rshift_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_rshift_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_ite_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_ite_inorder(const Expr_ptr expr)
{ assert(false); return false;  }
void Normalizer::walk_ite_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_cond_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_cond_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_cond_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_dot_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_dot_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_dot_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_params_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_params_inorder(const Expr_ptr expr)
{ assert( false ); return false; }
void Normalizer::walk_params_postorder(const Expr_ptr expr)
{ assert( false ); }

bool Normalizer::walk_subscript_preorder(const Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_subscript_inorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_subscript_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_set_preorder(const Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_set_postorder(const Expr_ptr expr)
{ assert(false); }

bool Normalizer::walk_comma_preorder(Expr_ptr expr)
{ assert(false); return false; }
bool Normalizer::walk_comma_inorder(Expr_ptr expr)
{ assert(false); return false; }
void Normalizer::walk_comma_postorder(Expr_ptr expr)
{ assert(false); }
