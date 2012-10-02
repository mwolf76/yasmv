/**
 *  @file expr_validator.cc
 *  @brief Expr validators
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
#include <expr_validator.hh>

Validator::Validator()
{}

Validator::~Validator()
{}

void Validator::pre_hook()
{}

void Validator::post_hook()
{}

// walker interface
bool Validator::walk_F_preorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_F_postorder(const Expr_ptr expr)
{}

bool Validator::walk_G_preorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_G_postorder(const Expr_ptr expr)
{}

bool Validator::walk_X_preorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_X_postorder(const Expr_ptr expr)
{}

bool Validator::walk_U_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_U_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_U_postorder(const Expr_ptr expr)
{}

bool Validator::walk_R_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_R_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_R_postorder(const Expr_ptr expr)
{}

bool Validator::walk_AF_preorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_AF_postorder(const Expr_ptr expr)
{}

bool Validator::walk_AG_preorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_AG_postorder(const Expr_ptr expr)
{}

bool Validator::walk_AX_preorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_AX_postorder(const Expr_ptr expr)
{}

bool Validator::walk_AU_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_AU_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_AU_postorder(const Expr_ptr expr)
{}

bool Validator::walk_AR_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_AR_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_AR_postorder(const Expr_ptr expr)
{}

bool Validator::walk_EF_preorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_EF_postorder(const Expr_ptr expr)
{}
bool Validator::walk_EG_preorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_EG_postorder(const Expr_ptr expr)
{}

bool Validator::walk_EX_preorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_EX_postorder(const Expr_ptr expr)
{}

bool Validator::walk_EU_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_EU_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_EU_postorder(const Expr_ptr expr)
{}

bool Validator::walk_ER_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_ER_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_ER_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_init_preorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_init_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_next_preorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_next_postorder(const Expr_ptr expr)
{}

bool Validator::walk_neg_preorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_neg_postorder(const Expr_ptr expr)
{}

bool Validator::walk_not_preorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_not_postorder(const Expr_ptr expr)
{}

bool Validator::walk_add_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_add_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_add_postorder(const Expr_ptr expr)
{}


bool Validator::walk_sub_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_sub_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_sub_postorder(const Expr_ptr expr)
{}

bool Validator::walk_div_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_div_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_div_postorder(const Expr_ptr expr)
{}

bool Validator::walk_mul_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_mul_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_mul_postorder(const Expr_ptr expr)
{}

bool Validator::walk_mod_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_mod_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_mod_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_and_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_and_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_or_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_or_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_xor_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_xor_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_xor_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_xnor_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_xnor_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_xnor_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_implies_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_implies_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_iff_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_iff_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_iff_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_lshift_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_lshift_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_lshift_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_rshift_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_rshift_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_rshift_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_eq_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_eq_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_eq_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_ne_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_ne_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_ne_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_gt_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_gt_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_gt_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_ge_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_ge_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_ge_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_lt_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_lt_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_lt_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_le_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_le_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_le_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_ite_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_ite_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_ite_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_cond_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_cond_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_cond_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_set_preorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_set_postorder(const Expr_ptr expr)
{ }

bool Validator::walk_comma_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_comma_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_comma_postorder(const Expr_ptr expr)
{}

bool Validator::walk_bits_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_bits_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_bits_postorder(const Expr_ptr expr)
{}

bool Validator::walk_dot_preorder(const Expr_ptr expr)
{ return true; }
bool Validator::walk_dot_inorder(const Expr_ptr expr)
{ return true; }
void Validator::walk_dot_postorder(const Expr_ptr expr)
{}

/* word print helpers */
string word_repr(const Expr_ptr expr, base_t base)
{
    assert (SWCONST == expr->f_symb || UWCONST == expr->f_symb);

    ostringstream oss;
    oss << "0"
        << ( expr->f_symb == SWCONST ? "s" : "u" )
        << base_char(base)
        << expr->u.f_size
        << to_base(expr->u.f_value, base) ;

    return oss.str();
}

void Validator::walk_leaf(const Expr_ptr expr)
{
    ExprType symb = expr->f_symb;

    // if (FALSE == symb) {
    // }
    // else if (TRUE == symb) {
    // }
    // else
        if (ICONST == symb) {
    }
    else if (UWCONST == symb ||
             SWCONST == symb) {
    }
    else if (IDENT == symb) {
    }

    else assert(0);
}
