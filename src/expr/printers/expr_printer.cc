/*
  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >

  This library is free software; you can redistribute it and/or
  modify it under the terms of the GNU Lesser General Public
  License as published by the Free Software Foundation; either
  version 2.1 of the License, or (at your option) any later version.

  This library is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public
  License along with this library; if not, write to the Free Software
  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

*/

/**
 * @file printer.cc
 *
 * @brief Expression printer
 *
 */
#include <common.hh>

#include <expr.hh>
#include <expr_printer.hh>

Printer::Printer()
  : f_os(cout)
{}

Printer::Printer(ostream& os)
  : f_os(os)
{}

Printer::~Printer()
{}

void Printer::pre_hook()
{}

void Printer::post_hook()
{ f_os << flush; }

Printer& Printer::operator<<(Expr_ptr expr)
{ this->operator()(expr); return *this; }

Printer& Printer::operator<< (const string& str) {
  f_os << str << flush; return (*this);
}

// walker interface
bool Printer::walk_F_preorder(const Expr_ptr expr)
{ f_os << "F ("; return true; }
void Printer::walk_F_postorder(const Expr_ptr expr)
{ f_os << ")"; }
bool Printer::walk_G_preorder(const Expr_ptr expr)
{ f_os << "G ("; return true; }
void Printer::walk_G_postorder(const Expr_ptr expr)
{ f_os << ")"; }
bool Printer::walk_X_preorder(const Expr_ptr expr)
{ f_os << "X ("; return true; }
void Printer::walk_X_postorder(const Expr_ptr expr)
{ f_os << ")"; }
bool Printer::walk_U_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_U_inorder(const Expr_ptr expr)
{ f_os << " U "; return true; }
void Printer::walk_U_postorder(const Expr_ptr expr)
{ f_os << ")"; }
bool Printer::walk_R_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_R_inorder(const Expr_ptr expr)
{ f_os << " R "; return true; }
void Printer::walk_R_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_AF_preorder(const Expr_ptr expr)
{ f_os << "AF ("; return true; }
void Printer::walk_AF_postorder(const Expr_ptr expr)
{ f_os << ")"; }
bool Printer::walk_AG_preorder(const Expr_ptr expr)
{ f_os << "AG ("; return true; }
void Printer::walk_AG_postorder(const Expr_ptr expr)
{ f_os << ")"; }
bool Printer::walk_AX_preorder(const Expr_ptr expr)
{ f_os << "AX ("; return true; }
void Printer::walk_AX_postorder(const Expr_ptr expr)
{ f_os << ")"; }
bool Printer::walk_AU_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_AU_inorder(const Expr_ptr expr)
{ f_os << " AU "; return true; }
void Printer::walk_AU_postorder(const Expr_ptr expr)
{ f_os << ")"; }
bool Printer::walk_AR_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_AR_inorder(const Expr_ptr expr)
{ f_os << " AR "; return true; }
void Printer::walk_AR_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_EF_preorder(const Expr_ptr expr)
{ f_os << "EF ("; return true; }
void Printer::walk_EF_postorder(const Expr_ptr expr)
{ f_os << ")"; }
bool Printer::walk_EG_preorder(const Expr_ptr expr)
{ f_os << "EG ("; return true; }
void Printer::walk_EG_postorder(const Expr_ptr expr)
{ f_os << ")"; }
bool Printer::walk_EX_preorder(const Expr_ptr expr)
{ f_os << "EX ("; return true; }
void Printer::walk_EX_postorder(const Expr_ptr expr)
{ f_os << ")"; }
bool Printer::walk_EU_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_EU_inorder(const Expr_ptr expr)
{ f_os << " EU "; return true; }
void Printer::walk_EU_postorder(const Expr_ptr expr)
{ f_os << ")"; }
bool Printer::walk_ER_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_ER_inorder(const Expr_ptr expr)
{ f_os << " ER "; return true; }
void Printer::walk_ER_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_init_preorder(const Expr_ptr expr)
{ f_os << "init("; return true; }
void Printer::walk_init_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_next_preorder(const Expr_ptr expr)
{ f_os << "next("; return true; }
void Printer::walk_next_postorder(const Expr_ptr expr)
{ f_os << ")"; }

// highest binding level??
bool Printer::walk_neg_preorder(const Expr_ptr expr)
{ f_os << "- "; return true; }
void Printer::walk_neg_postorder(const Expr_ptr expr)
{}

bool Printer::walk_not_preorder(const Expr_ptr expr)
{ f_os << "! "; return true; }
void Printer::walk_not_postorder(const Expr_ptr expr)
{}

bool Printer::walk_add_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_add_inorder(const Expr_ptr expr)
{ f_os << " + "; return true; }
void Printer::walk_add_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_sub_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_sub_inorder(const Expr_ptr expr)
{ f_os << " + "; return true; }
void Printer::walk_sub_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_div_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_div_inorder(const Expr_ptr expr)
{ f_os << " / "; return true; }
void Printer::walk_div_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_mul_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_mul_inorder(const Expr_ptr expr)
{ f_os << " * "; return true; }
void Printer::walk_mul_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_mod_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_mod_inorder(const Expr_ptr expr)
{ f_os << " % "; return true; }
void Printer::walk_mod_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_and_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_and_inorder(const Expr_ptr expr)
{ f_os << " & "; return true; }
void Printer::walk_and_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_or_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_or_inorder(const Expr_ptr expr)
{ f_os << " | "; return true; }
void Printer::walk_or_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_xor_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_xor_inorder(const Expr_ptr expr)
{ f_os << " xor "; return true; }
void Printer::walk_xor_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_xnor_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_xnor_inorder(const Expr_ptr expr)
{ f_os << " xnor "; return true; }
void Printer::walk_xnor_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_implies_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_implies_inorder(const Expr_ptr expr)
{ f_os << " -> "; return true; }
void Printer::walk_implies_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_iff_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_iff_inorder(const Expr_ptr expr)
{ f_os << " <-> "; return true; }
void Printer::walk_iff_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_lshift_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_lshift_inorder(const Expr_ptr expr)
{ f_os << " << "; return true; }
void Printer::walk_lshift_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_rshift_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_rshift_inorder(const Expr_ptr expr)
{ f_os << " >> "; return true; }
void Printer::walk_rshift_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_eq_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_eq_inorder(const Expr_ptr expr)
{ f_os << " == "; return true; }
void Printer::walk_eq_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_ne_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_ne_inorder(const Expr_ptr expr)
{ f_os << " != "; return true; }
void Printer::walk_ne_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_gt_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_gt_inorder(const Expr_ptr expr)
{ f_os << " > "; return true; }
void Printer::walk_gt_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_ge_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_ge_inorder(const Expr_ptr expr)
{ f_os << " >= "; return true; }
void Printer::walk_ge_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_lt_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_lt_inorder(const Expr_ptr expr)
{ f_os << " < "; return true; }
void Printer::walk_lt_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_le_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_le_inorder(const Expr_ptr expr)
{ f_os << " <= "; return true; }
void Printer::walk_le_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_ite_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_ite_inorder(const Expr_ptr expr)
{ f_os << " : "; return true; }
void Printer::walk_ite_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_cond_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_cond_inorder(const Expr_ptr expr)
{ f_os << " ? "; return true; }
void Printer::walk_cond_postorder(const Expr_ptr expr)
{ f_os << ")"; }


bool Printer::walk_set_preorder(const Expr_ptr expr)
{ f_os << "{"; return true; }
void Printer::walk_set_postorder(const Expr_ptr expr)
{ f_os << "}"; }

bool Printer::walk_comma_preorder(const Expr_ptr expr)
{ return true; }
bool Printer::walk_comma_inorder(const Expr_ptr expr)
{ f_os << ", "; return true; }
void Printer::walk_comma_postorder(const Expr_ptr expr)
{}

void Printer::walk_leaf(const Expr_ptr expr)

{
  ExprType symb = expr->f_symb;

  if (symb == ICONST) {
    f_os << expr->f_ull;
  }
  else if (symb == UWCONST) {
  }
  else if (symb == SWCONST) {
  }
  else if (symb == IDENT) {
    f_os << (*expr->f_atom);
  }
  // else if (symb == LITERAL) {
  //   f_os << expr->f_atom;
  // }

  else assert(0);
}
