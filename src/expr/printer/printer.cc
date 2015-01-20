/**
 *  @file printer.cc
 *  @brief Expr printers
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

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>
#include <expr/printer/printer.hh>

#define SHOW_SCOPE_ASSOCIATIVITY 1

Printer::Printer()
    : f_os(std::cout)
{}

Printer::Printer(std::ostream& os)
    : f_os(os)
{}

Printer::~Printer()
{}

void Printer::pre_hook()
{}

void Printer::post_hook()
{ f_os << std::flush; }

Printer& Printer::operator<<(Expr_ptr expr)
{ this->operator()(expr); return *this; }

Printer& Printer::operator<<(Expr& expr)
{ this->operator()(&expr); return *this; }

Printer& Printer::operator<< (const std::string& str)
{ f_os << str << std::flush; return *this; }

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

bool Printer::walk_next_preorder(const Expr_ptr expr)
{ f_os << "next("; return true; }
void Printer::walk_next_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_neg_preorder(const Expr_ptr expr)
{ f_os << "- "; return true; }
void Printer::walk_neg_postorder(const Expr_ptr expr)
{}

bool Printer::walk_not_preorder(const Expr_ptr expr)
{ f_os << "not "; return true; }
void Printer::walk_not_postorder(const Expr_ptr expr)
{}

bool Printer::walk_bw_not_preorder(const Expr_ptr expr)
{ f_os << "! "; return true; }
void Printer::walk_bw_not_postorder(const Expr_ptr expr)
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
{ f_os << " - "; return true; }
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
{ f_os << " and "; return true; }
void Printer::walk_and_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_bw_and_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_bw_and_inorder(const Expr_ptr expr)
{ f_os << " & "; return true; }
void Printer::walk_bw_and_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_or_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_or_inorder(const Expr_ptr expr)
{ f_os << " or "; return true; }
void Printer::walk_or_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_xor_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_xor_inorder(const Expr_ptr expr)
{ f_os << " xor "; return true; }
void Printer::walk_xor_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_bw_or_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_bw_or_inorder(const Expr_ptr expr)
{ f_os << " | "; return true; }
void Printer::walk_bw_or_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_bw_xor_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_bw_xor_inorder(const Expr_ptr expr)
{ f_os << " ^ "; return true; }
void Printer::walk_bw_xor_postorder(const Expr_ptr expr)
{ f_os << ")"; }

bool Printer::walk_bw_xnor_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_bw_xnor_inorder(const Expr_ptr expr)
{ f_os << " ~ "; return true; }
void Printer::walk_bw_xnor_postorder(const Expr_ptr expr)
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

bool Printer::walk_cast_preorder(const Expr_ptr expr)
{ f_os << "("; return true; }
bool Printer::walk_cast_inorder(const Expr_ptr expr)
{ f_os << ") "; return true; }
void Printer::walk_cast_postorder(const Expr_ptr expr)
{ }

bool Printer::walk_type_preorder(const Expr_ptr expr)
{ return true; }
bool Printer::walk_type_inorder(const Expr_ptr expr)
{ f_os << "("; return true; }
void Printer::walk_type_postorder(const Expr_ptr expr)
{ f_os << ")";}

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
{ f_os << " = "; return true; }
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

bool Printer::walk_dot_preorder(const Expr_ptr expr)
{
#if SHOW_SCOPE_ASSOCIATIVITY
    f_os << "[[ ";
#endif

    return true;
}
bool Printer::walk_dot_inorder(const Expr_ptr expr)
{
    // if (! ExprMgr::INSTANCE().is_empty( expr -> lhs()))
    f_os << ".";

    return true;
}
void Printer::walk_dot_postorder(const Expr_ptr expr)
{
#if SHOW_SCOPE_ASSOCIATIVITY
    f_os << " ]]";
#endif
}

bool Printer::walk_params_preorder(const Expr_ptr expr)
{ return true; }
bool Printer::walk_params_inorder(const Expr_ptr expr)
{ f_os << "("; return true; }
void Printer::walk_params_postorder(const Expr_ptr expr)
{ f_os << ")";}

bool Printer::walk_subscript_preorder(const Expr_ptr expr)
{ return true; }
bool Printer::walk_subscript_inorder(const Expr_ptr expr)
{ f_os << "["; return true; }
void Printer::walk_subscript_postorder(const Expr_ptr expr)
{ f_os << "]"; }

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

#include <iomanip>
using std::hex;
using std::dec;
using std::oct;

void Printer::walk_leaf(const Expr_ptr expr)
{
    // if (ExprMgr::INSTANCE().is_empty(expr))
    //     return;

    switch (expr->f_symb) {
    case ICONST: f_os << dec << expr->value(); break;
    case HCONST: f_os << hex << "0x" << expr->value(); break;
    case OCONST: f_os << oct << "0"  << expr->value(); break;
    case IDENT:  f_os << expr->atom(); break;
    case UNDEF:  f_os << "UNDEF"; break;
    default: assert(0);
    }
}
