/**
 *  @file analyzer.cc
 *  @brief Expr type analyzer
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
#include <analyzer.hh>

Analyzer::Analyzer()
    : f_map()
    , f_kind_stack()
    , f_ctx_stack()
    , f_mm(ModelMgr::INSTANCE())
    , f_em(ExprMgr::INSTANCE())
    , f_tm(TypeMgr::INSTANCE())
{
    // initialize predefined sets
    f_temporal.push_back(EXPR_BOOLEAN);
    f_temporal.push_back(EXPR_G_ONLY_LTL);
    f_temporal.push_back(EXPR_GENERIC_LTL);
    f_temporal.push_back(EXPR_AG_ONLY_CTL);
    f_temporal.push_back(EXPR_GENERIC_CTL);

    f_ltl.push_back(EXPR_BOOLEAN);
    f_ltl.push_back(EXPR_G_ONLY_LTL);
    f_ltl.push_back(EXPR_GENERIC_LTL);

    f_ctl.push_back(EXPR_BOOLEAN);
    f_ctl.push_back(EXPR_AG_ONLY_CTL);
    f_ctl.push_back(EXPR_GENERIC_CTL);

    f_algebraic.push_back(EXPR_ALGEBRAIC);
    f_boolean.push_back(EXPR_BOOLEAN);

    TRACE << "Created Analyzer @" << this << endl;
}

Analyzer::~Analyzer()
{ TRACE << "Destroying Analyzer @" << this << endl; }

ExprKind Analyzer::process(Expr_ptr ctx, Expr_ptr body)
{
    ExprKind res = EXPR_UNKNOWN;
    DEBUG << "Determining kind for expression " << ctx << "::" << body << endl;

    // remove previous results
    f_kind_stack.clear();
    f_ctx_stack.clear();

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);

    // invoke walker on the body of the expr to be processed
    (*this)(body);

    assert(1 == f_kind_stack.size());
    res = f_kind_stack.back();

    ((EXPR_ERROR == res) ? WARN : DEBUG) << body << " is a " << res << endl;
    return res;
}

void Analyzer::pre_hook()
{}
void Analyzer::post_hook()
{}

bool Analyzer::walk_F_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_F_postorder(const Expr_ptr expr)
{ walk_ltl_unary(expr); }

bool Analyzer::walk_G_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_G_postorder(const Expr_ptr expr)
{ walk_ltl_g(expr); }

bool Analyzer::walk_X_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_X_postorder(const Expr_ptr expr)
{ walk_ltl_unary(expr); }

bool Analyzer::walk_U_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_U_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_U_postorder(const Expr_ptr expr)
{ walk_ltl_binary(expr); }

bool Analyzer::walk_R_preorder(const Expr_ptr expr)
{ return cache_miss(expr);  }
bool Analyzer::walk_R_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_R_postorder(const Expr_ptr expr)
{ walk_ltl_binary(expr); }

bool Analyzer::walk_AF_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_AF_postorder(const Expr_ptr expr)
{ walk_ctl_unary(expr); }

bool Analyzer::walk_AG_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_AG_postorder(const Expr_ptr expr)
{ walk_ctl_ag(expr); }

bool Analyzer::walk_AX_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_AX_postorder(const Expr_ptr expr)
{ walk_ctl_unary(expr); }

bool Analyzer::walk_AU_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_AU_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_AU_postorder(const Expr_ptr expr)
{ walk_ctl_binary(expr); }

bool Analyzer::walk_AR_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_AR_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_AR_postorder(const Expr_ptr expr)
{ walk_ctl_binary(expr); }

bool Analyzer::walk_EF_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_EF_postorder(const Expr_ptr expr)
{ walk_ctl_unary(expr); }

bool Analyzer::walk_EG_preorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_EG_postorder(const Expr_ptr expr)
{ walk_ctl_unary(expr); }

bool Analyzer::walk_EX_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_EX_postorder(const Expr_ptr expr)
{ walk_ctl_unary(expr); }

bool Analyzer::walk_EU_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_EU_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_EU_postorder(const Expr_ptr expr)
{ walk_ctl_binary(expr); }

bool Analyzer::walk_ER_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_ER_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_ER_postorder(const Expr_ptr expr)
{ walk_ctl_binary(expr); }

bool Analyzer::walk_next_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_next_postorder(const Expr_ptr expr)
{ walk_unary_boolean(expr); }

bool Analyzer::walk_neg_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_neg_postorder(const Expr_ptr expr)
{ walk_unary_algebraic(expr); }

bool Analyzer::walk_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_not_postorder(const Expr_ptr expr)
{ walk_unary_boolean(expr); }

bool Analyzer::walk_add_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_add_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_add_postorder(const Expr_ptr expr)
{ walk_binary_algebraic(expr); }

bool Analyzer::walk_sub_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_sub_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_sub_postorder(const Expr_ptr expr)
{ walk_binary_algebraic(expr); }

bool Analyzer::walk_div_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_div_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_div_postorder(const Expr_ptr expr)
{ walk_binary_algebraic(expr); }

bool Analyzer::walk_mul_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_mul_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_mul_postorder(const Expr_ptr expr)
{ walk_binary_algebraic(expr); }

bool Analyzer::walk_mod_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_mod_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_mod_postorder(const Expr_ptr expr)
{ walk_binary_algebraic(expr); }

bool Analyzer::walk_and_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_and_postorder(const Expr_ptr expr)
{ walk_binary_boolean(expr); }

bool Analyzer::walk_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_or_postorder(const Expr_ptr expr)
{ walk_binary_boolean(expr); }

bool Analyzer::walk_xor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_xor_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_xor_postorder(const Expr_ptr expr)
{ walk_binary_boolean(expr); }

bool Analyzer::walk_xnor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_xnor_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_xnor_postorder(const Expr_ptr expr)
{ walk_binary_boolean(expr); }

bool Analyzer::walk_implies_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_implies_postorder(const Expr_ptr expr)
{ walk_binary_boolean(expr); }

bool Analyzer::walk_iff_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_iff_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_iff_postorder(const Expr_ptr expr)
{ walk_binary_boolean(expr); }

bool Analyzer::walk_lshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_lshift_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_lshift_postorder(const Expr_ptr expr)
{ walk_binary_algebraic(expr); }

bool Analyzer::walk_rshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_rshift_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_rshift_postorder(const Expr_ptr expr)
{ walk_binary_algebraic(expr); }

bool Analyzer::walk_eq_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_eq_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_eq_postorder(const Expr_ptr expr)
{ walk_binary_relational(expr); }

bool Analyzer::walk_ne_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_ne_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_ne_postorder(const Expr_ptr expr)
{ walk_binary_relational(expr); }

bool Analyzer::walk_gt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_gt_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_gt_postorder(const Expr_ptr expr)
{ walk_binary_relational(expr); }

bool Analyzer::walk_ge_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_ge_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_ge_postorder(const Expr_ptr expr)
{ walk_binary_relational(expr); }

bool Analyzer::walk_lt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_lt_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_lt_postorder(const Expr_ptr expr)
{ walk_binary_relational(expr); }

bool Analyzer::walk_le_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_le_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_le_postorder(const Expr_ptr expr)
{ walk_binary_relational(expr); }

bool Analyzer::walk_ite_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_ite_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_ite_postorder(const Expr_ptr expr)
{ walk_ternary_ite(expr); }

bool Analyzer::walk_cond_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_cond_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_cond_postorder(const Expr_ptr expr)
{}

// TODO....
void Analyzer::walk_dot_postorder(const Expr_ptr expr)
{
    assert(0);
    // Type_ptr rhs_type;

    // { // RHS, no checks necessary/possible
    //     const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
    //     rhs_type = top;
    // }

    // { // LHS, must be an instance (by assertion, otherwise leaf would have fail)
    //     const Type_ptr top = f_type_stack.back(); f_type_stack.pop_back();
    //     assert(f_tm.is_instance(top));
    // }

    // // propagate rhs type
    // f_type_stack.push_back(rhs_type);

    // // restore previous ctx
    // f_ctx_stack.pop_back();
}

void Analyzer::walk_leaf(const Expr_ptr expr)
{
    ExprType symb_type = expr->f_symb;
    ExprKind res = EXPR_ERROR;

    // cache miss took care of the stack already
    if (! cache_miss(expr)) return;

    // a constants is a 0-bits unsigned type
    if ((symb_type == ICONST) ||
        (symb_type == HCONST) ||
        (symb_type == OCONST)) {
        res = EXPR_ALGEBRAIC;
    }

    else if (symb_type == IDENT) {
        ISymbol_ptr symb = resolve(f_ctx_stack.back(), expr);

        assert(symb);
        const Type_ptr tp = symb->type(); // define types are already inferred (CHECKME?!?)
        assert(tp);

        if (f_tm.is_integer(tp)) {
            res = EXPR_ALGEBRAIC;
        }
        else if (f_tm.is_boolean(tp)) {
            res = EXPR_BOOLEAN;
        }
        else assert(0);
    }
    else assert(0);

    assert(res);
    f_kind_stack.push_back(res);
}

// one step of resolution returns a const or variable
ISymbol_ptr Analyzer::resolve(const Expr_ptr ctx, const Expr_ptr frag)
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

void Analyzer::walk_ltl_g(const Expr_ptr expr)
{
    const ExprKind top = f_kind_stack.back(); f_kind_stack.pop_back();
    check_ltl(expr, top);

    f_kind_stack.push_back(top == EXPR_G_ONLY_LTL ? EXPR_G_ONLY_LTL : EXPR_GENERIC_LTL);
}

void Analyzer::walk_ltl_unary(const Expr_ptr expr)
{
    const ExprKind top = f_kind_stack.back(); f_kind_stack.pop_back();
    check_ltl(expr, top);

    f_kind_stack.push_back(EXPR_GENERIC_LTL);
}

void Analyzer::walk_ltl_binary(const Expr_ptr expr)
{
    const ExprKind rhs = f_kind_stack.back(); f_kind_stack.pop_back();
    check_ltl(expr, rhs);

    const ExprKind lhs = f_kind_stack.back(); f_kind_stack.pop_back();
    check_ltl(expr, lhs);

    f_kind_stack.push_back(EXPR_GENERIC_LTL);
}

void Analyzer::walk_ctl_ag(const Expr_ptr expr)
{
    const ExprKind top = f_kind_stack.back(); f_kind_stack.pop_back();
    check_ctl(expr, top);

    f_kind_stack.push_back(top == EXPR_AG_ONLY_CTL ? EXPR_AG_ONLY_CTL : EXPR_GENERIC_CTL);
}

void Analyzer::walk_ctl_unary(const Expr_ptr expr)
{
    const ExprKind top = f_kind_stack.back(); f_kind_stack.pop_back();
    check_ctl(expr, top);

    f_kind_stack.push_back(EXPR_GENERIC_LTL);
}

void Analyzer::walk_ctl_binary(const Expr_ptr expr)
{
    const ExprKind rhs = f_kind_stack.back(); f_kind_stack.pop_back();
    check_ltl(expr, rhs);

    const ExprKind lhs = f_kind_stack.back(); f_kind_stack.pop_back();
    check_ltl(expr, lhs);

    f_kind_stack.push_back(EXPR_GENERIC_LTL);

}

void Analyzer::walk_unary_algebraic(const Expr_ptr expr)
{
    const ExprKind top = f_kind_stack.back(); f_kind_stack.pop_back();
    check_algebraic(expr, top);

    f_kind_stack.push_back(EXPR_ALGEBRAIC);
}


void Analyzer::walk_binary_algebraic(const Expr_ptr expr)
{
    const ExprKind rhs = f_kind_stack.back(); f_kind_stack.pop_back();
    check_algebraic(expr, rhs);

    const ExprKind lhs = f_kind_stack.back(); f_kind_stack.pop_back();
    check_algebraic(expr, lhs);

    f_kind_stack.push_back(EXPR_ALGEBRAIC);
}

void Analyzer::walk_binary_relational(const Expr_ptr expr)
{
    const ExprKind rhs = f_kind_stack.back(); f_kind_stack.pop_back();
    check_algebraic(expr, rhs);

    const ExprKind lhs = f_kind_stack.back(); f_kind_stack.pop_back();
    check_algebraic(expr, lhs);

    f_kind_stack.push_back(EXPR_BOOLEAN);
}

void Analyzer::walk_binary_boolean(const Expr_ptr expr)
{
    const ExprKind rhs = f_kind_stack.back(); f_kind_stack.pop_back();
    check_boolean(expr, rhs);

    const ExprKind lhs = f_kind_stack.back(); f_kind_stack.pop_back();
    check_boolean(expr, lhs);

    f_kind_stack.push_back(EXPR_BOOLEAN);
}

void Analyzer::walk_ternary_ite(const Expr_ptr expr)
{
    const ExprKind rhs = f_kind_stack.back(); f_kind_stack.pop_back();
    const ExprKind lhs = f_kind_stack.back(); f_kind_stack.pop_back();
    check_match(expr, rhs, lhs);

    const ExprKind cond = f_kind_stack.back(); f_kind_stack.pop_back();
    check_temporal(expr, cond);

    f_kind_stack.push_back(rhs);
}

// -- low level checkrs --------------------------------------------------------
void Analyzer::check_temporal(const Expr_ptr expr, ExprKind ek)
{
    if ((EXPR_BOOLEAN != ek) &&
        (EXPR_GENERIC_CTL != ek) &&
        (EXPR_GENERIC_LTL != ek) &&
        (EXPR_AG_ONLY_CTL != ek) &&
        (EXPR_G_ONLY_LTL != ek)) {
        throw BadExpressionKindException(ek, expr, f_temporal);
    }
}

void Analyzer::check_ltl(const Expr_ptr expr, ExprKind ek)
{
    if ((EXPR_BOOLEAN != ek) &&
        (EXPR_GENERIC_LTL != ek) &&
        (EXPR_G_ONLY_LTL != ek)) {
        throw BadExpressionKindException(ek, expr, f_ltl);
    }
}

void Analyzer::check_ctl(const Expr_ptr expr, ExprKind ek)
{
    if ((EXPR_BOOLEAN != ek) &&
        (EXPR_GENERIC_CTL != ek) &&
        (EXPR_AG_ONLY_CTL != ek)) {
        throw BadExpressionKindException(ek, expr, f_ctl);
    }
}

void Analyzer::check_algebraic(const Expr_ptr expr, ExprKind ek)
{
    if ((EXPR_ALGEBRAIC != ek)) {
        throw BadExpressionKindException(ek, expr, f_algebraic);
    }
}

void Analyzer::check_boolean(const Expr_ptr expr, ExprKind ek)
{
    if ((EXPR_BOOLEAN != ek)) {
        throw BadExpressionKindException(ek, expr, f_boolean);
    }
}

void Analyzer::check_match(const Expr_ptr expr, ExprKind lhs, ExprKind rhs)
{
    if ((lhs != rhs)) {
        ExprKinds tmp;
        tmp.push_back(lhs);

        throw BadExpressionKindException(rhs, expr, tmp);
    }
}


// -- ostream utils ------------------------------------------------------------
ostream& operator<<(ostream& os, ExprKind ek)
{
    const char *tmp;
    switch (ek) {
    case EXPR_UNKNOWN: tmp = "unknown"; break;
    case EXPR_BOOLEAN: tmp = "boolean"; break;
    case EXPR_ALGEBRAIC: tmp = "algebraic"; break;
    case EXPR_G_ONLY_LTL: tmp = "G only LTL"; break;
    case EXPR_AG_ONLY_CTL: tmp = "AG only CTL"; break;
    case EXPR_GENERIC_LTL: tmp = "LTL"; break;
    case EXPR_GENERIC_CTL: tmp = "CTL"; break;
    case EXPR_ERROR: tmp = "ERROR"; break;
    default: assert(0); // unexpected
    } // of switch

    return os << tmp;
}

ostream& operator<<(ostream& os, ExprKinds& eks)
{
    ExprKinds::iterator i;

    for (i = eks.begin(); i != eks.end(); ) {
        ExprKind& tmp = (*i);
        os << tmp;

        i ++;
        if (i != eks.end()) {
            os << ", ";
        }
    }

    return os;
}
