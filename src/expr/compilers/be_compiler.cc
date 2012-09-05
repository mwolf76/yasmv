/**
 *  @file be_compiler.cc
 *  @brief Expr compilers
 *
 *  This module contains definitions and services that implement the
 *  booolean expressions compilation into a form which is suitable for
 *  the SAT analysis. Current implementation uses ADDs to perform
 *  expression manipulation and booleanization. Expressions are
 *  assumed to be type-safe, only boolean expressions on arithmetic
 *  predicates are supported. The final result of expression
 *  compilation must be a 0-1 ADD which is suitable for CNF clauses
 *  injection directly into the SAT solver. The compilation engine is
 *  implemented using a simple walker pattern: (a) on preorder, return
 *  true if the node has not yet been visited; (b) always do in-order
 *  (for binary nodes); (c) perform proper compilation in post-order
 *  hooks.
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
#include <be_compiler.hh>

BECompiler::BECompiler()
    : f_map()
    , f_add_stack()
    , f_ctx_stack()
    , f_mm(ModelMgr::INSTANCE())
    , f_em(ExprMgr::INSTANCE())
    , f_cudd(* new Cudd())
{ TRACE << "Created BECompiler @" << this << endl; }

BECompiler::~BECompiler()
{ TRACE << "Destroying BECompiler @" << this << endl; }

ADD BECompiler::process(Expr_ptr ctx, Expr_ptr body)
{
    DEBUG << "Compiling boolean expression " << ctx << "::" << body << endl;

    // remove previous results
    f_add_stack.clear();
    f_ctx_stack.clear();

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);

    // invoke walker on the body of the expr to be processed
    (*this)(body);

    assert(1 == f_add_stack.size());
    return f_add_stack.back();
}

void BECompiler::pre_hook()
{}
void BECompiler::post_hook()
{}

bool BECompiler::walk_F_preorder(const Expr_ptr expr)
{ assert(0); return false; }
void BECompiler::walk_F_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_G_preorder(const Expr_ptr expr)
{ assert(0); return false; }
void BECompiler::walk_G_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_X_preorder(const Expr_ptr expr)
{ assert(0); return false; }
void BECompiler::walk_X_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_U_preorder(const Expr_ptr expr)
{ assert(0); return false; }
bool BECompiler::walk_U_inorder(const Expr_ptr expr)
{ assert(0); return false; }
void BECompiler::walk_U_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_R_preorder(const Expr_ptr expr)
{ assert(0); return false; }
bool BECompiler::walk_R_inorder(const Expr_ptr expr)
{ assert(0); return false; }
void BECompiler::walk_R_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_AF_preorder(const Expr_ptr expr)
{ assert(0); return false; }
void BECompiler::walk_AF_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_AG_preorder(const Expr_ptr expr)
{ assert(0); return false; }
void BECompiler::walk_AG_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_AX_preorder(const Expr_ptr expr)
{ assert(0); return false; }
void BECompiler::walk_AX_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_AU_preorder(const Expr_ptr expr)
{ assert(0); return false; }
bool BECompiler::walk_AU_inorder(const Expr_ptr expr)
{ assert(0); return false; }
void BECompiler::walk_AU_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_AR_preorder(const Expr_ptr expr)
{ assert(0); return false; }
bool BECompiler::walk_AR_inorder(const Expr_ptr expr)
{ assert(0); return false; }
void BECompiler::walk_AR_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_EF_preorder(const Expr_ptr expr)
{ assert(0); return false; }
void BECompiler::walk_EF_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_EG_preorder(const Expr_ptr expr)
{ assert(0); return false; }
void BECompiler::walk_EG_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_EX_preorder(const Expr_ptr expr)
{ assert(0); return false; }
void BECompiler::walk_EX_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_EU_preorder(const Expr_ptr expr)
{ assert(0); return false; }
bool BECompiler::walk_EU_inorder(const Expr_ptr expr)
{ assert(0); return false; }
void BECompiler::walk_EU_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_ER_preorder(const Expr_ptr expr)
{ assert(0); return false; }
bool BECompiler::walk_ER_inorder(const Expr_ptr expr)
{ assert(0); return false; }
void BECompiler::walk_ER_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_init_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void BECompiler::walk_init_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_next_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void BECompiler::walk_next_postorder(const Expr_ptr expr)
{ assert(0); }

bool BECompiler::walk_neg_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void BECompiler::walk_neg_postorder(const Expr_ptr expr)
{
    const ADD top = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(- top);
}

bool BECompiler::walk_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void BECompiler::walk_not_postorder(const Expr_ptr expr)
{
    const ADD top = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(~ top);
}

bool BECompiler::walk_add_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_add_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_add_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs + rhs);
}

bool BECompiler::walk_sub_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_sub_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_sub_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs - rhs);
}

bool BECompiler::walk_div_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_div_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_div_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs / rhs);
}

bool BECompiler::walk_mul_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_mul_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_mul_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs * rhs);
}

bool BECompiler::walk_mod_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_mod_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_mod_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs / rhs);
}

bool BECompiler::walk_and_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_and_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs & rhs);
}

bool BECompiler::walk_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_or_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs | rhs);
}

bool BECompiler::walk_xor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_xor_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_xor_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs.Xor(rhs));
}

bool BECompiler::walk_xnor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_xnor_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_xnor_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs.Xnor(rhs));
}

bool BECompiler::walk_implies_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_implies_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    // TODO: REVIEW ME
    // f_add_stack.push_back(!lhs || rhs);
}

bool BECompiler::walk_iff_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_iff_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_iff_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs.Xnor(rhs));
}

bool BECompiler::walk_lshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_lshift_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_lshift_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs.LShift(rhs));
}

bool BECompiler::walk_rshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_rshift_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_rshift_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs.RShift(rhs));
}

bool BECompiler::walk_eq_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_eq_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_eq_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back((lhs == rhs)
                          ? f_cudd.addOne()
                          : f_cudd.addZero());
}

bool BECompiler::walk_ne_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_ne_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_ne_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back((lhs == rhs)
                          ? f_cudd.addZero()
                          : f_cudd.addOne());
}

bool BECompiler::walk_gt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_gt_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_gt_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back((lhs > rhs)
                          ? f_cudd.addOne()
                          : f_cudd.addZero());
}

bool BECompiler::walk_ge_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_ge_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_ge_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back((lhs >= rhs)
                          ? f_cudd.addOne()
                          : f_cudd.addZero());
}

bool BECompiler::walk_lt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_lt_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_lt_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back((lhs < rhs)
                          ? f_cudd.addOne()
                          : f_cudd.addZero());
}

bool BECompiler::walk_le_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_le_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_le_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back((lhs <= rhs)
                          ? f_cudd.addOne()
                          : f_cudd.addZero());
}

bool BECompiler::walk_ite_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_ite_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_ite_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back((lhs <= rhs)
                          ? f_cudd.addOne()
                          : f_cudd.addZero());
 }

bool BECompiler::walk_cond_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_cond_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_cond_postorder(const Expr_ptr expr)
{
    const ADD c = f_add_stack.back(); f_add_stack.pop_back();
    const ADD t = f_add_stack.back(); f_add_stack.pop_back();
    const ADD e = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(c.Ite(t, e));
}

bool BECompiler::walk_set_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void BECompiler::walk_set_postorder(const Expr_ptr expr)
{}

bool BECompiler::walk_comma_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_comma_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_comma_postorder(const Expr_ptr expr)
{}

bool BECompiler::walk_member_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_member_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_member_postorder(const Expr_ptr expr)
{
    // tODO: member
}

bool BECompiler::walk_union_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_union_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_union_postorder(const Expr_ptr expr)
{
    // todo: union
}

bool BECompiler::walk_dot_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_dot_inorder(const Expr_ptr expr)
{
    // ADD tmp = f_add_stack.back();
    // Expr_ptr ctx = tmp->get_repr();
    // f_ctx_stack.push_back(ctx);
    return true;
}
// TODO: later
void BECompiler::walk_dot_postorder(const Expr_ptr expr)
{
    // ADD rhs_add;

    // { // RHS, no checks necessary/possible
    //     const ADD top = f_add_stack.back(); f_add_stack.pop_back();
    //     rhs_add = top;
    // }

    // { // LHS, must be an instance (by assertion, otherwise leaf would have fail)
    //     const ADD top = f_add_stack.back(); f_add_stack.pop_back();
    //     assert(f_tm.is_instance(top));
    // }

    // // propagate rhs add
    // f_add_stack.push_back(rhs_add);

    // // restore previous ctx
    // f_ctx_stack.pop_back();
}

void BECompiler::walk_leaf(const Expr_ptr expr)
{
    ExprType symb_type = expr->f_symb;
    ADD add;

    // cache miss took care of the stack already
    if (! cache_miss(expr)) return;

    if ((symb_type == ICONST)  ||
        (symb_type == UWCONST) ||
        (symb_type == SWCONST)) {
        add = f_cudd.constant(expr->u.f_value);
    }
    else if (symb_type == IDENT) {
        ISymbol_ptr symb = resolve(f_ctx_stack.back(), expr);
        add = symb->as_variable().encoding();
    }
    else assert(0);

    f_add_stack.push_back(add);
}

// one step of resolution returns a const or variable
ISymbol_ptr BECompiler::resolve(const Expr_ptr ctx, const Expr_ptr frag)
{
    Model& model = static_cast <Model&> (*f_mm.get_model());
    ISymbol_ptr symb = model.fetch_symbol(FQExpr(ctx, frag));

    // is this a variable?
    if (symb->is_variable()) {
        return symb;
    }

    // ... or a define?
    else if (symb->is_define()) {

        while (symb->is_define()) {
            Expr_ptr body = symb->as_define().body();
            if (!f_em.is_identifier(body)) {
                // throw BadDefine(); // TODO
            }
            symb = model.fetch_symbol(FQExpr(ctx, body));
        }

        return symb;
    }

    // .. or a constant?
    else if (symb->is_const()) {
        return symb;
    }

    // or what?!?
    else assert(0);
}
