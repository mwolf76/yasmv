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
    , f_enc(EncodingMgr::INSTANCE())
{ TRACE << "Created BECompiler @" << this << endl; }

BECompiler::~BECompiler()
{ TRACE << "Destroying BECompiler @" << this << endl; }

ADD BECompiler::process(Expr_ptr ctx, Expr_ptr body, step_t time = 0)
{
    DEBUG << "Compiling boolean expression (time = " << time
          << ") " << ctx << "::" << body
          << endl;

    // remove previous results
    f_add_stack.clear();
    f_ctx_stack.clear();

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);
    f_time_stack.push_back(time);

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
{
    f_time_stack.push_back(0);
    return true;
}
void BECompiler::walk_init_postorder(const Expr_ptr expr)
{
    f_time_stack.pop_back(); // reset time stack
}

bool BECompiler::walk_next_preorder(const Expr_ptr expr)
{
    step_t curr_time = f_time_stack.back();
    f_time_stack.push_back(1 + curr_time);
    return true;
}
void BECompiler::walk_next_postorder(const Expr_ptr expr)
{
    f_time_stack.pop_back(); // reset time stack
}

bool BECompiler::walk_at_preorder(const Expr_ptr expr)
{ return true; }
bool BECompiler::walk_at_inorder(const Expr_ptr expr)
{
    ADD tmp = f_add_stack.back();
    assert(Cudd_IsConstant(tmp));

    /* watch out, this can be dangerous */
    step_t curr_time = Cudd_V(tmp);
    f_time_stack.push_back(1 + curr_time);

    return true;
}
void BECompiler::walk_at_postorder(const Expr_ptr expr)
{
    f_time_stack.pop_back(); // reset time stack
}

bool BECompiler::walk_neg_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void BECompiler::walk_neg_postorder(const Expr_ptr expr)
{
    const ADD top = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(top.Negate());
}

bool BECompiler::walk_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void BECompiler::walk_not_postorder(const Expr_ptr expr)
{
    const ADD top = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(top.Cmpl());
}

bool BECompiler::walk_add_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_add_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_add_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs.Plus(rhs));
}

bool BECompiler::walk_sub_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_sub_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_sub_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs.Minus(rhs));
}

bool BECompiler::walk_div_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_div_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_div_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs.Divide(rhs));
}

bool BECompiler::walk_mul_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_mul_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_mul_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs.Times(rhs));
}

bool BECompiler::walk_mod_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_mod_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_mod_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs.Modulus(rhs));
}

bool BECompiler::walk_and_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_and_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs.Times(rhs)); /* 0, 1 logic uses arithmetic product */
}

bool BECompiler::walk_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_or_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs.Or(rhs));
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
    f_add_stack.push_back(lhs.Cmpl().Or(rhs));
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
                          ? f_enc.one()
                          : f_enc.zero());
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
                          ? f_enc.zero()
                          : f_enc.one());
}

bool BECompiler::walk_gt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_gt_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_gt_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(rhs.Lt(lhs)
                          ? f_enc.one()
                          : f_enc.zero());
}

bool BECompiler::walk_ge_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_ge_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_ge_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(rhs.Leq(lhs)
                          ? f_enc.one()
                          : f_enc.zero());
}

bool BECompiler::walk_lt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_lt_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_lt_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs.Lt(rhs)
                          ? f_enc.one()
                          : f_enc.zero());
}

bool BECompiler::walk_le_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_le_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_le_postorder(const Expr_ptr expr)
{
    const ADD rhs = f_add_stack.back(); f_add_stack.pop_back();
    const ADD lhs = f_add_stack.back(); f_add_stack.pop_back();
    f_add_stack.push_back(lhs.Leq(rhs)
                          ? f_enc.one()
                          : f_enc.zero());
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
                          ? f_enc.one()
                          : f_enc.zero());
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
{ assert(0); /* unsupported */ }

bool BECompiler::walk_comma_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_comma_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_comma_postorder(const Expr_ptr expr)
{ assert(0); /* unsupported */ }

bool BECompiler::walk_member_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_member_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_member_postorder(const Expr_ptr expr)
{ assert(0); /* unsupported */ }

bool BECompiler::walk_union_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_union_inorder(const Expr_ptr expr)
{ return true; }
void BECompiler::walk_union_postorder(const Expr_ptr expr)
{ assert(0); /* unsupported */ }

bool BECompiler::walk_dot_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool BECompiler::walk_dot_inorder(const Expr_ptr expr)
{
    // ADD tmp = f_add_stack.back();
    // Expr_ptr ctx = tmp->get_repr();
    // f_ctx_stack.push_back(ctx);
    return true;
}
void BECompiler::walk_dot_postorder(const Expr_ptr expr)
{
    ADD rhs_add;

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
    /* cached? */
    if (! cache_miss(expr)) return;

    // symb resolution
    Model& model = static_cast <Model&> (*f_mm.model());
    ISymbol_ptr symb = model.fetch_symbol(FQExpr(f_ctx_stack.back(), expr));

    // 0. bool/integer constant leaves
    if (symb->is_const()) {
        IConstant& konst = symb->as_const();

        if (konst.is_false()) {
            f_add_stack.push_back(f_enc.zero());
        }
        else if (konst.is_true()) {
            f_add_stack.push_back(f_enc.one());
        }
        else {
            f_add_stack.push_back(f_enc.constant(konst.value()));
        }
    }

    assert (symb->is_variable() ||
            symb->is_define());

    if (symb->is_variable()) {

        // if encoding for variable is available reuse its ADD...
        ENCMap::iterator eye = f_encodings.find(symb);
        if (eye != f_encodings.end()) {
            IEncoding_ptr enc = (*eye).second;
            f_add_stack.push_back(enc->add());
        }

        // otherwise: (1) create it,
        Type_ptr type = symb->as_variable().type();
        IEncoding_ptr enc = f_enc.make_encoding(type);

        // (2) cache it,
        register_encoding(symb, enc);

        // (3) return it.
        f_add_stack.push_back(enc->add());
    }

    // ... or a define? (re-entrant invocation)
    else if (symb->is_define()) {
        Expr_ptr body = NULL;
        while (symb->is_define()) {
            body = symb->as_define().body();
            symb = model.fetch_symbol(FQExpr(f_ctx_stack.back(), body));
        }

        // walk body in given ctx
        // f_ctx_stack.push_back(ctx); FIXME

        // invoke walker on the body of the expr to be processed
        (*this)(body);
    }

    // or what?!?
    else assert(0);
}
