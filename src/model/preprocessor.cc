/**
 *  @file preprocessor.cc
 *  @brief Expr preprocessor
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
 *  This module contains definitions and services that implement a
 *  type inference engine. The type inference engine is implemented
 *  using a simple walker pattern: (a) on preorder, return true if the
 *  node has not yet been visited; (b) always do in-order (for binary
 *  nodes); (c) perform proper type checking in post-order
 *  hooks. Implicit conversion rules are designed to follow as closely
 *  as possible section 6.3.1 of iso/iec 9899:1999 (aka C99)
 *  standard. Type rules are implemented in the result_type methods of
 *  the TypeMgr class.
 *
 **/

#include <common.hh>

#include <expr.hh>
#include <preprocessor.hh>

#include <model_mgr.hh>

#include <proxy.hh>

// uncommment following line to enable post_node_hook debug (verbose!)
// #define DEBUG_PREPROCESSOR

Preprocessor::Preprocessor(ModelMgr& owner)
    : f_ctx_stack()
    , f_expr_stack()
    , f_env()
    , f_owner(owner)
    , f_em(ExprMgr::INSTANCE())
{
    DEBUG << "Created Preprocessor @" << this << endl;
}

Preprocessor::~Preprocessor()
{ DEBUG << "Destroying Preprocessor @" << this << endl; }

Expr_ptr Preprocessor::process(Expr_ptr ctx, Expr_ptr expr)
{
    // remove previous results
    f_ctx_stack.clear();
    f_expr_stack.clear();

    // clear the environment
    f_env.clear();

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);

    // invoke walker on the body of the expr to be processed
    (*this)(expr);

    assert(1 == f_expr_stack.size());

    POP_EXPR(res);
    assert(NULL != res);

    return res;
}

void Preprocessor::pre_hook()
{}
void Preprocessor::post_hook()
{}

void Preprocessor::pre_node_hook(Expr_ptr expr)
{}

void Preprocessor::post_node_hook(Expr_ptr expr)
{}

bool Preprocessor::walk_next_preorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_next_postorder(const Expr_ptr expr)
{
    POP_EXPR(lhs);
    PUSH_EXPR( f_em.make_next( lhs));
}

bool Preprocessor::walk_prev_preorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_prev_postorder(const Expr_ptr expr)
{
    POP_EXPR(lhs);
    PUSH_EXPR( f_em.make_prev( lhs));
}

bool Preprocessor::walk_neg_preorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_neg_postorder(const Expr_ptr expr)
{
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_neg( lhs));
}

bool Preprocessor::walk_not_preorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_not_postorder(const Expr_ptr expr)
{
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_not( lhs));
}

bool Preprocessor::walk_add_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_add_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_add_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_add( lhs, rhs ));
}

bool Preprocessor::walk_sub_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_sub_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_sub_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_sub( lhs, rhs ));
}

bool Preprocessor::walk_div_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_div_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_div_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_div( lhs, rhs ));
}

bool Preprocessor::walk_mul_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_mul_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_mul_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_mul( lhs, rhs ));
}

bool Preprocessor::walk_mod_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_mod_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_mod_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_mod( lhs, rhs ));
}

bool Preprocessor::walk_and_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_and_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_and( lhs, rhs ));
}

bool Preprocessor::walk_or_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_or_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_or( lhs, rhs ));
}

bool Preprocessor::walk_xor_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_xor_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_xor_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_xor( lhs, rhs ));
}

bool Preprocessor::walk_xnor_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_xnor_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_xnor_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_xnor( lhs, rhs ));
}

bool Preprocessor::walk_implies_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_implies_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_implies( lhs, rhs ));
}

bool Preprocessor::walk_iff_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_iff_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_iff_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_iff( lhs, rhs ));
}

bool Preprocessor::walk_lshift_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_lshift_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_lshift_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_lshift( lhs, rhs ));
}

bool Preprocessor::walk_rshift_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_rshift_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_rshift_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_rshift( lhs, rhs ));
}

bool Preprocessor::walk_eq_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_eq_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_eq_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_eq( lhs, rhs ));
}

bool Preprocessor::walk_ne_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_ne_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_ne_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_ne( lhs, rhs ));
}

bool Preprocessor::walk_gt_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_gt_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_gt_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_gt( lhs, rhs ));
}

bool Preprocessor::walk_ge_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_ge_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_ge_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_ge( lhs, rhs ));
}

bool Preprocessor::walk_lt_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_lt_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_lt_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_lt( lhs, rhs ));
}

bool Preprocessor::walk_le_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_le_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_le_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_le( lhs, rhs ));
}

bool Preprocessor::walk_ite_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_ite_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_ite_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    POP_EXPR(cond);
    PUSH_EXPR(f_em.make_ite( f_em.make_cond( cond,
                                             lhs),
                             rhs ));
}

bool Preprocessor::walk_cond_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_cond_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_cond_postorder(const Expr_ptr expr)
{}

bool Preprocessor::walk_dot_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_dot_inorder(const Expr_ptr expr)
{
    assert( false ); // FIXME
    return false;
}
void Preprocessor::walk_dot_postorder(const Expr_ptr expr)
{
    assert( false );
}

/* main entry-point */
bool Preprocessor::walk_params_preorder(const Expr_ptr expr)
{ substitute_expression( expr ); return false; }
bool Preprocessor::walk_params_inorder(const Expr_ptr expr)
{ assert( false ); return false; }
void Preprocessor::walk_params_postorder(const Expr_ptr expr)
{ assert(false); }

bool Preprocessor::walk_subscript_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_subscript_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_subscript_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_subscript( lhs, rhs ));
}

bool Preprocessor::walk_set_preorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_set_postorder(const Expr_ptr expr)
{
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_set( lhs));
}

bool Preprocessor::walk_comma_preorder(Expr_ptr expr)
{ assert(false); return false; }
bool Preprocessor::walk_comma_inorder(Expr_ptr expr)
{ assert(false); return false; }
void Preprocessor::walk_comma_postorder(Expr_ptr expr)
{ assert(false); }

bool Preprocessor::walk_cast_preorder(Expr_ptr expr)
{ assert(false); return false; }
bool Preprocessor::walk_cast_inorder(Expr_ptr expr)
{ assert(false); return false; }
void Preprocessor::walk_cast_postorder(Expr_ptr expr)
{ assert(false); }


void Preprocessor::walk_leaf(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr expr_ = expr;

    // is an integer const ..
    if (em.is_numeric(expr_)) {
        PUSH_EXPR(expr_);
        return;
    }

    // .. or a symbol
    if (em.is_identifier(expr_)) {

        /* traverse the env stack, subst with the first occurence, if any */
        ExprPairStack::reverse_iterator env_iter;
        for (env_iter = f_env.rbegin(); env_iter != f_env.rend(); ++ env_iter) {
            pair<Expr_ptr, Expr_ptr> entry = (*env_iter);

            if (entry.first == expr_) {
                expr_ = entry.second;
                break;
            }
        }

        /* Symb resolution */
        ResolverProxy proxy;
        ISymbol_ptr symb = proxy.symbol(f_ctx_stack.back(), expr_);

        if (symb->is_const()) {
            Expr_ptr res = symb->as_const().expr();
            PUSH_EXPR(res);
            return;
        }
        else if (symb->is_literal()) {
            Expr_ptr res = symb->as_literal().expr();
            PUSH_EXPR(res);
            return;
        }
        else if (symb->is_enum()) {
            Expr_ptr res = symb->as_enum().expr();
            PUSH_EXPR(res);
            return;
        }
        else if (symb->is_variable()) {
            Expr_ptr res = symb->as_variable().expr();
            PUSH_EXPR(res);
            return;
        }
        else if (symb->is_define()) {
            assert( false );
        }
    }

    assert(false); // unexpected
}

void Preprocessor::traverse_param_list(ExprVector& params, const Expr_ptr expr)
{
    if (f_em.is_comma( expr)) {
        traverse_param_list( params, expr->lhs());
        traverse_param_list( params, expr->rhs());
    }
    else {
        params.push_back( expr);
    }
}

void Preprocessor::substitute_expression(const Expr_ptr expr)
{
    ResolverProxy proxy;

    /* LHS -> define name, extract formals for definition */
    assert ( f_em.is_identifier( expr->lhs()));
    IDefine& define = proxy.symbol(f_ctx_stack.back(), expr -> lhs()) -> as_define();
    const ExprVector& formals = define.formals();

    /* RHS -> comma separated lists of actual parameters */
    ExprVector actuals; traverse_param_list( actuals, expr -> rhs());

    /* Populate the subst environment */
    assert( formals.size() == actuals.size());

    ExprVector::const_iterator ai;
    ExprVector::const_iterator fi;
    for (ai = actuals.begin(), fi = formals.begin();
         ai != actuals.end(); ++ ai, ++ fi) {

        /* actual may have been introduced by a nested define, so we
           chain-resolve it to the outermost, real model variable,
           actual using the nested environment stack. */
        Expr_ptr actual = (*ai);
        ExprPairStack::reverse_iterator eps_riter;
        for ( eps_riter = f_env.rbegin(); eps_riter != f_env.rend(); ++ eps_riter ) {
            pair<Expr_ptr, Expr_ptr> tmp (*eps_riter);
            if (tmp.first == actual) {
                actual = tmp.second;
            }
        }

        Expr_ptr formal = (*fi);
        f_env.push_back( make_pair <Expr_ptr, Expr_ptr>
                         ( formal, actual ));
    }

    /* Here comes a bit of magic: we just relaunch the preprocessor on the
       define body, to perform the substitution :-D */
    (*this)(define.body());

    /* Restore previous environment */
    for (ai = actuals.begin(); ai != actuals.end(); ++ ai ) {
        f_env.pop_back();
    }
}
