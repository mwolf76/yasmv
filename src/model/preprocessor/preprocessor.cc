/**
 * @file preprocessor.cc
 * @brief Model preprocessor subsystem implementation.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#include <symb/proxy.hh>
#include <symb/classes.hh>

#include <model/preprocessor/preprocessor.hh>

Preprocessor::Preprocessor(ModelMgr& owner)
    : f_ctx_stack()
    , f_expr_stack()
    , f_env()
    , f_owner(owner)
    , f_em(ExprMgr::INSTANCE())
{
    const void *instance
        (this);

    DEBUG
        << "Created Preprocessor @"
        << instance
        << std::endl;
}

Preprocessor::~Preprocessor()
{
    const void *instance
        (this);

    DEBUG
        << "Destroying Preprocessor @"
        << instance
        << std::endl;
}

Expr_ptr Preprocessor::process(Expr_ptr expr, Expr_ptr ctx)
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

bool Preprocessor::walk_F_preorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_F_postorder(const Expr_ptr expr)
{
    POP_EXPR(lhs);
    PUSH_EXPR( f_em.make_F( lhs));
}

bool Preprocessor::walk_G_preorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_G_postorder(const Expr_ptr expr)
{
    POP_EXPR(lhs);
    PUSH_EXPR( f_em.make_G( lhs));
}

bool Preprocessor::walk_X_preorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_X_postorder(const Expr_ptr expr)
{
    POP_EXPR(lhs);
    PUSH_EXPR( f_em.make_X( lhs));
}

bool Preprocessor::walk_U_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_U_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_U_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_U( lhs, rhs ));
}

bool Preprocessor::walk_R_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_R_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_R_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_R( lhs, rhs ));
}

bool Preprocessor::walk_next_preorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_next_postorder(const Expr_ptr expr)
{
    POP_EXPR(lhs);
    PUSH_EXPR( f_em.make_next( lhs));
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

bool Preprocessor::walk_bw_not_preorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_bw_not_postorder(const Expr_ptr expr)
{
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_bw_not( lhs));
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

bool Preprocessor::walk_bw_and_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_bw_and_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_bw_and_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_bw_and( lhs, rhs ));
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

bool Preprocessor::walk_bw_or_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_bw_or_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_bw_or_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_bw_or( lhs, rhs ));
}

bool Preprocessor::walk_bw_xor_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_bw_xor_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_bw_xor_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_bw_xor( lhs, rhs ));
}

bool Preprocessor::walk_bw_xnor_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_bw_xnor_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_bw_xnor_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_bw_xnor( lhs, rhs ));
}

bool Preprocessor::walk_guard_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_guard_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_guard_postorder(const Expr_ptr expr)
{
    POP_EXPR(rhs);
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_implies( lhs, rhs )); /* rewrite guard into an implication */
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

bool Preprocessor::walk_assignment_preorder(const Expr_ptr expr)
{ return true; }
bool Preprocessor::walk_assignment_inorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_assignment_postorder(const Expr_ptr expr)
{
    ExprMgr& em
        (f_em);

    POP_EXPR(rhs);
    POP_EXPR(lhs);

    PUSH_EXPR( em.make_assignment( em.make_next(lhs),
                                   rhs ));
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
{
    assert(false); /* TODO: review this */
    // substitute_expression( expr );
    return false;
}
bool Preprocessor::walk_params_inorder(const Expr_ptr expr)
{ assert( false ); return false; }
void Preprocessor::walk_params_postorder(const Expr_ptr expr)
{ assert(false); }

bool Preprocessor::walk_params_comma_preorder(Expr_ptr expr)
{ assert(false); return false; }
bool Preprocessor::walk_params_comma_inorder(Expr_ptr expr)
{ assert(false); return false; }
void Preprocessor::walk_params_comma_postorder(Expr_ptr expr)
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

bool Preprocessor::walk_array_preorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_array_postorder(const Expr_ptr expr)
{
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_array( lhs));
}

bool Preprocessor::walk_array_comma_preorder(Expr_ptr expr)
{ assert(false); return false; }
bool Preprocessor::walk_array_comma_inorder(Expr_ptr expr)
{ assert(false); return false; }
void Preprocessor::walk_array_comma_postorder(Expr_ptr expr)
{ assert(false); }


bool Preprocessor::walk_set_preorder(const Expr_ptr expr)
{ return true; }
void Preprocessor::walk_set_postorder(const Expr_ptr expr)
{
    POP_EXPR(lhs);
    PUSH_EXPR(f_em.make_set( lhs));
}

bool Preprocessor::walk_set_comma_preorder(Expr_ptr expr)
{ assert(false); return false; }
bool Preprocessor::walk_set_comma_inorder(Expr_ptr expr)
{ assert(false); return false; }
void Preprocessor::walk_set_comma_postorder(Expr_ptr expr)
{ assert(false); }

bool Preprocessor::walk_cast_preorder(Expr_ptr expr)
{ assert(false); return false; }
bool Preprocessor::walk_cast_inorder(Expr_ptr expr)
{ assert(false); return false; }
void Preprocessor::walk_cast_postorder(Expr_ptr expr)
{ assert(false); }

bool Preprocessor::walk_type_preorder(Expr_ptr expr)
{ assert(false); return false; }
bool Preprocessor::walk_type_inorder(Expr_ptr expr)
{ assert(false); return false; }
void Preprocessor::walk_type_postorder(Expr_ptr expr)
{ assert(false); }

void Preprocessor::walk_leaf(const Expr_ptr expr)
{
    ExprMgr& em
        (f_owner.em());

    Expr_ptr expr_
        (expr);

    // is an integer const ..
    if (em.is_int_const(expr_)) {
        PUSH_EXPR(expr_);
        return;
    }

    // .. or a symbol
    if (em.is_identifier(expr_)) {

        /* traverse the env stack, subst with the first occurence, if any */
        ExprPairStack::reverse_iterator env_iter;
        for (env_iter = f_env.rbegin(); env_iter != f_env.rend(); ++ env_iter) {

            std::pair<Expr_ptr, Expr_ptr> entry
                (*env_iter);

            if (entry.first == expr_) {
                expr_ = entry.second;
                break;
            }
        }

        /* Symb resolution */
        ResolverProxy proxy;
        Symbol_ptr symb
            (proxy.symbol( em.make_dot( f_ctx_stack.back(), expr_)));

        if (symb->is_const()) {
            Expr_ptr res = symb->as_const().name();
            PUSH_EXPR(res);
            return;
        }
        else if (symb->is_literal()) {
            Expr_ptr res = symb->as_literal().name();
            PUSH_EXPR(res);
            return;
        }
        else if (symb->is_variable()) {
            Expr_ptr res = symb->as_variable().name();
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
    if (f_em.is_params_comma( expr)) {
        traverse_param_list( params, expr->lhs());
        traverse_param_list( params, expr->rhs());
    }
    else {
        params.push_back( expr);
    }
}

// void Preprocessor::substitute_expression(const Expr_ptr expr)
// {
//     ResolverProxy proxy;

//     /* LHS -> define name, extract formals for definition */
//     assert ( f_em.is_identifier( expr->lhs()));
//     Define& define
//         (proxy.symbol( f_owner.em().
//                        make_dot( f_ctx_stack.back(), expr -> lhs())) -> as_define());

//     const ExprVector& formals
//         (define.formals());

//     /* RHS -> comma separated lists of actual parameters */
//     ExprVector actuals;
//     traverse_param_list( actuals, expr -> rhs());

//     /* Populate the subst environment */
//     assert( formals.size() == actuals.size());

//     ExprVector::const_iterator ai;
//     ExprVector::const_iterator fi;
//     for (ai = actuals.begin(), fi = formals.begin();
//          ai != actuals.end(); ++ ai, ++ fi) {

//         /* actual may have been introduced by a nested define, so we
//            chain-resolve it to the outermost, real model variable,
//            actual using the nested environment stack. */
//         Expr_ptr actual
//             (*ai);

//         ExprPairStack::reverse_iterator eps_riter;
//         for ( eps_riter = f_env.rbegin(); eps_riter != f_env.rend(); ++ eps_riter ) {

//             std::pair<Expr_ptr, Expr_ptr> tmp
//                 (*eps_riter);

//             if (tmp.first == actual) {
//                 actual = tmp.second;
//             }
//         }

//         Expr_ptr formal
//             (*fi);

//         f_env.push_back( std::make_pair <Expr_ptr, Expr_ptr>
//                          ( formal, actual ));
//     }

//     /* Here comes a bit of magic: we just relaunch the preprocessor on the
//        define body, to perform the substitution :-D */
//     (*this)(define.body());

//     /* Restore previous environment */
//     for (ai = actuals.begin(); ai != actuals.end(); ++ ai ) {
//         f_env.pop_back();
//     }
// }
