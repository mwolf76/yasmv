/**
 *  @file preprocessor/internals.cc
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
#include <symb/proxy.hh>

#include <model/preprocessor/preprocessor.hh>

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
    Define& define = proxy.symbol(f_ctx_stack.back(), expr -> lhs()) -> as_define();
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
            std::pair<Expr_ptr, Expr_ptr> tmp (*eps_riter);
            if (tmp.first == actual) {
                actual = tmp.second;
            }
        }

        Expr_ptr formal = (*fi);
        f_env.push_back( std::make_pair <Expr_ptr, Expr_ptr>
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
