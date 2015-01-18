/**
 *  @file expr_mgr.cc
 *  @brief Expression management. ExprMgr class
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
#include <expr_mgr.hh>

#include <stack>
#include <vector>

// singleton instance initialization
ExprMgr_ptr ExprMgr::f_instance = NULL;

ExprMgr::ExprMgr()
{
    // boolean type identifier, false and true identifiers
    bool_expr = make_identifier(BOOL_TOKEN);
    false_expr = make_identifier(FALSE_TOKEN);
    true_expr = make_identifier(TRUE_TOKEN);

    /* {constant, signed, unsigned} integer types identifiers */
    {
        std::ostringstream oss;
        oss
            << CONST_TOKEN << " "
            << INT_TOKEN;

        const_int_expr = make_identifier(oss.str());
    }
    {
        std::ostringstream oss;
        oss
            << UNSIGNED_TOKEN << " "
            << INT_TOKEN;

        unsigned_int_expr = make_identifier(oss.str());
    }
    {
        std::ostringstream oss;
        oss
            << SIGNED_TOKEN << " "
            << INT_TOKEN;

        signed_int_expr = make_identifier(oss.str());
    }
    {

    /* {constant, signed, unsigned} fixed types identifiers */
    }
    {
        std::ostringstream oss;
        oss
            << CONST_TOKEN
            << " " << FXD_TOKEN;

        const_fxd_expr = make_identifier(oss.str());
    }
    {
        std::ostringstream oss;
        oss
            << SIGNED_TOKEN << " "
            << FXD_TOKEN;

        signed_fxd_expr = make_identifier(oss.str());
    }

    array_expr = make_identifier(ARRAY_TOKEN);

    main_expr = make_identifier(MAIN_TOKEN);

    empty_expr = make_identifier(EMPTY_TOKEN);

    DEBUG
        << "ExprMgr @" << this
        << " initialized"
        << std::endl;
}

ExprMgr::~ExprMgr()
{
    DEBUG
        << "ExprMgr @" << this
        << " deinitialized"
        << std::endl;
}

Expr_ptr ExprMgr::make_enum_type(ExprSet& literals)
{
    Expr_ptr res = NULL;

    /* reverse iteration */
    for (ExprSet::reverse_iterator eye = literals.rbegin();
         eye != literals.rend(); eye ++) {
        if (!res) res = (*eye);
        else res = make_expr(COMMA, (*eye), res);
    }

    return make_set(res);
}


Expr_ptr ExprMgr::make_identifier(Atom atom)
{
    boost::mutex::scoped_lock lock(f_atom_mutex);

    AtomPoolHit ah = f_atom_pool.insert(atom);
    const Atom& pooled_atom =  (* ah.first);

#if 0
    if (ah.second) {
        DEBUG
            << "Added new atom to pool: `"
            << pooled_atom << "`"
            << std::endl;
    }
#endif

    return make_expr(pooled_atom);
}

Expr_ptr ExprMgr::__make_expr(Expr_ptr expr) {
    boost::mutex::scoped_lock lock(f_expr_mutex);

    ExprPoolHit eh = f_expr_pool.insert(*expr);
    Expr_ptr pooled_expr = const_cast<Expr_ptr> (& (*eh.first));

#if 0
    if (eh.second) {
        void *p (pooled_expr);
        DEBUG
            << "Added new expr to pool: `"
            << pooled_expr << "`, @"
            << p
            << std::endl;
    }
#endif

    return pooled_expr;
}

Expr_ptr ExprMgr::left_associate_dot(const Expr_ptr expr)
{
    Expr_ptr res (NULL);
    std::vector<Expr_ptr> fragments;

    // 1. in-order visit, build fwd expr stack
    std::stack<Expr_ptr> stack;
    stack.push( expr );

    while (0 < stack.size()) {
        Expr_ptr top (stack.top());
        stack.pop();

        if (is_dot( top)) {
            stack.push( top->rhs());
            stack.push( top->lhs());
            continue;
        }

        fragments.push_back(top);
    }

    // 2. good, now build canonical AST
    for (std::vector<Expr_ptr>::const_iterator i = fragments.begin(); fragments.end() != i; ++ i)
        res = res ? make_expr( DOT, res, *i) : *i;

    return res;
}
