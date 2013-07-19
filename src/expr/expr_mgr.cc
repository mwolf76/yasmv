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

// singleton instance initialization
ExprMgr_ptr ExprMgr::f_instance = NULL;

ExprMgr::ExprMgr()
{
    // boolean type identifier, false and true identifiers
    bool_expr = make_identifier(BOOL_TOKEN);
    false_expr = make_identifier(FALSE_TOKEN);
    true_expr = make_identifier(TRUE_TOKEN);

    // integer types identifiers
    {
        ostringstream oss; oss << UNSIGNED_TOKEN << " " << INT_TOKEN;
        unsigned_int_expr = make_identifier(oss.str());
    }
    {
        ostringstream oss; oss << SIGNED_TOKEN << " " << INT_TOKEN;
        signed_int_expr = make_identifier(oss.str());
    }
    int_expr = make_identifier(INT_TOKEN);

    main_expr = make_identifier(MAIN_TOKEN);
    set_expr = make_identifier(SET_TOKEN);
    range_expr = make_identifier(RANGE_TOKEN);
    array_expr = make_identifier (ARRAY_TOKEN);

    DEBUG << "ExprMgr @" << this << " initialized" << endl;
}

ExprMgr::~ExprMgr()
{
    DEBUG << "ExprMgr @" << this << " deinitialized" << endl;
}

Expr_ptr ExprMgr::make_set_type(ExprSet& literals)
{
    Expr_ptr res = NULL;

    /* reverse iteration */
    for (ExprSet::reverse_iterator eye = literals.rbegin();
         eye != literals.rend(); eye ++) {
        if (!res) res = (*eye);
        else res = make_expr(COMMA, (*eye), res);
    }

    return make_expr(SET, res, NULL);
}

value_t ExprMgr::pow2(unsigned exp)
{
    value_t res = 1;
    for (unsigned i = exp; i; -- i) {
        res *= 2;
    }
    return res;
}
