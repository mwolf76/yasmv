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

    // {constant, signed, unsigned} integer types identifiers
    {
        ostringstream oss; oss << CONST_TOKEN << " " << INT_TOKEN;
        const_int_expr = make_identifier(oss.str());
    }
    {
        ostringstream oss; oss << UNSIGNED_TOKEN << " " << INT_TOKEN;
        unsigned_int_expr = make_identifier(oss.str());
    }
    {
        ostringstream oss; oss << SIGNED_TOKEN << " " << INT_TOKEN;
        signed_int_expr = make_identifier(oss.str());
    }
    {
        ostringstream oss; oss << UNSIGNED_TOKEN << " " << FXD_TOKEN;
        unsigned_fxd_expr = make_identifier(oss.str());
    }
    {
        ostringstream oss; oss << SIGNED_TOKEN << " " << FXD_TOKEN;
        signed_fxd_expr = make_identifier(oss.str());
    }

    array_expr = make_identifier(ARRAY_TOKEN);
    main_expr = make_identifier(MAIN_TOKEN);

    default_ctx_expr = main_expr; // make_identifier(DEFAULT_CTX_TOKEN);

    // arithmetical ops
    f_s2e.insert( make_pair < string, ExprType > ( "neg", NEG ));
    f_s2e.insert( make_pair < string, ExprType > ( "add", PLUS ));
    f_s2e.insert( make_pair < string, ExprType > ( "sub", SUB ));
    f_s2e.insert( make_pair < string, ExprType > ( "div", DIV ));
    f_s2e.insert( make_pair < string, ExprType > ( "mod", MOD ));
    f_s2e.insert( make_pair < string, ExprType > ( "mul", MUL ));

    // bitwise ops
    f_s2e.insert( make_pair < string, ExprType > ( "not", NOT ));
    f_s2e.insert( make_pair < string, ExprType > ( "or", OR ));
    f_s2e.insert( make_pair < string, ExprType > ( "and", AND ));
    f_s2e.insert( make_pair < string, ExprType > ( "xor", XOR ));
    f_s2e.insert( make_pair < string, ExprType > ( "xnor", XNOR ));
    f_s2e.insert( make_pair < string, ExprType > ( "implies", IMPLIES ));

    // relational ops
    f_s2e.insert( make_pair < string, ExprType > ( "eq", EQ ));
    f_s2e.insert( make_pair < string, ExprType > ( "ne", NE ));
    f_s2e.insert( make_pair < string, ExprType > ( "gt", GT ));
    f_s2e.insert( make_pair < string, ExprType > ( "ge", GE ));
    f_s2e.insert( make_pair < string, ExprType > ( "lt", LT ));
    f_s2e.insert( make_pair < string, ExprType > ( "le", LE ));

    DEBUG << "ExprMgr @" << this << " initialized" << endl;
}

ExprMgr::~ExprMgr()
{
    DEBUG << "ExprMgr @" << this << " deinitialized" << endl;
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

ExprType ExprMgr::exprTypeFromString (string exprTypeString )
{
    exprTypeFromStringMap::const_iterator i = f_s2e.find( exprTypeString );
    assert (i != f_s2e.end());

    return (*i).second;
}

