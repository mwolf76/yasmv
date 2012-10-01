/**
 *  @file expr.cc
 *  @brief Expression management
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

#include <expr.hh>
#include <types.hh>

// static initialization
ExprMgr* ExprMgr::f_instance = NULL;
// const Expr& ExprMgr::nil = Expr();

// get rid of this Goddammit!!!
void link_expr()
{}

bool EnumType::has_symbs() const
{
    bool res = false;
    ExprMgr& em = ExprMgr::INSTANCE();

    for (ExprSet::iterator eye = f_literals.begin();
         (!res) && (eye != f_literals.end()); eye ++) {

        res |= em.is_identifier(*eye);
    }

    return res;
}

bool EnumType::has_numbers() const
{
    bool res = false;
    ExprMgr& em = ExprMgr::INSTANCE();

    for (ExprSet::iterator eye = f_literals.begin();
         (!res) && (eye != f_literals.end()); eye ++) {

        res |= em.is_numeric(*eye);
    }

    return res;
}

ExprMgr::ExprMgr()
{
    // boolean type identifier, false and true identifiers
    bool_expr = make_identifier(BOOL_TOKEN);
    false_expr = make_identifier(FALSE_TOKEN);
    true_expr = make_identifier(TRUE_TOKEN);

    // unsigned and signed base integer types identifiers
    unsigned_expr = make_identifier(UNSIGNED_TOKEN);
    signed_expr = make_identifier(SIGNED_TOKEN);

    integer_expr = make_identifier(INTEGER_TOKEN); // abstract

    // temporal type identifier
    temporal_expr = make_identifier(TEMPORAL_TOKEN);

    // main module identifier
    main_expr = make_identifier(MAIN_TOKEN);

    DEBUG << "ExprMgr @" << this << " initialized" << endl;
}

ExprMgr::~ExprMgr()
{
    DEBUG << "ExprMgr @" << this << " deinitialized" << endl;
}
