/**
 *  @file fqexpr.cc, Fully Qualified Expression (FQEXpr)
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

#include <fqexpr.hh>
#include <expr_mgr.hh>

FQExpr::FQExpr(Expr_ptr expr)
    : f_ctx(ExprMgr::INSTANCE().make_main())
    , f_expr(expr)
    , f_time(0)
{}

FQExpr::FQExpr(Expr_ptr ctx, Expr_ptr expr, step_t time)
    : f_ctx(ctx)
    , f_expr(expr)
    , f_time(time)
{}

FQExpr::FQExpr(const FQExpr& fqexpr)
    : f_ctx(fqexpr.ctx())
    , f_expr(fqexpr.expr())
    , f_time(fqexpr.time())
{}

bool FQExpr::operator==(const FQExpr& other) const
{
    return
        this->f_ctx == other.ctx() &&
        this->f_expr == other.expr() &&
        this->f_time == other.time();
}

unsigned long FQExpr::hash() const
{
    return 0; // TODO
}
