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
#include <expr_mgr.hh>
#include <expr_printer.hh>

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

UCBI::UCBI(Expr_ptr ctx, Expr_ptr expr, step_t time, unsigned bitno)
    : f_ctx(ctx)
    , f_expr(expr)
    , f_time(time)
    , f_bitno(bitno)
{}

UCBI::UCBI(const UCBI& ucbi)
    : f_ctx(ucbi.ctx())
    , f_expr(ucbi.expr())
    , f_time(ucbi.time())
    , f_bitno(ucbi.bitno())
{}

TCBI::TCBI(Expr_ptr ctx, Expr_ptr expr, step_t time, unsigned bitno, step_t base)
    : f_ctx(ctx)
    , f_expr(expr)
    , f_time(time)
    , f_bitno(bitno)
    , f_base(base)
{}

TCBI::TCBI(const TCBI& tcbi)
    : f_ctx(tcbi.ctx())
    , f_expr(tcbi.expr())
    , f_time(tcbi.time())
    , f_bitno(tcbi.bitno())
    , f_base(tcbi.base())
{}

ostream& operator<<(ostream& os, const Expr_ptr t)
{
    Printer (os) << t;
    return os;
}

ostream& operator<<(ostream& os, const FQExpr& fqexpr)
{
    Expr_ptr ctx = fqexpr.ctx();
    Expr_ptr expr = fqexpr.expr();
    step_t step = fqexpr.time();

    os << "@" <<  step << "{";
    Printer (os) << fqexpr.ctx()
                 << "::"
                 << fqexpr.expr();
    os << "}";
    return os;
}

ostream& operator<<(ostream& os, const UCBI& ucbi)
{
    Expr_ptr ctx = ucbi.ctx();
    Expr_ptr expr = ucbi.expr();
    step_t step = ucbi.time();
    unsigned bitno = ucbi.bitno();

    os << "+" << step
       << "{" ;

    Printer (os) << ctx
                 << "::"
                 << expr ;

    os << "}."
       << bitno ;

    return os;
}

ostream& operator<<(ostream& os, const TCBI& tcbi)
{
    Expr_ptr ctx = tcbi.ctx();
    Expr_ptr expr = tcbi.expr();
    step_t step = tcbi.time();
    unsigned bitno = tcbi.bitno();
    step_t timebase = tcbi.base();

    os << "@" << timebase
       << "{"

       << "+" <<  step
       << "{" ;

    Printer (os) << ctx
                 << "::"
                 << expr ;

    os << "}."
       << bitno ;

    os << "}" ;

    return os;
}
