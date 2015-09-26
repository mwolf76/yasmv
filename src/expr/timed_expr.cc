/**
 *  @file timed_expr.cc
 *  @brief Expression management
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

#include <expr/timed_expr.hh>

TimedExpr::TimedExpr(Expr_ptr expr, step_t time)
    : f_expr(expr)
    , f_time(time)
{}

std::ostream& operator<<(std::ostream& os, const TimedExpr& timed_expr)
{
    Expr_ptr expr
        (timed_expr.expr());
    step_t time
        (timed_expr.time());

    if (UINT_MAX != time)
        os
            << "@"
            << time;

    os
        << "{" << expr
        << "}" ;

    return os;
}

long TimedExprHash::operator() (const TimedExpr& k) const
{
    long x, res = 0;
    ExprHash eh;

    long v0 = eh(*k.expr());
    long v1 = k.time();

    res = (res << 4) + v0;
    if ((x = res & 0xF0000000L) != 0) {
        res ^= (x >> 24);
    }
    res &= ~x;

    res = (res << 4) + v1;
    if ((x = res & 0xF0000000L) != 0) {
        res ^= (x >> 24);
    }
    res &= ~x;

    return res;
}

bool TimedExprEq::operator()(const TimedExpr& x, const TimedExpr& y) const
{
    return (x.expr() == y.expr() && x.time() == y.time());
}

