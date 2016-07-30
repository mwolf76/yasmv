/**
 * @file timed_expr.hh
 * @brief Expression management
 *
 * This header file contains the declarations required by the Timed
 * Expression class.
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

#ifndef TIMED_EXPR_H
#define TIMED_EXPR_H

#include <expr/expr.hh>

class TimedExpr {
public:
    TimedExpr(Expr_ptr expr, step_t time);

    inline Expr_ptr expr() const
    { return f_expr; }

    inline step_t time() const
    { return f_time; }

    inline bool operator==(const TimedExpr& other)
    { return f_expr == other.f_expr && f_time == other.f_time; }

private:
    Expr_ptr f_expr;
    step_t f_time;
};

std::ostream& operator<<(std::ostream& os, const TimedExpr& expr);

struct TimedExprHash {
    long operator() (const TimedExpr& k) const;
};

struct TimedExprEq {
    bool operator() (const TimedExpr& x, const TimedExpr& y) const;
};

typedef boost::unordered_set<Expr, ExprHash, ExprEq> ExprPool;
typedef std::pair<ExprPool::iterator, bool> ExprPoolHit;

#endif /* TIMED_EXPR_H */
