/**
 *  @file expr.hh, Fully Qualified Expression (FQEXpr)
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
#ifndef FQ_EXPR_H
#define FQ_EXPR_H

#include <expr.hh>

typedef class FQExpr* FQExpr_ptr;

class FQExpr {
public:
    FQExpr(Expr_ptr expr); // default ctx, default time
    FQExpr(Expr_ptr ctx, Expr_ptr expr, step_t time = 0);

    FQExpr(const FQExpr& fqexpr);

    inline const Expr_ptr& ctx() const
    { return f_ctx; }

    inline const Expr_ptr& expr() const
    { return f_expr; }

    inline step_t time() const
    { return f_time; }

    bool operator==(const FQExpr& other) const;
    unsigned long hash() const;

private:
    // expression ctx (default is 'main')
    Expr_ptr f_ctx;

    // expression body
    Expr_ptr f_expr;

    // expression time (default is 0)
    step_t f_time;
};

struct fqexpr_hash {
    inline long operator() (const FQExpr& x) const
    { return x.hash(); }
};

struct fqexpr_eq {
    inline bool operator() (const FQExpr &x,
                            const FQExpr &y) const
    { return x == y; }
};

#endif
