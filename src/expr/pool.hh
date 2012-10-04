/**
 *  @file pool.hh
 *  @brief Expression management, pooling subsystem
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
#ifndef EXPR_POOL_H
#define EXPR_POOL_H

#include <expr.hh>

// Expression pool
struct ExprHash {
    long operator() (const Expr& k) const {
        {
            if (k.f_symb == IDENT) {
                return (long)(k.u.f_atom);
            }

            else {
                long v0, v1, x, res = (long)(k.f_symb);
                if (k.f_symb == ICONST
                    || k.f_symb == SWCONST
                    || k.f_symb == UWCONST) {
                    v0 = (long)(k.u.f_value);
                    v1 = (long)(k.u.f_value >> sizeof(long));
                }
                else {
                    v0 = (long)(k.u.f_lhs);
                    v1 = (long)(k.u.f_rhs);
                }

                res = (res << 4) + v0;
                if ((x = res & 0xF0000000L) != 0)
                    res ^= (x >> 24);
                res &= ~x;

                res = (res << 4) + v1;
                if ((x = res & 0xF0000000L) != 0)
                    res ^= (x >> 24);
                res &= ~x;

                return res;
            }

            assert (0); // unreachable
        }
    }
};

// An equality predicate functor
struct ExprEq {
    bool operator() (const Expr& x, const Expr& y) const
    {
        return
            // both exprs must be the same type and...
            x.f_symb == y.f_symb
            && (
                /* ...either have the same identifier */
                (x.f_symb == IDENT  && *x.u.f_atom == *y.u.f_atom) ||

                /* ...or have the same constant size, value */
                (x.f_symb >= ICONST && x.f_symb <= SWCONST
                 && x.u.f_size == y.u.f_size && x.u.f_size == y.u.f_size) ||

                /* ...or share the same subtrees */
                (x.u.f_lhs == y.u.f_lhs && y.u.f_rhs == y.u.f_rhs));
    }
};

typedef unordered_set<Expr, ExprHash, ExprEq> ExprPool;
typedef pair<ExprPool::iterator, bool> ExprPoolHit;

#endif
