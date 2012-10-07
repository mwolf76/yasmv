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

/* -- expr pool definitions -------------------------------------------------- */

struct ExprHash {
    long operator() (const Expr& k) const;
};

struct ExprEq {
    bool operator() (const Expr& x, const Expr& y) const;
};

typedef unordered_set<Expr, ExprHash, ExprEq> ExprPool;
typedef pair<ExprPool::iterator, bool> ExprPoolHit;

/* -- atom pool definitions -------------------------------------------------- */

struct AtomHash {
    long operator() (const Atom& k) const;
};

struct AtomEq {
    bool operator() (const Atom& x, const Atom& y) const;
};

typedef unordered_set<Atom, AtomHash, AtomEq> AtomPool;
typedef pair<AtomPool::iterator, bool> AtomPoolHit;

/* -- fqexpr pool definitions ------------------------------------------------ */

struct FQExprHash {
    long operator() (const FQExpr& k) const;
};

struct FQExprEq {
    bool operator() (const FQExpr& x, const FQExpr& y) const;
};

typedef unordered_set<FQExpr, FQExprHash, FQExprEq> FQExprPool;
typedef pair<FQExprPool::iterator, bool> FQExprPoolHit;

/* -- generic ptr based definitions ------------------------------------------ */
struct PtrHash {
    long operator() (void *ptr) const;
};

struct PtrEq {
    bool operator() (const void* x,
                     const void* y) const;
};

#endif
