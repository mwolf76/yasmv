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

#include <boost/unordered_set.hpp>
#include <utility>

#include <expr.hh>

/* -- expr pool definitions -------------------------------------------------- */

struct ExprHash {
    long operator() (const Expr& k) const;
};

struct ExprEq {
    bool operator() (const Expr& x, const Expr& y) const;
};

typedef boost::unordered_set<Expr, ExprHash, ExprEq> ExprPool;
typedef std::pair<ExprPool::iterator, bool> ExprPoolHit;

/* -- atom pool definitions -------------------------------------------------- */

struct AtomHash {
    long operator() (const Atom& k) const;
};

struct AtomEq {
    bool operator() (const Atom& x, const Atom& y) const;
};

typedef boost::unordered_set<Atom, AtomHash, AtomEq> AtomPool;
typedef std::pair<AtomPool::iterator, bool> AtomPoolHit;

/* -- fqexpr pool definitions ------------------------------------------------ */

struct FQExprHash {
    long operator() (const FQExpr& k) const;
};

struct FQExprEq {
    bool operator() (const FQExpr& x, const FQExpr& y) const;
};

typedef boost::unordered_set<FQExpr, FQExprHash, FQExprEq> FQExprPool;
typedef std::pair<FQExprPool::iterator, bool> FQExprPoolHit;

/* -- generic ptr based definitions ------------------------------------------ */
struct PtrHash {
    long operator() (void *ptr) const;
};

struct PtrEq {
    bool operator() (const void* x,
                     const void* y) const;
};

/* -- integer key definitions (here to collect them all together) ------------ */
struct ValueHash {
    long operator() (value_t) const;
};

struct ValueEq {
    bool operator() (const value_t x,
                     const value_t y) const;
};

struct IntHash {
    inline long operator() (int term) const
    { return (long) (term); }
};

struct IntEq {
    inline bool operator() (const int phi,
                            const int psi) const
    { return phi == psi; }
};

struct PolarizedLiteralHash {
    long operator() (const PolarizedLiteral& k) const;
};

struct PolarizedLiteralEq {
    bool operator() (const PolarizedLiteral& x,
                     const PolarizedLiteral& y) const;
};

struct UCBIHash {
    long operator() (const UCBI& k) const;
};

struct UCBIEq {
    bool operator() (const UCBI& x, const UCBI& y) const;
};

struct TCBIHash {
    long operator() (const TCBI& k) const;
};

struct TCBIEq {
    bool operator() (const TCBI& x, const TCBI& y) const;
};

#endif
