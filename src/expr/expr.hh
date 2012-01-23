/*
Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

 */

/**
 * @file expr.hh
 *
 * @brief Expression management
 *
 * This module contains definitions and services that implement an
 * optimized storage for expressions. Expressions are stored in a
 * Directed Acyclic Graph (DAG) for data sharing.
 *
 */

#ifndef EXPR_H
#define EXPR_H
#include <common.hh>

typedef enum {
  /* LTL */
  F, G, X, U, R,

  /* CTL */
  AF, EF, AG, EG, AX, EX, AU, EU, AR, ER,

  /* arithmetical operators */
  NEG, PLUS, SUB, DIV, MUL, MOD,

  /* logical/bitwise operators */
  NOT, AND, OR, XOR, XNOR, IMPLIES, IFF,

  /* relational operators */
  EQ, NE, GE, GT, LE, LT,

  /* conditionals */
  ITE, COND,

  /* leaves */
  ICONST, UWCONST, SWCONST, IDENT, LITERAL, NIL,

} ExprType;


typedef struct Expr_TAG {
  ExprType f_symb;

  union {
    struct {
      const struct Expr_TAG& f_lhs;
      const struct Expr_TAG& f_rhs;
    };

    /* 64 bit */
    unsigned long long f_ull;
  };

  Expr_TAG(ExprType symb, const Expr_TAG& lhs, const Expr_TAG& rhs)
    : f_symb(symb),
      f_lhs(lhs),
      f_rhs(rhs)
  {}

  Expr_TAG()
    : f_symb(NIL),
      f_lhs(*this),
      f_rhs(*this)
  {}

} Expr;

typedef struct {
  // ELF hash (cfr. General Hash Functions by
  long operator() (const Expr& k) const
  {
    long res, x = (long)(k.f_symb);

    res = (res << 4) + (long)(&(k.f_lhs));
    if ((x = res & 0xF0000000L) != 0)
      res ^= (x >> 24);
    res &= ~x;

    res = (res << 4) + (long)(&(k.f_rhs));
    if ((x = res & 0xF0000000L) != 0)
      res ^= (x >> 24);
    res &= ~x;

    return res;
  }
} ExprHash;

typedef struct {
 bool operator() (const Expr& x, const Expr& y) const
  {
    return x.f_symb == y.f_symb &&
      &x.f_lhs == &y.f_lhs &&
      &y.f_rhs == &y.f_rhs ;
  }
} ExprEq;

ostream& operator<<(ostream& os, const Expr& t)
{ return os << ""; }

// using STL string as basic atom class
typedef string Atom;
typedef Atom* Atom_ptr;
typedef vector<Atom_ptr> Atoms;

// typedef Literal* Literal_ptr;
// typedef vector<Literal_ptr> Literals;

typedef Expr* Expr_ptr;
typedef vector<Expr_ptr> Exprs;

typedef unordered_set<Expr, ExprHash, ExprEq> ExprPool;
typedef pair<ExprPool::iterator, bool> ExprPoolHit;

class ExprMgr;
typedef ExprMgr* ExprMgr_ptr;

class ExprMgr  {
  typedef ExprMgr* ExprMgr_ptr;

public:
  static ExprMgr_ptr INSTANCE() {
    if (! f_instance) f_instance = new ExprMgr();
    return f_instance;
  }

  static const Expr& nil;

  /* LTL */
  inline const Expr& make_F(Expr& expr)
  { return make_expr(F, expr, nil); }

  inline const Expr& make_G(Expr& expr)
  { return make_expr(G, expr, nil); }

  inline const Expr& make_X(Expr& expr)
  { return make_expr(X, expr, nil); }

  inline const Expr& make_U(Expr& expr)
  { return make_expr(U, expr, nil); }

  inline const Expr& make_R(Expr& expr)
  { return make_expr(R, expr, nil); }

  /* CTL (A) */
  inline const Expr& make_AF(Expr& expr)
  { return make_expr(AF, expr, nil); }

  inline const Expr& make_AG(Expr& expr)
  { return make_expr(AG, expr, nil); }

  inline const Expr& make_AX(Expr& expr)
  { return make_expr(AX, expr, nil); }

  inline const Expr& make_AU(Expr& expr)
  { return make_expr(AU, expr, nil); }

  inline const Expr& make_AR(Expr& expr)
  { return make_expr(AR, expr, nil); }

  /* CTL (E) */
  inline const Expr& make_EF(Expr& expr)
  { return make_expr(EF, expr, nil); }

  inline const Expr& make_EG(Expr& expr)
  { return make_expr(EG, expr, nil); }

  inline const Expr& make_EX(Expr& expr)
  { return make_expr(EX, expr, nil); }

  inline const Expr& make_EU(Expr& expr)
  { return make_expr(EU, expr, nil); }

  inline const Expr& make_ER(Expr& expr)
  { return make_expr(ER, expr, nil); }

  /* arithmetical operators */
  inline const Expr& make_neg(Expr& expr)
  { return make_expr(NEG, expr, nil); }

  inline const Expr& make_plus(Expr& a, Expr& b)
  { return make_expr(PLUS, a, b); }

  inline const Expr& make_sub(Expr& a, Expr& b)
  { return make_expr(SUB, a, b); }

  inline const Expr& make_div(Expr& a, Expr& b)
  { return make_expr(DIV, a, b); }

  inline const Expr& make_mul(Expr& a, Expr& b)
  { return make_expr(MUL, a, b); }

  inline const Expr& make_mod(Expr& a, Expr& b)
  { return make_expr(MOD, a, b); }

  /* logical/bitwise operators */
  inline const Expr& make_not(Expr& expr)
  { return make_expr(NOT, expr, nil); }

  inline const Expr& make_and(Expr& a, Expr& b)
  { return make_expr(AND, a, b); }

  inline const Expr& make_or(Expr& a, Expr& b)
  { return make_expr(OR, a, b); }

  inline const Expr& make_xor(Expr& a, Expr& b)
  { return make_expr(XOR, a, b); }

  inline const Expr& make_xnor(Expr& a, Expr& b)
  { return make_expr(XNOR, a, b); }

  inline const Expr& make_implies(Expr& a, Expr& b)
  { return make_expr(IMPLIES, a, b); }

  inline const Expr& make_iff(Expr& a, Expr& b)
  { return make_expr(IFF, a, b); }

  /* relational operators */
  inline const Expr& make_eq(Expr& a, Expr& b)
  { return make_expr(EQ, a, b); }

  inline const Expr& make_ne(Expr& a, Expr& b)
  { return make_expr(NE, a, b); }

  inline const Expr& make_ge(Expr& a, Expr& b)
  { return make_expr(GE, a, b); }

  inline const Expr& make_gt(Expr& a, Expr& b)
  { return make_expr(GT, a, b); }

  inline const Expr& make_le(Expr& a, Expr& b)
  { return make_expr(LE, a, b); }

  inline const Expr& make_lt(Expr& a, Expr& b)
  { return make_expr(LT, a, b); }

  inline const Expr& make_ite(Expr& pred, Expr& t, Expr& e)
  { return make_expr(ITE, make_expr(COND, pred, t), e); }

  // /* leaves */
  // inline const Expr& make_iconst(long long value)
  // { return make_expr(ICONST, value); }

  // inline const Expr& make_uwconst(unsigned long long value)
  // { return make_expr(UWCONST, value); }

  // inline const Expr& make_uwconst(long long value)
  // { return make_expr(SWCONST, value); }

protected:
  ExprMgr()
    : f_nil(),
      f_pool()
  {
    f_pool.insert(f_nil);
  }

private:
  static ExprMgr_ptr f_instance;

  /* low-level services */
  inline const Expr& make_expr(ExprType et, const Expr& a, const Expr& b)
  { f_pool.insert(Expr(et, a, b)); }

  ExprPool f_pool;
  Expr f_nil;
};

// static initialization
ExprMgr_ptr ExprMgr::f_instance = NULL;

#endif
