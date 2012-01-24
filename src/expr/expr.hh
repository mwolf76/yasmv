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

  /* temporal ops */
  INIT, NEXT,

  /* arithmetical operators */
  NEG, PLUS, SUB, DIV, MUL, MOD,

  /* logical/bitwise operators */
  NOT, AND, OR, XOR, XNOR, IMPLIES, IFF, LSHIFT, RSHIFT,

  /* relational operators */
  EQ, NE, GE, GT, LE, LT,

  /* conditionals */
  ITE, COND,

  /* leaves */
  ICONST, UWCONST, SWCONST, IDENT, LITERAL, NIL,

  /* postfix exprs */
  DOT, SUBSCRIPT, RANGE,

  /* utils */
  COMMA, SET,

} ExprType;

// using STL string as basic atom class
typedef string Atom;

typedef struct Expr_TAG {
  ExprType f_symb;

  union {
    struct {
      const struct Expr_TAG& f_lhs;
      const struct Expr_TAG& f_rhs;
    };

    /* 64 bit */
    unsigned long long f_ull;

    struct {
      const Atom& f_atom;
    };
  };

  // NOTE: there is no chance of getting the wrong ctor called as
  // any of them has a different number of paramters. (sweet)
  inline Expr_TAG()
    : f_symb(NIL)
    , f_lhs(*this)
    , f_rhs(*this)
  {}

  inline Expr_TAG(const Atom& atom)
    : f_symb(IDENT)
    , f_atom(atom)
  {}

  inline Expr_TAG(ExprType symb,
                  long long value)
    : f_symb(symb)
    , f_ull(value)
  {
    // safety check
    assert ((symb == ICONST)  ||
            (symb == UWCONST) ||
            (symb == SWCONST));
  }

  // ordinary expr
  inline Expr_TAG(ExprType symb,
                  const Expr_TAG& lhs,
                  const Expr_TAG& rhs)
    : f_symb(symb)
    , f_lhs(lhs)
    , f_rhs(rhs)
  {}

  inline bool operator==(const struct Expr_TAG& other) const
  {
    return this->f_symb == other.f_symb &&
      this->f_lhs == other.f_lhs &&
      this->f_rhs == other.f_rhs ;
  }

} Expr;

class IExprVisitor {
public:
  virtual void visit(Expr& expr) =0;
};

static Expr nil;

// Expression pool
struct ExprHash {
  inline long operator() (const Expr& k) const
  {
    long x, res = (long)(k.f_symb);

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
};

struct ExprEq {
  inline bool operator() (const Expr& x, const Expr& y) const
  {
    return x.f_symb == y.f_symb &&
      &x.f_lhs == &y.f_lhs &&
      &y.f_rhs == &y.f_rhs ;
  }
};

typedef unordered_set<Expr, ExprHash, ExprEq> ExprPool;
typedef pair<ExprPool::iterator, bool> ExprPoolHit;

// Atom pool
struct AtomHash {
  inline long operator() (const Atom& k) const
  {
    unsigned long hash = 0;
    unsigned long x    = 0;

    for(std::size_t i = 0; i < k.length(); i++)
      {
        hash = (hash << 4) + k[i];
        if((x = hash & 0xF0000000L) != 0)
          {
            hash ^= (x >> 24);
          }
        hash &= ~x;
      }

    return hash;
  }
};

struct AtomEq {
  inline bool operator() (const Atom& x, const Atom& y) const
  { return x == y; }
};

typedef unordered_set<Atom, AtomHash, AtomEq> AtomPool;
typedef pair<AtomPool::iterator, bool> AtomPoolHit;

ostream& operator<<(ostream& os, const Expr& t);

typedef Expr* Expr_ptr;
typedef vector<Expr_ptr> Exprs;

class IModule {
public:
  virtual bool is_main() const =0;
  virtual const Expr& get_name() const =0;

  virtual const Exprs& get_formalParams() const =0;
  virtual void add_formalParam(Expr& identifier) =0;

  // virtual const ISADeclarations& get_isaDecls() =0;
  // virtual IModule& operator+=(ISADeclaration& identifier) =0;

  virtual const Variables& get_localVars() const =0;
  virtual void add_localVar(IVariable& var) =0;

  virtual const Defines& get_localDefs() const =0;
  virtual void add_localDef(IDefine& def) =0;

  virtual const Assigns& get_assign() const =0;
  virtual void add_assign(IAssign& assgn) =0;

  virtual const Exprs& get_init() const =0;
  virtual void add_init(Expr& expr) =0;

  virtual const Exprs& get_invar() const =0;
  virtual void add_invar(Expr& expr) =0;

  virtual const Exprs& get_trans() const =0;
  virtual void add_trans(Expr& expr) =0;

  virtual const Exprs& get_fairness() const =0;
  virtual void add_fairness(Expr& expr) =0;

};

#endif
