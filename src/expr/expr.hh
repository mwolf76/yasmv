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
  NEG, ADD, SUB, DIV, MUL, MOD,

  /* logical/bitwise operators */
  NOT, AND, OR, XOR, XNOR, IMPLIES, IFF, LSHIFT, RSHIFT,

  /* relational operators */
  EQ, NE, GE, GT, LE, LT,

  /* conditionals */
  ITE, COND,

  /* leaves */
  ICONST, UWCONST, SWCONST, IDENT, NIL,

  /* postfix exprs */
  DOT, SUBSCRIPT, RANGE,

  /* utils */
  COMMA, SET,

} ExprType;

// using STL string as basic atom class
typedef string Atom;
typedef Atom* Atom_ptr;

typedef struct Expr_TAG {
  ExprType f_symb;

  union {
    struct {
      struct Expr_TAG* f_lhs;
      struct Expr_TAG* f_rhs;
    };

    /* 64 bit */
    unsigned long long f_ull;

    struct {
      const Atom_ptr f_atom;
    };
  };

  // NOTE: there is no chance of getting the wrong ctor called as
  // any of them has a different number of paramters. (sweet)
  inline Expr_TAG()
    : f_symb(NIL)
    , f_lhs(NULL)
    , f_rhs(NULL)
  {}

  inline Expr_TAG(const Atom& atom)
    : f_symb(IDENT)
    , f_atom(const_cast<const Atom_ptr> (&atom))
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
                  Expr_TAG* lhs,
                  Expr_TAG* rhs)
    : f_symb(symb)
    , f_lhs(lhs)
    , f_rhs(rhs)
  {}

  inline bool operator==(const struct Expr_TAG* other) const
  {
    return this->f_symb == other->f_symb &&
      this->f_lhs == other->f_lhs &&
      this->f_rhs == other->f_rhs ;
  }

} Expr;

// Expression pool
struct ExprHash {
  long operator() (const Expr& k) const {
    {
      if (k.f_symb == IDENT) {
        return (long)(k.f_atom);
      }

      else {
        long v0, v1, x, res = (long)(k.f_symb);
        if (k.f_symb == ICONST
            || k.f_symb == SWCONST
            || k.f_symb == UWCONST) {
          v0 = (long)(k.f_ull);
          v1 = (long)(k.f_ull >> sizeof(long));
        }
        else {
          v0 = (long)(k.f_lhs);
          v1 = (long)(k.f_rhs);
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

struct ExprEq {
  bool operator() (const Expr& x, const Expr& y) const
  {
    return
      // both exprs must be the same type...
      x.f_symb == y.f_symb && (

                               /* either the same identifier */
                               (x.f_symb == IDENT  && x.f_atom == y.f_atom) ||

                               /* or the same constant */
                               (x.f_symb >= ICONST && x.f_ull == y.f_ull) ||

                               /* or the same subtree */
                               (x.f_lhs == y.f_lhs && y.f_rhs == y.f_rhs));
  }
};

typedef unordered_set<Expr, ExprHash, ExprEq> ExprPool;
typedef pair<ExprPool::iterator, bool> ExprPoolHit;

// Atom pool
struct AtomHash {
  long operator() (const Atom& k) const
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
  bool operator() (const Atom& x, const Atom& y) const
  { return x == y; }
};

typedef unordered_set<Atom, AtomHash, AtomEq> AtomPool;
typedef pair<AtomPool::iterator, bool> AtomPoolHit;

typedef Expr* Expr_ptr;
typedef vector<Expr_ptr> Exprs;

// for logging purposes
ostream& operator<<(ostream& os, const Expr_ptr t);

class ExprMgr;
typedef ExprMgr* ExprMgr_ptr;

class ExprMgr  {
public:
  static ExprMgr& INSTANCE()
  {
    if (! f_instance)
        f_instance = new ExprMgr();

    return (*f_instance);
  }

  /* LTL */
  inline Expr_ptr make_F(Expr_ptr expr)
  { return make_expr(F, expr, NULL); }

  inline Expr_ptr make_G(Expr_ptr expr)
  { return make_expr(G, expr, NULL); }

  inline Expr_ptr make_X(Expr_ptr expr)
  { return make_expr(X, expr, NULL); }

  inline Expr_ptr make_U(Expr_ptr lhs, Expr_ptr rhs)
  { return make_expr(U, lhs, rhs); }

  inline Expr_ptr make_R(Expr_ptr lhs, Expr_ptr rhs)
  { return make_expr(R, lhs, rhs); }

  /* CTL (A) */
  inline Expr_ptr make_AF(Expr_ptr expr)
  { return make_expr(AF, expr, NULL); }

  inline Expr_ptr make_AG(Expr_ptr expr)
  { return make_expr(AG, expr, NULL); }

  inline Expr_ptr make_AX(Expr_ptr expr)
  { return make_expr(AX, expr, NULL); }

  inline Expr_ptr make_AU(Expr_ptr lhs, Expr_ptr rhs)
  { return make_expr(AU, lhs, rhs); }

  inline Expr_ptr make_AR(Expr_ptr lhs, Expr_ptr rhs)
  { return make_expr(AR, lhs, rhs); }

  /* CTL (E) */
  inline Expr_ptr make_EF(Expr_ptr expr)
  { return make_expr(EF, expr, NULL); }

  inline Expr_ptr make_EG(Expr_ptr expr)
  { return make_expr(EG, expr, NULL); }

  inline Expr_ptr make_EX(Expr_ptr expr)
  { return make_expr(EX, expr, NULL); }

  inline Expr_ptr make_EU(Expr_ptr lhs, Expr_ptr rhs)
  { return make_expr(EU, lhs, rhs); }

  inline Expr_ptr make_ER(Expr_ptr lhs, Expr_ptr rhs)
  { return make_expr(ER, lhs, rhs); }

  /* temporal ops */
  inline Expr_ptr make_init(Expr_ptr expr)
  { return make_expr(INIT, expr, NULL); }

  inline Expr_ptr make_next(Expr_ptr expr)
  { return make_expr(NEXT, expr, NULL); }

  /* arithmetical operators */
  inline Expr_ptr make_neg(Expr_ptr expr)
  { return make_expr(NEG, expr, NULL); }

  inline Expr_ptr make_add(Expr_ptr a, Expr_ptr b)
  { return make_expr(ADD, a, b); }

  inline Expr_ptr make_sub(Expr_ptr a, Expr_ptr b)
  { return make_expr(SUB, a, b); }

  inline Expr_ptr make_div(Expr_ptr a, Expr_ptr b)
  { return make_expr(DIV, a, b); }

  inline Expr_ptr make_mul(Expr_ptr a, Expr_ptr b)
  { return make_expr(MUL, a, b); }

  inline Expr_ptr make_mod(Expr_ptr a, Expr_ptr b)
  { return make_expr(MOD, a, b); }

  /* logical/bitwise operators */
  inline Expr_ptr make_not(Expr_ptr expr)
  { return make_expr(NOT, expr, NULL); }

  inline Expr_ptr make_and(Expr_ptr a, Expr_ptr b)
  { return make_expr(AND, a, b); }

  inline Expr_ptr make_or(Expr_ptr a, Expr_ptr b)
  { return make_expr(OR, a, b); }

  inline Expr_ptr make_lshift(Expr_ptr a, Expr_ptr b)
  { return make_expr(LSHIFT, a, b); }

  inline Expr_ptr make_rshift(Expr_ptr a, Expr_ptr b)
  { return make_expr(RSHIFT, a, b); }

  inline Expr_ptr make_xor(Expr_ptr a, Expr_ptr b)
  { return make_expr(XOR, a, b); }

  inline Expr_ptr make_xnor(Expr_ptr a, Expr_ptr b)
  { return make_expr(XNOR, a, b); }

  inline Expr_ptr make_implies(Expr_ptr a, Expr_ptr b)
  { return make_expr(IMPLIES, a, b); }

  inline Expr_ptr make_iff(Expr_ptr a, Expr_ptr b)
  { return make_expr(IFF, a, b); }

  /* relational operators */
  inline Expr_ptr make_eq(Expr_ptr a, Expr_ptr b)
  { return make_expr(EQ, a, b); }

  inline Expr_ptr make_ne(Expr_ptr a, Expr_ptr b)
  { return make_expr(NE, a, b); }

  inline Expr_ptr make_ge(Expr_ptr a, Expr_ptr b)
  { return make_expr(GE, a, b); }

  inline Expr_ptr make_gt(Expr_ptr a, Expr_ptr b)
  { return make_expr(GT, a, b); }

  inline Expr_ptr make_le(Expr_ptr a, Expr_ptr b)
  { return make_expr(LE, a, b); }

  inline Expr_ptr make_lt(Expr_ptr a, Expr_ptr b)
  { return make_expr(LT, a, b); }

  inline Expr_ptr make_cond(Expr_ptr a, Expr_ptr b)
  { return make_expr(COND, a, b); }

  inline Expr_ptr make_ite(Expr_ptr a, Expr_ptr b)
  { return make_expr(ITE, a, b); }

  /* leaves */
  inline Expr_ptr make_iconst(long long value)
  { return __make_expr(f_expr_pool.insert(Expr(ICONST, value))); }

  inline Expr_ptr make_uwconst(unsigned long long value)
  { return __make_expr(f_expr_pool.insert(Expr(UWCONST, value))); }

  inline Expr_ptr make_swconst(long long value)
  { return __make_expr(f_expr_pool.insert(Expr(SWCONST, value))); }

  // inline const Expr_ptr make_enum(EnumType& enumeration)
  // {
  //   Expr_ptr res = PX(NULL);
  //   const EnumLiterals& literals = enumeration.get_literals();

  //   /* reverse iteration */
  //   for (EnumLiterals::reverse_iterator eye = literals.rbegin();
  //        eye != literals.rend(); eye ++) {
  //     res = PX(make_expr(COMMA, (**eye), *res));
  //   }

  //   return make_expr(SET, *res, NULL);
  // }

  inline Expr_ptr make_dot(Expr_ptr a, Expr_ptr b)
  { return make_expr(DOT, a, b); }

  inline Expr_ptr make_subscript(Expr_ptr a, Expr_ptr b)
  { return make_expr(SUBSCRIPT, a, b); }

  inline Expr_ptr make_range(Expr_ptr a, Expr_ptr b)
  { return make_expr(RANGE, a, b);  }

  // TODO:
  inline Expr_ptr make_hex_const(Atom atom)
  { return NULL; }

  inline Expr_ptr make_oct_const(Atom atom)
  { return NULL; }

  inline Expr_ptr make_dec_const(Atom atom)
  { return NULL; }

  /* predefined identifiers */
  inline Expr_ptr make_boolean()
  { return bool_expr; }
  inline Expr_ptr make_main()
  { return main_expr; }

  inline Expr_ptr make_identifier(Atom atom)
  {
    AtomPoolHit ah = (f_atom_pool.insert(atom));
    if (ah.second) {
      AtomPool::const_pointer atom = & (*ah.first);
      logger << "Added new atom to pool: '" << (*atom) << "'" << endl;
    }

    return make_expr(*ah.first);
  }

protected:
  ExprMgr()
  {
    const Atom_ptr atom_boolean = new Atom("boolean");
    const ExprPoolHit bool_hit = f_expr_pool.insert(*atom_boolean);
    assert(bool_hit.second); // it has to be true
    bool_expr = const_cast<Expr_ptr> (& (*bool_hit.first));

    const Atom_ptr atom_main = new Atom("main");
    const ExprPoolHit main_hit = f_expr_pool.insert(*atom_main);
    assert(main_hit.second); // it has to be true
    main_expr = const_cast<Expr_ptr> (& (*main_hit.first));
  }

private:
  static ExprMgr_ptr f_instance;

  /* mid level services */
  Expr_ptr make_expr(ExprType et, Expr_ptr a, Expr_ptr b)
  { return __make_expr(f_expr_pool.insert(Expr(et, a, b))); }

  Expr_ptr make_expr(const Atom& atom)
  { return __make_expr(f_expr_pool.insert(Expr(atom))); }

  // low-level
  inline Expr_ptr __make_expr(ExprPoolHit hit) {
    ExprPool::pointer expr = const_cast <Expr_ptr> ( & (*hit.first) );

    if (hit.second) {
      logger << "Added new expr to pool: '" << expr << "'" << endl;
    }
    return expr;
  }

  /* builtins */
  Expr_ptr bool_expr;
  Expr_ptr main_expr;

  /* shared pools */
  ExprPool f_expr_pool;
  AtomPool f_atom_pool;
};

#endif
