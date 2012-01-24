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

#ifndef EXPR_MGR_H
#define EXPR_MGR_H

#include <common.hh>
#include <expr.hh>

// a Pointer to eXpression conversion macro to simplify expr manipulation code
#define PX(expr) (const_cast<Expr_ptr>(&(expr)))

class ExprMgr;
typedef ExprMgr* ExprMgr_ptr;

class ExprMgr  {
public:

  static ExprMgr& INSTANCE() {
    if (! f_instance) f_instance = new ExprMgr();
    return (*f_instance);
  }

  /* LTL */
  inline const Expr& make_F(const Expr& expr)
  { return make_expr(F, expr, nil); }

  inline const Expr& make_G(const Expr& expr)
  { return make_expr(G, expr, nil); }

  inline const Expr& make_X(const Expr& expr)
  { return make_expr(X, expr, nil); }

  inline const Expr& make_U(const Expr& expr)
  { return make_expr(U, expr, nil); }

  inline const Expr& make_R(const Expr& expr)
  { return make_expr(R, expr, nil); }

  /* CTL (A) */
  inline const Expr& make_AF(const Expr& expr)
  { return make_expr(AF, expr, nil); }

  inline const Expr& make_AG(const Expr& expr)
  { return make_expr(AG, expr, nil); }

  inline const Expr& make_AX(const Expr& expr)
  { return make_expr(AX, expr, nil); }

  inline const Expr& make_AU(const Expr& expr)
  { return make_expr(AU, expr, nil); }

  inline const Expr& make_AR(const Expr& expr)
  { return make_expr(AR, expr, nil); }

  /* CTL (E) */
  inline const Expr& make_EF(const Expr& expr)
  { return make_expr(EF, expr, nil); }

  inline const Expr& make_EG(const Expr& expr)
  { return make_expr(EG, expr, nil); }

  inline const Expr& make_EX(const Expr& expr)
  { return make_expr(EX, expr, nil); }

  inline const Expr& make_EU(const Expr& expr)
  { return make_expr(EU, expr, nil); }

  inline const Expr& make_ER(const Expr& expr)
  { return make_expr(ER, expr, nil); }

  /* temporal ops */
  inline const Expr& make_init(const Expr& expr)
  { return make_expr(INIT, expr, nil); }

  inline const Expr& make_next(const Expr& expr)
  { return make_expr(NEXT, expr, nil); }

  /* arithmetical operators */
  inline const Expr& make_neg(const Expr& expr)
  { return make_expr(NEG, expr, nil); }

  inline const Expr& make_add(const Expr& a, const Expr& b)
  { return make_expr(PLUS, a, b); }

  inline const Expr& make_sub(const Expr& a, const Expr& b)
  { return make_expr(SUB, a, b); }

  inline const Expr& make_div(const Expr& a, const Expr& b)
  { return make_expr(DIV, a, b); }

  inline const Expr& make_mul(const Expr& a, const Expr& b)
  { return make_expr(MUL, a, b); }

  inline const Expr& make_mod(const Expr& a, const Expr& b)
  { return make_expr(MOD, a, b); }

  /* logical/bitwise operators */
  inline const Expr& make_not(const Expr& expr)
  { return make_expr(NOT, expr, nil); }

  inline const Expr& make_and(const Expr& a, const Expr& b)
  { return make_expr(AND, a, b); }

  inline const Expr& make_or(const Expr& a, const Expr& b)
  { return make_expr(OR, a, b); }

  inline const Expr& make_lshift(const Expr& a, const Expr& b)
  { return make_expr(LSHIFT, a, b); }

  inline const Expr& make_rshift(const Expr& a, const Expr& b)
  { return make_expr(RSHIFT, a, b); }

  inline const Expr& make_xor(const Expr& a, const Expr& b)
  { return make_expr(XOR, a, b); }

  inline const Expr& make_xnor(const Expr& a, const Expr& b)
  { return make_expr(XNOR, a, b); }

  inline const Expr& make_implies(const Expr& a, const Expr& b)
  { return make_expr(IMPLIES, a, b); }

  inline const Expr& make_iff(const Expr& a, const Expr& b)
  { return make_expr(IFF, a, b); }

  /* relational operators */
  inline const Expr& make_eq(const Expr& a, const Expr& b)
  { return make_expr(EQ, a, b); }

  inline const Expr& make_ne(const Expr& a, const Expr& b)
  { return make_expr(NE, a, b); }

  inline const Expr& make_ge(const Expr& a, const Expr& b)
  { return make_expr(GE, a, b); }

  inline const Expr& make_gt(const Expr& a, const Expr& b)
  { return make_expr(GT, a, b); }

  inline const Expr& make_le(const Expr& a, const Expr& b)
  { return make_expr(LE, a, b); }

  inline const Expr& make_lt(const Expr& a, const Expr& b)
  { return make_expr(LT, a, b); }

  inline const Expr& make_cond(const Expr& a, const Expr& b)
  { return make_expr(COND, a, b); }

  inline const Expr& make_ite(const Expr& a, const Expr& b)
  { return make_expr(ITE, a, b); }

  /* leaves */
  inline const Expr& make_iconst(long long value)
  { return make_const(ICONST, value); }

  inline const Expr& make_uwconst(unsigned long long value)
  { return make_const(UWCONST, value); }

  inline const Expr& make_uwconst(long long value)
  { return make_const(SWCONST, value); }

  // inline const Expr& make_enum(EnumType& enumeration)
  // {
  //   Expr_ptr res = PX(nil);
  //   const EnumLiterals& literals = enumeration.get_literals();

  //   /* reverse iteration */
  //   for (EnumLiterals::reverse_iterator eye = literals.rbegin();
  //        eye != literals.rend(); eye ++) {
  //     res = PX(make_expr(COMMA, (**eye), *res));
  //   }

  //   return make_expr(SET, *res, nil);
  // }

  inline const Expr& make_dot(const Expr& a, const Expr& b)
  { return make_expr(DOT, a, b); }

  inline const Expr& make_subscript(const Expr& a, const Expr& b)
  { return make_expr(SUBSCRIPT, a, b); }

  inline const Expr& make_range(const Expr& a, const Expr& b)
  { return make_expr(RANGE, a, b);  }

  /* consts */

  // TODO:
  inline const Expr& make_hex_const(const Atom atom)
  { return nil; }

  inline const Expr& make_oct_const(const Atom atom)
  { return nil; }

  inline const Expr& make_dec_const(const Atom atom)
  { return nil; }

  /* predefined identifiers */
  inline const Expr& make_boolean()
  { return make_identifier("boolean"); }

  inline const Expr& make_main()
  { return make_identifier("main"); }

  inline const Expr& make_identifier(const Atom atom)
  {
    AtomPoolHit ah = (f_atom_pool.insert(Atom(atom)));
    if (ah.second) {
      logger << "Added new atom to pool: '" << *ah.first << "'" << endl;
    }

    return make_expr(*ah.first);
  }

protected:
  ExprMgr()
    :  f_expr_pool()
    ,  f_atom_pool()
  {
    // setup pre-defined known identifiers
    f_expr_pool.insert(make_boolean());
  }

private:
  static ExprMgr_ptr f_instance;

  /* low-level services */
  inline const Expr& make_expr(ExprType et, const Expr& a, const Expr& b)
  {
    ExprPoolHit eh = (f_expr_pool.insert(Expr(et, a, b)));
    if (eh.second) {
      logger << "Added new expr to pool" << (*eh.first) << endl;
    }

    return (*eh.first);
  }

  inline const Expr& make_expr(const Atom& atom)
  {
    ExprPoolHit eh = (f_expr_pool.insert(Expr(atom)));
    if (eh.second) {
      logger << "Added new expr to pool" << (*eh.first) << endl;
    }

    return (*eh.first);
  }

  inline const Expr& make_const(ExprType et, long long value)
  {
    assert( et == ICONST || et == UWCONST || et == SWCONST );
    ExprPoolHit eh = (f_expr_pool.insert(Expr(et, value)));
    if (eh.second) {
      logger << "Added new expr to pool" << (*eh.first) << endl;
    }

    return (*eh.first);
  }

  /* shared pools */
  ExprPool f_expr_pool;
  AtomPool f_atom_pool;
};

#endif
