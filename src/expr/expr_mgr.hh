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
// #define PX(expr) (const_cast<Expr_ptr>(&(expr)))

class ExprMgr;
typedef ExprMgr* ExprMgr_ptr;

class ExprMgr  {
public:

  static ExprMgr& INSTANCE() {
    if (! f_instance) f_instance = new ExprMgr();
    return (*f_instance);
  }

  /* LTL */
  inline Expr_ptr make_F( Expr_ptr  expr)
  { return make_expr(F, expr, NULL); }

  inline Expr_ptr make_G( Expr_ptr  expr)
  { return make_expr(G, expr, NULL); }

  inline Expr_ptr make_X( Expr_ptr  expr)
  { return make_expr(X, expr, NULL); }

  inline Expr_ptr make_U( Expr_ptr  expr)
  { return make_expr(U, expr, NULL); }

  inline Expr_ptr make_R( Expr_ptr  expr)
  { return make_expr(R, expr, NULL); }

  /* CTL (A) */
  inline Expr_ptr make_AF( Expr_ptr  expr)
  { return make_expr(AF, expr, NULL); }

  inline Expr_ptr make_AG( Expr_ptr  expr)
  { return make_expr(AG, expr, NULL); }

  inline Expr_ptr make_AX( Expr_ptr  expr)
  { return make_expr(AX, expr, NULL); }

  inline Expr_ptr make_AU( Expr_ptr  expr)
  { return make_expr(AU, expr, NULL); }

  inline Expr_ptr make_AR( Expr_ptr  expr)
  { return make_expr(AR, expr, NULL); }

  /* CTL (E) */
  inline Expr_ptr make_EF( Expr_ptr  expr)
  { return make_expr(EF, expr, NULL); }

  inline Expr_ptr make_EG( Expr_ptr  expr)
  { return make_expr(EG, expr, NULL); }

  inline Expr_ptr make_EX( Expr_ptr  expr)
  { return make_expr(EX, expr, NULL); }

  inline Expr_ptr make_EU( Expr_ptr  expr)
  { return make_expr(EU, expr, NULL); }

  inline Expr_ptr make_ER( Expr_ptr  expr)
  { return make_expr(ER, expr, NULL); }

  /* temporal ops */
  inline Expr_ptr make_init( Expr_ptr  expr)
  { return make_expr(INIT, expr, NULL); }

  inline Expr_ptr make_next( Expr_ptr  expr)
  { return make_expr(NEXT, expr, NULL); }

  /* arithmetical operators */
  inline Expr_ptr make_neg( Expr_ptr  expr)
  { return make_expr(NEG, expr, NULL); }

  inline Expr_ptr make_add( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(ADD, a, b); }

  inline Expr_ptr make_sub( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(SUB, a, b); }

  inline Expr_ptr make_div( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(DIV, a, b); }

  inline Expr_ptr make_mul( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(MUL, a, b); }

  inline Expr_ptr make_mod( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(MOD, a, b); }

  /* logical/bitwise operators */
  inline Expr_ptr make_not( Expr_ptr  expr)
  { return make_expr(NOT, expr, NULL); }

  inline Expr_ptr make_and( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(AND, a, b); }

  inline Expr_ptr make_or( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(OR, a, b); }

  inline Expr_ptr make_lshift( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(LSHIFT, a, b); }

  inline Expr_ptr make_rshift( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(RSHIFT, a, b); }

  inline Expr_ptr make_xor( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(XOR, a, b); }

  inline Expr_ptr make_xnor( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(XNOR, a, b); }

  inline Expr_ptr make_implies( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(IMPLIES, a, b); }

  inline Expr_ptr make_iff( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(IFF, a, b); }

  /* relational operators */
  inline Expr_ptr make_eq( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(EQ, a, b); }

  inline Expr_ptr make_ne( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(NE, a, b); }

  inline Expr_ptr make_ge( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(GE, a, b); }

  inline Expr_ptr make_gt( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(GT, a, b); }

  inline Expr_ptr make_le( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(LE, a, b); }

  inline Expr_ptr make_lt( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(LT, a, b); }

  inline Expr_ptr make_cond( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(COND, a, b); }

  inline Expr_ptr make_ite( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(ITE, a, b); }

  /* leaves */
  inline Expr_ptr make_iconst(long long value)
  { return make_const (ICONST, value); }

  inline Expr_ptr make_uwconst(unsigned long long value)
  { return make_const (UWCONST, value); }

  inline Expr_ptr make_uwconst(long long value)
  { return make_const(SWCONST, value); }

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

  inline Expr_ptr make_dot( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(DOT, a, b); }

  inline Expr_ptr make_subscript( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(SUBSCRIPT, a, b); }

  inline Expr_ptr make_range( Expr_ptr  a,  Expr_ptr  b)
  { return make_expr(RANGE, a, b);  }

  /* s */

  // TODO:
  inline Expr_ptr make_hex_const( Atom atom)
  { return NULL; }

  inline Expr_ptr make_oct_const( Atom atom)
  { return NULL; }

  inline Expr_ptr make_dec_const( Atom atom)
  { return NULL; }

  /* predefined identifiers */
  inline Expr_ptr make_boolean()
  { return make_identifier("boolean"); }

  inline Expr_ptr make_main()
  { return make_identifier("main"); }

  inline Expr_ptr make_identifier( Atom atom)
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
    f_expr_pool.insert(*make_boolean());
  }

private:
  static ExprMgr_ptr f_instance;

  /* low-level services */
  inline Expr_ptr make_expr(ExprType et,  Expr_ptr  a,  Expr_ptr  b)
  {
    ExprPoolHit eh = (f_expr_pool.insert(Expr(et, a, b)));
    if (eh.second) {
      logger << "Added new expr to pool" << (*eh.first) << endl;
    }

    return const_cast <Expr_ptr> (& (*eh.first));
  }

  inline Expr_ptr make_expr(const Atom& atom)
  {
    ExprPoolHit eh = (f_expr_pool.insert(Expr(atom)));
    if (eh.second) {
      logger << "Added new expr to pool" << (*eh.first) << endl;
    }

    return const_cast <Expr_ptr> (& (*eh.first));
  }

  inline Expr_ptr make_const(ExprType et, long long value)
  {
    assert( et == ICONST || et == UWCONST || et == SWCONST );
    ExprPoolHit eh = (f_expr_pool.insert(Expr(et, value)));
    if (eh.second) {
      logger << "Added new expr to pool" << (*eh.first) << endl;
    }

    return const_cast <Expr_ptr> (& (*eh.first));
  }

  /* shared pools */
  ExprPool f_expr_pool;
  AtomPool f_atom_pool;
};

#endif
