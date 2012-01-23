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

  /* utils */
  COMMA, SET,

} ExprType;

// using STL string as basic atom class
typedef string Atom;

// TODO: document this
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

  // ordinary expr
  Expr_TAG(ExprType symb, const Expr_TAG& lhs, const Expr_TAG& rhs)
    : f_symb(symb)
    , f_lhs(lhs)
    , f_rhs(rhs)
  {}

  // identifier
  Expr_TAG(const Atom& atom)
    : f_symb(IDENT)
    , f_atom(atom)
  {}

  // nil
  Expr_TAG()
    : f_symb(NIL)
    , f_lhs(*this)
    , f_rhs(*this)
  {}

} Expr;

typedef Expr* Expr_ptr;
typedef vector<Expr_ptr> Exprs;

typedef struct {
  // ELF hash (cfr. General Hash Functions by
  long operator() (const Expr& k) const
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

// typedef Literal* Literal_ptr;
// typedef vector<Literal_ptr> Literals;

typedef struct {
  long operator() (const Atom& k) const
  {
    return 0;
  }
} AtomHash;

typedef struct {
 bool operator() (const Atom& x, const Atom& y) const
  { return x == y; }
} AtomEq;

typedef unordered_set<Expr, ExprHash, ExprEq> ExprPool;
typedef pair<ExprPool::iterator, bool> ExprPoolHit;

typedef unordered_set<Atom, AtomHash, AtomEq> AtomPool;
typedef pair<AtomPool::iterator, bool> AtomPoolHit;

class IVarType {
public:
  virtual Expr get_name() const =0;
  virtual bool is_boolean() const =0;
  virtual bool is_intRange() const =0;
  virtual bool is_intEnum() const =0;
  virtual bool is_symb_enum() const =0;
  virtual bool is_mixed_enum() const =0;
  virtual bool is_instance() const =0;
};
typedef IVarType* IVarType_ptr;

class IModule {
public:
  virtual bool is_main() const =0;
  virtual const Expr& get_name() const =0;

  virtual const Exprs& get_formalParams() =0;
  virtual void add_formalParam(Expr& identifier) =0;

  // virtual const ISADeclarations& get_isaDecls() =0;
  // virtual IModule& operator+=(ISADeclaration& identifier) =0;

  virtual const Variables& get_localVars() const =0;
  virtual void add_localVar(IVariable& var) =0;
};

typedef IModule* IModule_ptr;
typedef vector<IModule_ptr> Modules;

class IVariable {
public:
  virtual const Expr& get_fqdn() const =0;

  virtual const IModule& get_owner() const =0;
  virtual const Expr& get_name() const =0;

  virtual const IVarType& get_type() const =0;
};
typedef IVariable* IVariable_ptr;

class IModel {
public:
  virtual const string& get_origin() const =0;
  virtual const Modules& get_modules() const =0;
  virtual IModel& operator+=(IModule& module) =0;
};

typedef set<Expr, ExprEq> EnumLiterals;
class EnumType : public IVarType {
  friend class TypeRegister;
  EnumType() {}

  EnumLiterals f_literals;

public:
  bool is_boolean() const
  { return false; }

  bool is_intRange() const
  { return false; }

  bool is_intEnum() const
  { return false; }

  bool is_symb_enum() const
  { return false; }

  bool is_mixed_enum() const
  { return false; }

  bool is_instance() const
  { return false; }

  // Expr get_name() const
  // { return  ExprMgr::INSTANCE().make_enum(*this); }

  const EnumLiterals& get_literals() const
  { return f_literals; }

};

class ExprMgr;
typedef ExprMgr* ExprMgr_ptr;

class ExprMgr  {
  typedef ExprMgr* ExprMgr_ptr;

public:
  static ExprMgr& INSTANCE() {
    if (! f_instance) f_instance = new ExprMgr();
    return (*f_instance);
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

  inline const Expr& make_enum(EnumType& enumeration)
  {
    Expr_ptr res = const_cast<Expr_ptr> (&nil);
    const EnumLiterals& literals = enumeration.get_literals();

    /* reverse iteration */
    for (EnumLiterals::reverse_iterator eye = literals.rbegin();
         eye != literals.rend(); eye ++) {
      res = const_cast<Expr_ptr>(&make_expr(COMMA, *eye, *res));
    }

    // head node
    res = const_cast<Expr_ptr>(&make_expr(SET, *res, nil));

    return *res;
  }

  inline const Expr& make_boolean()
  {
    AtomPoolHit ah = (f_atom_pool.insert(Atom("boolean")));
    if (ah.second) {
      logger << "Added new atom to pool" << *ah.first;
    }

    return make_expr(*ah.first);
  }

  inline const Expr& make_identifier(const Atom atom)
  {
    AtomPoolHit ah = (f_atom_pool.insert(Atom(atom)));
    if (ah.second) {
      logger << "Added new atom to pool" << *ah.first;
    }

    return make_expr(*ah.first);
  }

protected:
  ExprMgr()
    :  f_expr_pool()
    ,  f_atom_pool()
  {
    // setup pre-defined known identifiers
    f_expr_pool.insert(make_identifier(Atom("boolean")));

  }

private:
  static ExprMgr_ptr f_instance;

  /* low-level services */
  inline const Expr& make_expr(ExprType et, const Expr& a, const Expr& b)
  {
    ExprPoolHit eh = (f_expr_pool.insert(Expr(et, a, b)));
    if (eh.second) {
      logger << "Added new expr to pool" << *eh.first;
    }

    return *eh.first;
  }

  inline const Expr& make_expr(const Atom& atom)
  {
    ExprPoolHit eh = (f_expr_pool.insert(Expr(atom)));
    if (eh.second) {
      logger << "Added new expr to pool" << *eh.first;
    }

    return *eh.first;
  }

  /* shared pools */
  ExprPool f_expr_pool;
  AtomPool f_atom_pool;
};

// static initialization
ExprMgr_ptr ExprMgr::f_instance = NULL;

#endif
