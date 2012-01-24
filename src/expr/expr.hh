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

typedef IModule* IModule_ptr;
typedef vector<IModule_ptr> Modules;

class IVariable {
public:
  virtual const Expr& get_name() const =0;
  virtual const IVarType& get_type() const =0;
};

class IDefine {
public:
  virtual const Expr& get_name() const =0;
  virtual const Expr& get_body() const =0;
};

class IAssign {
public:
  virtual const Expr& get_name() const =0;
  virtual const Expr& get_body() const =0;
};

class IModel {
public:
  virtual const Modules& get_modules() const =0;
  virtual void add_module(IModule& module) =0;
};

typedef set<Expr*> EnumLiterals;
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

  void add_literal(Expr& lit)
  { f_literals.insert(&lit); }
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

  // Pointer to eXpression to simplify expr manipulation code
# define  PX(expr) (const_cast<Expr_ptr>(&(expr)))

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

  inline const Expr& make_enum(EnumType& enumeration)
  {
    Expr_ptr res = PX(nil);
    const EnumLiterals& literals = enumeration.get_literals();

    /* reverse iteration */
    for (EnumLiterals::reverse_iterator eye = literals.rbegin();
         eye != literals.rend(); eye ++) {
      res = PX(make_expr(COMMA, (**eye), *res));
    }

    return make_expr(SET, *res, nil);
  }

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
