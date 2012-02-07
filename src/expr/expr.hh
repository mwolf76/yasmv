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

  /* word-related operators */
  CONCAT, COUNT,

  /* casts */
  CAST_INT, CAST_BOOL, CAST_SIGNED, CAST_UNSIGNED,

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

  /* set exprs */
  MEMBER, UNION,

  /* utils */
  COMMA, SET,

} ExprType;

// using STL string as basic atom class
typedef string Atom;
typedef Atom* Atom_ptr;

typedef struct Expr_TAG {
  ExprType f_symb;
  Expr_TAG* f_ctx;

  union {
    struct {
      struct Expr_TAG* f_lhs;
      struct Expr_TAG* f_rhs;
    };

    struct {
      /* 64 bit */
      unsigned long long f_ull;
      unsigned short f_wsize; // words only
    };

    struct {
      const Atom_ptr f_atom;
    };
  };

  // NOTE: there is no chance of getting the wrong ctor called as
  // any of them has a different number of paramters. (sweet)
  inline Expr_TAG()
    : f_symb(NIL)
    , f_ctx(NULL)
    , f_lhs(NULL)
    , f_rhs(NULL)
  {}

  // identifiers
  inline Expr_TAG(const Atom& atom)
    : f_symb(IDENT)
    , f_atom(const_cast<const Atom_ptr> (&atom))
  {}

  // word constants
  inline Expr_TAG(ExprType symb,
                  short wsize,
                  long long value)
    : f_symb(symb)
    , f_ull(value)
    , f_wsize(wsize)
  { assert ((symb == UWCONST) || (symb == SWCONST)); }

  // int constants
  inline Expr_TAG(ExprType symb,
                  long long value)
    : f_symb(symb)
    , f_ull(value)
  { assert (symb == ICONST); }

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

// system-wide expr
typedef Expr* Expr_ptr;

typedef vector<Expr_ptr> Exprs;
typedef set<Expr_ptr> EnumLiterals;

// TODO: move all these exception classes somewhere else!!
class UnsupportedOperatorException : public exception {
  virtual const char* what() const throw() {
    return "Unsupported operator";
  }
};


// for logging purposes
ostream& operator<<(ostream& os, const Expr_ptr t);

class ExprMgr;
typedef ExprMgr* ExprMgr_ptr;

class BadWordConstException {
public:
  BadWordConstException(const char* msg)
    : f_msg(msg)
  {}

  virtual const char* what() const throw() {
    return f_msg;
  }

protected:
  const char* f_msg;
};

class ExprMgr  {
public:
  static ExprMgr& INSTANCE()
  {
    if (! f_instance)
        f_instance = new ExprMgr();

    return (*f_instance);
  }

  // -- makers ----------------------------------------------------------------

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

  /* word-related and casts */
  inline Expr_ptr make_concat(Expr_ptr a, Expr_ptr b)
  { return make_expr(CONCAT, a, b); }

  inline Expr_ptr make_toint(Expr_ptr expr)
  { return make_expr(CAST_INT, expr, NULL); }

  inline Expr_ptr make_bool(Expr_ptr expr)
  { return make_expr(CAST_BOOL, expr, NULL); }

  inline Expr_ptr make_word1(Expr_ptr expr)
  { throw UnsupportedOperatorException(); }

  inline Expr_ptr make_signed(Expr_ptr expr)
  { return make_expr(CAST_SIGNED, expr, NULL); }

  inline Expr_ptr make_unsigned(Expr_ptr expr)
  { return make_expr(CAST_UNSIGNED, expr, NULL); }

  inline Expr_ptr make_count(Expr_ptr expr)
  { return make_expr(COUNT, expr, NULL); }

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

  inline Expr_ptr make_union(Expr_ptr a, Expr_ptr b)
  { return make_expr(UNION, a, b); }

  inline Expr_ptr make_member(Expr_ptr a, Expr_ptr b)
  { return make_expr(MEMBER, a, b); }

  inline Expr_ptr make_cond(Expr_ptr a, Expr_ptr b)
  { return make_expr(COND, a, b); }

  inline Expr_ptr make_ite(Expr_ptr a, Expr_ptr b)
  { return make_expr(ITE, a, b); }

  /* leaves */
  inline Expr_ptr make_iconst(unsigned long long value)
  { return __make_expr(f_expr_pool.insert(Expr(ICONST, value))); }

  inline Expr_ptr make_uwconst(unsigned short wsize, unsigned long long value)
  { return __make_expr(f_expr_pool.insert(Expr(UWCONST, wsize, value))); }

  inline Expr_ptr make_swconst(unsigned short wsize, unsigned long long value)
  { return __make_expr(f_expr_pool.insert(Expr(SWCONST, wsize, value))); }

  inline Expr_ptr make_enum(const EnumLiterals& literals)
  {
    Expr_ptr res = NULL;

    /* reverse iteration */
    for (EnumLiterals::reverse_iterator eye = literals.rbegin();
         eye != literals.rend(); eye ++) {
      if (!res) res = (*eye);
      else res = make_expr(COMMA, (*eye), res);
    }

    return make_expr(SET, res, NULL);
  }

  inline Expr_ptr make_dot(Expr_ptr a, Expr_ptr b)
  { return make_expr(DOT, a, b); }

  inline Expr_ptr make_subscript(Expr_ptr a, Expr_ptr b)
  { return make_expr(SUBSCRIPT, a, b); }

  inline Expr_ptr make_range(Expr_ptr a, Expr_ptr b)
  { return make_expr(RANGE, a, b);  }

  /* predefined identifiers */
  inline Expr_ptr make_temporal() const
  { return temporal_expr; }

  inline Expr_ptr make_boolean() const
  { return bool_expr; }

  inline Expr_ptr make_const() const
  { return const_expr; }

  inline Expr_ptr make_integer() const
  { return integer_expr; }

  inline Expr_ptr make_main() const
  { return main_expr; }

  inline Expr_ptr make_uword(Expr_ptr size)
  { return make_expr(SUBSCRIPT, uword_expr, size); }

  inline Expr_ptr make_sword(Expr_ptr size)
  { return make_expr(SUBSCRIPT, sword_expr, size); }

  // Here a bit of magic occurs, so it's better to keep a note: this
  // method is used by the parser to build identifier nodes.  The
  // function is fed with a const char* coming from the Lexer, an Atom
  // object (which is in fact a std::string) is built on-the-fly and
  // used to search the atom pool. The atom resulting from the search
  // is always the one stored in the pool. The auto atom object,
  // however gets destroyed as it gets out of scope, so no leak occurs.
  inline Expr_ptr make_identifier(Atom atom)
  {
    AtomPoolHit ah = (f_atom_pool.insert(atom));
    if (ah.second) {
      AtomPool::const_pointer atom = & (*ah.first);
      logger << "Added new atom to pool: '" << (*atom) << "'" << endl;
    }

    return make_expr(*ah.first);
  }

  inline Expr_ptr make_wconst(Atom atom)
  {
    regex wconst_rx("0(u|s)(b|d|o|h|)(/d+)_(.+)");
    cmatch match;

    regex_match(atom.c_str(), match, wconst_rx);
    assert (match.size() == 4);

    string sign_flag(match[0]);
    string type_flag(match[1]);
    string size_field(match[2]);
    string wliteral(match[3]);
    bool is_signed = (sign_flag == "s");
    unsigned short wsize = atoi(size_field.c_str());

    unsigned long long value = 0ULL;

    if (match[1] == "b") {
      if (wsize != wliteral.size())
        throw BadWordConstException("Boolean word constants must match the word size.");

      int i;
      for (i = wliteral.size() -1;
           i >= (is_signed) ? 1 : 0; -- i) {
        value = 2 * value + wliteral[i];
      }

      // MSB is -2^(wsize)
      if ((is_signed) && (wliteral[0] == '1')) {
        value -= pow2(i);
      }

    }

    // NEG not supported here
    else if (match[1] == "d") {
      value = strtoll(wliteral.c_str(), NULL, 10);
    }
    else if (match[1] == "o") {
      value = strtoll(wliteral.c_str(), NULL, 8);
    }
    else if (match[1] == "h") {
      value = strtoll(wliteral.c_str(), NULL, 16);
    }
    else assert(0);

    // range check
    if (value >= pow2(wsize - (is_signed ? 1 : 0))) {
      throw BadWordConstException("Decimal value not representable with this word size.");
    }

    return is_signed ? make_swconst( wsize, value )
      : make_uwconst(wsize, value );
  }

  inline Expr_ptr make_hex_const(Atom atom)
  { return make_iconst( strtoll(atom.c_str(), NULL, 16)); }

  inline Expr_ptr make_dec_const(Atom atom)
  { return make_iconst( strtoll(atom.c_str(), NULL, 10)); }

  inline Expr_ptr make_oct_const(Atom atom)
  { return make_iconst( strtoll(atom.c_str(), NULL, 8)); }

  // -- is-a predicates -------------------------------------------------------
  inline bool is_identifier(const Expr_ptr expr) const {
    assert(expr);
    return expr->f_symb == IDENT;
  }

  inline bool is_numeric(const Expr_ptr expr) const {
    assert(expr);
    return (expr->f_symb == ICONST)
      || (expr->f_symb == UWCONST)
      || (expr->f_symb == SWCONST) ;
  }

  inline Expr_ptr lvalue_varname(const Expr_ptr expr) const {
    assert(expr);
    if (expr->f_symb == IDENT)
      return expr;

    if ((expr->f_symb == INIT) ||
        (expr->f_symb == NEXT))
      return expr->f_lhs;

    return NULL;
  }

protected:
  ExprMgr()
  {
    const Atom_ptr atom_temporal = new Atom("temporal");
    const ExprPoolHit temporal_hit = f_expr_pool.insert(*atom_temporal);
    assert(temporal_hit.second); // it has to be true
    temporal_expr = const_cast<Expr_ptr> (& (*temporal_hit.first));

    const Atom_ptr atom_integer = new Atom("integer");
    const ExprPoolHit integer_hit = f_expr_pool.insert(*atom_integer);
    assert(integer_hit.second); // it has to be true
    integer_expr = const_cast<Expr_ptr> (& (*integer_hit.first));

    const Atom_ptr atom_boolean = new Atom("boolean");
    const ExprPoolHit bool_hit = f_expr_pool.insert(*atom_boolean);
    assert(bool_hit.second); // it has to be true
    bool_expr = const_cast<Expr_ptr> (& (*bool_hit.first));

    const Atom_ptr atom_main = new Atom("main");
    const ExprPoolHit main_hit = f_expr_pool.insert(*atom_main);
    assert(main_hit.second); // it has to be true
    main_expr = const_cast<Expr_ptr> (& (*main_hit.first));

    const Atom_ptr atom_const = new Atom("const");
    const ExprPoolHit const_hit = f_expr_pool.insert(*atom_const);
    assert(const_hit.second); // it has to be true
    const_expr = const_cast<Expr_ptr> (& (*const_hit.first));

    const Atom_ptr atom_uword = new Atom("unsigned word");
    const ExprPoolHit uword_hit = f_expr_pool.insert(*atom_uword);
    assert(uword_hit.second); // it has to be true
    uword_expr = const_cast<Expr_ptr> (& (*uword_hit.first));

    const Atom_ptr atom_sword = new Atom("signed word");
    const ExprPoolHit sword_hit = f_expr_pool.insert(*atom_sword);
    assert(sword_hit.second); // it has to be true
    sword_expr = const_cast<Expr_ptr> (& (*sword_hit.first));
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

  // utils
  inline unsigned long long pow2(unsigned exp) {
    unsigned long long res = 1;
    for (unsigned i = exp; i; -- i) {
      res *= 2;
    }
    return res;
  }

  /* builtins */
  Expr_ptr temporal_expr;
  Expr_ptr integer_expr;
  Expr_ptr bool_expr;
  Expr_ptr const_expr;
  Expr_ptr main_expr;
  Expr_ptr uword_expr;
  Expr_ptr sword_expr;

  /* shared pools */
  ExprPool f_expr_pool;
  AtomPool f_atom_pool;
};

class FQExpr {
  Expr_ptr f_ctx;
  Expr_ptr f_expr;

public:
  FQExpr(Expr_ptr ctx, Expr_ptr expr)
    : f_ctx(ctx)
    , f_expr(expr)
  {}

  FQExpr(Expr_ptr expr)
    : f_ctx(ExprMgr::INSTANCE().make_main()) // default ctx
    , f_expr(expr)
  {}

  FQExpr(const FQExpr& fqexpr)
    : f_ctx(fqexpr.ctx())
    , f_expr(fqexpr.expr())
  {}

  inline const Expr_ptr& ctx() const
  { return f_ctx; }

  inline const Expr_ptr& expr() const
  { return f_expr; }

  inline bool operator==(const FQExpr& other) const
  {
    return this->f_ctx == other.ctx() &&
      this->f_expr == other.expr();
  }

  // TODO: hash func
  inline unsigned long hash() const
  { return 0; }

};
typedef FQExpr* FQExpr_ptr;

struct fqexpr_hash {
  inline long operator() (const FQExpr& x) const
  { return x.hash(); }
};

struct fqexpr_eq {
  inline bool operator() (const FQExpr &x,
                          const FQExpr &y) const
  { return x == y; }
};

typedef vector<FQExpr> FQExprs;

class ISymbol;
typedef ISymbol* ISymbol_ptr;
typedef unordered_map<Expr_ptr, ISymbol_ptr, PtrHash, PtrEq> Symbols;

class IConstant;
typedef IConstant* IConstant_ptr;
typedef unordered_map<Expr_ptr, IConstant_ptr, PtrHash, PtrEq> Constants;

class IVariable;
typedef IVariable* IVariable_ptr;
typedef unordered_map<Expr_ptr, IVariable_ptr, PtrHash, PtrEq> Variables;

class IDefine;
typedef IDefine* IDefine_ptr;
typedef unordered_map<Expr_ptr, IDefine_ptr, PtrHash, PtrEq> Defines;

class IAssign;
typedef IAssign* IAssign_ptr;
typedef unordered_set<IAssign_ptr, PtrHash, PtrEq> Assigns;

class IModule;
typedef IModule* IModule_ptr;
typedef unordered_map<Expr_ptr, IModule_ptr, PtrHash, PtrEq> Modules;

#endif
