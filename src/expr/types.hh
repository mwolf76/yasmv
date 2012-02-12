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
 * @file types.hh
 *
 * @brief Type system classes
 *
 */

#ifndef TYPES_H
#define TYPES_H

#include <common.hh>

#include <expr.hh>
#include <expr_mgr.hh>

// Basic Type class. Is.. nothing.
class Type {
public:
  virtual const Expr_ptr get_repr() const
  { return NULL; }

};
typedef Type* Type_ptr;
const static Type nilType; // ??

// -- Supported data types: boolean, ranged integers, pure-int enums,
// .. symbolic enums, mixed enums, words and signed words up to 32 bits
// .. wide, module instances.
class BooleanType : public Type {
  friend class TypeMgr;
  ExprMgr& f_em;

  Expr_ptr f_repr;

protected:
  BooleanType()
    : f_em(ExprMgr::INSTANCE())
    , f_repr(f_em.make_boolean())
  {}

public:
  const Expr_ptr get_repr() const
  { return f_repr; }
};

class TemporalType : public Type {
  friend class TypeMgr;
  ExprMgr& f_em;

  Expr_ptr f_repr;

protected:
  TemporalType()
    : f_em(ExprMgr::INSTANCE())
    , f_repr(f_em.make_temporal())
  {}

public:
  const Expr_ptr get_repr() const
  { return f_repr; }
};

class IntegerType : public Type {
  friend class TypeMgr;
  ExprMgr& f_em;

  IntegerType()
    : f_em(ExprMgr::INSTANCE())
  {}

public:
  const Expr_ptr get_repr() const
  { return f_em.make_integer(); }
};

class IntRangeType : public Type {
  friend class TypeMgr;
  ExprMgr& f_em;

  const Expr_ptr f_min;
  const Expr_ptr f_max;

  IntRangeType(const Expr_ptr min, const Expr_ptr max)
    : f_em(ExprMgr::INSTANCE())
    , f_min(min)
    , f_max(max)
  {}

public:
  inline const Expr_ptr get_min() const
  { return f_min; }

  inline const Expr_ptr get_max() const
  { return f_max; }

  const Expr_ptr get_repr() const
  { return f_em.make_range(f_min, f_max); }
};


class EnumType : public Type {
  friend class TypeMgr;
  ExprMgr& f_em;

  EnumType()
    : f_em(ExprMgr::INSTANCE())
  {}

  EnumLiterals f_literals;

public:
  const Expr_ptr get_repr() const
  { return f_em.make_enum(f_literals); }

  const EnumLiterals& get_literals() const
  { return f_literals; }

  void add_literal(Expr& lit)
  { f_literals.insert(&lit); }

  bool has_symbs() const;
  bool has_numbers() const;
};

class Word : public Type {
  friend class TypeMgr;
  ExprMgr& f_em;

  unsigned f_size;
  bool f_is_signed;

  Word(unsigned size, bool is_signed=false)
    : f_em(ExprMgr::INSTANCE())
    , f_size(size)
    , f_is_signed(is_signed)
  {}

public:
  const Expr_ptr get_repr() const
  {
    return (!f_is_signed)
      ? f_em.make_uword(f_em.make_iconst(f_size))
      : f_em.make_sword(f_em.make_iconst(f_size));
  }

  unsigned get_size() const
  { return f_size; }

  bool is_signed() const
  { return f_is_signed; }

};

class Instance : public Type {
public:
  friend class TypeMgr;

  const Expr_ptr f_identifier;
  IModule_ptr f_module;
  Exprs f_params;

  Instance(Expr* identifier)
    : f_identifier(identifier)
    , f_module(NULL)
    , f_params()
  {}

  void add_param(const Expr_ptr expr)
  { f_params.push_back(expr); }

  const Exprs& get_params() const
  { return f_params; }

  const Expr_ptr get_module_name() const
  { return f_identifier; }

  const IModule_ptr get_module() const
  { assert(f_module); return f_module; }

  void set_module(IModule_ptr module)
  { assert(!f_module); assert(module); f_module = module; }

};
typedef Instance* Instance_ptr;

typedef vector<Expr> Literals;

// the same here??
typedef unordered_map<FQExpr, Type_ptr, fqexpr_hash, fqexpr_eq> TypeMap;
typedef pair<TypeMap::iterator, bool> TypeHit;

class TypeMgr;
typedef TypeMgr* TypeMgr_ptr;

class TypeMgr {
public:
  static TypeMgr& INSTANCE() {
    if (! f_instance) f_instance = new TypeMgr();
    return (*f_instance);
  }

  inline const Type_ptr get_type(const FQExpr& fqexpr) const
  {
    TypeMap::const_iterator eye = f_map.find(fqexpr);
    Type_ptr res = NULL;

    // cache miss
    if (eye == f_map.end()) return NULL;

    return res;
  }

  inline void set_type(const FQExpr fqexpr, const Type_ptr tp)
  { f_map[ fqexpr ] = tp; }

  inline const Type_ptr find_const()
  { return f_register[ FQExpr(f_em.make_const()) ]; }

  inline const Type_ptr find_boolean()
  { return f_register[ FQExpr(f_em.make_boolean()) ]; }

  inline const Type_ptr find_integer()
  { return f_register[ FQExpr(f_em.make_integer()) ]; }

  // this type is reserved to tell temporal boolean exprs properties
  // from boolean propositions
  inline const Type_ptr find_temporal()
  {
    return f_register[ FQExpr(f_em.make_temporal()) ];
  }

  inline const Type_ptr find_enum(Expr_ptr ctx, EnumLiterals& lits)
  { return f_register[ FQExpr(ctx, f_em.make_enum(lits)) ]; }


  const Type_ptr find_uword(Expr_ptr size)
  { return f_register[ FQExpr(f_em.make_uword(size)) ]; }

  const Type_ptr find_sword(Expr_ptr size)
  { return f_register[ FQExpr (f_em.make_sword(size)) ]; }

  const Type_ptr find_range(const Expr_ptr from, const Expr_ptr to)
  { return f_register[ FQExpr (f_em.make_range(from, to)) ]; }

  const Type_ptr find_instance(Expr_ptr identifier)
  {
    Type_ptr inst = new Instance(identifier);
    TypeHit hit =
      f_register.insert( make_pair( FQExpr(identifier),
                                    inst));
    if (hit.second) {
      logger << "Added instance of module '"
             << identifier
             << "' to type register"
             << endl;
    }

    TypeMap::pointer p = &(*hit.first);
    return p->second;
  }

  inline bool is_temporal(const Type_ptr tp) const
  { return is_boolean(tp) || NULL != dynamic_cast <const TemporalType*> (tp); }

  inline bool is_boolean(const Type_ptr tp) const
  { return NULL != dynamic_cast <const BooleanType*> (tp); }

  inline bool is_intRange(const Type_ptr tp) const
  { return NULL != dynamic_cast <const IntRangeType*> (tp); }

  inline bool is_intEnum(const Type_ptr tp) const
  {
    EnumType* tmp;
    if (! (tmp = dynamic_cast <EnumType*> (tp))) {
      return false;
    }

    return ! tmp->has_symbs();
  }

  inline bool is_integer(const Type_ptr tp) const
  {
    return
      is_intRange(tp) ||
      is_intEnum(tp)  ||
      (NULL != dynamic_cast<const IntegerType*>(tp));
  }

  inline bool is_symbEnum(const Type_ptr tp) const
  {
    EnumType* tmp;
    if (! (tmp = dynamic_cast <EnumType*> (tp))) {
      return false;
    }

    return ! tmp->has_numbers();
  }

  inline bool is_mixed_enum(const Type_ptr tp) const
  {
    EnumType* tmp;

    if (! (tmp = dynamic_cast <EnumType*> (tp))) {
      return false;
    }

    return
      tmp->has_symbs() &&
      tmp->has_numbers();
  }

  inline bool is_word(const Type_ptr tp) const
  { return (NULL != dynamic_cast <Word*> (tp)); }

  inline bool is_instance(const Type_ptr tp) const
  { return (NULL != dynamic_cast <Instance*> (tp)); }


protected:
  TypeMgr()
    : f_register()
    , f_map()
    , f_em(ExprMgr::INSTANCE())
  {
    // register predefined types
    register_type( FQExpr( f_em.make_boolean() ),
                   new BooleanType());

    register_type( FQExpr( f_em.make_integer() ),
                   new IntegerType());

    register_type( FQExpr( f_em.make_temporal() ),
                   new TemporalType());
  }

private:
  static TypeMgr_ptr f_instance;

  /* low-level services */
  void register_type(const FQExpr fqexpr, Type_ptr vtype)
  { f_register [ fqexpr ] = vtype; }

  /* local data */
  TypeMap f_register;
  TypeMap f_map;

  // ref to expr manager
  ExprMgr& f_em;
};
ostream& operator<<(ostream& os, Type_ptr tp);

// -- analyzer related exception hierarchy
class AnalyzerException : public exception {
public:
  virtual const char* what() const throw() =0;
};

class BadContext : public AnalyzerException {
  Expr_ptr f_ctx;

public:
  BadContext(Expr_ptr ctx)
    : f_ctx(ctx)
  {}

  const char* what() const throw() {
    ostringstream oss;

    oss << "Bad Context: " << f_ctx;
    return oss.str().c_str();
  }
};

class BadParams : public AnalyzerException {
  Expr_ptr f_moduleName;
  int f_modl_params_num;
  int f_inst_params_num;

public:
  BadParams(Expr_ptr module, int params_num, int actual_num)
    : f_moduleName(module)
    , f_modl_params_num(params_num)
    , f_inst_params_num(actual_num)
  {}

  const char* what() const throw() {
    ostringstream oss;

    oss << "BadParams: " << f_moduleName
        << " expected " << f_modl_params_num
        << " got " << f_inst_params_num;
    return oss.str().c_str();
  }
};

class UnresolvedSymbol : public AnalyzerException {
  Expr_ptr f_ctx;
  Expr_ptr f_expr;

public:
  UnresolvedSymbol(Expr_ptr ctx, Expr_ptr expr)
    : f_ctx(ctx)
    , f_expr(expr)
  {}

  const char* what() const throw() {
    ostringstream oss;

    oss << "Unresolved symbol: " << f_ctx << "::" << f_expr;
    return oss.str().c_str();
  }
};

// when a numer of types were allowed and none of them was given
class BadType : public AnalyzerException {
  Expr_ptr f_got;
  Exprs f_allowed;
  Expr_ptr f_body;

public:

  // exactly one type allowed
  BadType(Expr_ptr got, Expr_ptr allowed, Expr_ptr body)
    : f_got(got)
    , f_allowed()
    , f_body(body)
  {
    f_allowed.push_back(allowed);
  }

  // multiple types allowed shortcut
  BadType(Expr_ptr got, Exprs allowed, Expr_ptr body)
    : f_got(got)
    , f_allowed(allowed)
    , f_body(body)
  {}

  ~BadType() throw()
  {}

  const char* what() const throw() {
    ostringstream oss;

    oss << "BadType: got " << f_got
        << " expected ";

    Exprs::const_iterator eye = f_allowed.begin();
    do
      {
        oss << (*eye); eye ++;
        if (eye != f_allowed.end()) oss << ", ";
      } while (eye != f_allowed.end());

    return oss.str().c_str();
  }
};


class NotAnLvalue: public AnalyzerException {
  Expr_ptr f_got;

public:
  NotAnLvalue(Expr_ptr got)
    : f_got(got)
  {}

  const char* what() const throw() {
    ostringstream oss;

    oss << "NotAnLValue: " << f_got;
    return oss.str().c_str();
  }
};


class ResolutionException
 : public AnalyzerException {

  Expr_ptr f_expr;

public:
  ResolutionException(Expr_ptr expr)
    : f_expr(expr)
  {}

  const char* what() const throw() {
    ostringstream oss;

    oss << "UnresolvedSymbol: " << f_expr;
    return oss.str().c_str();
  }

};

ostream& operator<<(ostream& os, AnalyzerException& ae);


#endif
