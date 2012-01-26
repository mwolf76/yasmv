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
  virtual const string get_repr() const
  { return "<NullType>"; }

  virtual bool is_boolean() const
  { return false; }

  virtual bool is_intRange() const
  { return false; }

  virtual bool is_intEnum() const
  { return false; }

  virtual bool is_symb_enum() const
  { return false; }

  virtual bool is_mixed_enum() const
  { return false; }

  virtual bool is_instance() const
  { return false; }
};
typedef Type* Type_ptr;
const static Type nilType;

// -- Supported data types: boolean, ranged integers, pure-int enums,
// .. symbolic enums, mixed enums, words and signed words up to 32 bits
// .. wide, module instances.
class BooleanType : public Type {
  friend class TypeMgr;
  BooleanType() {}

public:
  bool is_boolean() const
  { return true; }

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

  const string get_repr() const
  { return "boolean"; }
};

class IntRangeType : public Type {
  Expr f_min;
  Expr f_max;

  IntRangeType(Expr min, Expr max) {
    f_min = min;
    f_max = max;
  }

public:
  inline const Expr& get_min() const
  { return f_min; }

  inline const Expr& get_max() const
  { return f_max; }

  const string get_repr() const
  {
    ostringstream oss;
    oss << "[" << get_min() << ".." << get_max() << "]";
    return oss.str();
  }
};


typedef set<Expr*> EnumLiterals;
class EnumType : public Type {
  friend class TypeMgr;
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

  const string get_repr() const
  {
    ostringstream oss;
    EnumLiterals::iterator eye;

    oss << "{ ";
    eye = f_literals.begin();
    while (eye != f_literals.end()) {
      oss << (**eye);
      eye ++;
      if (eye != f_literals.begin()) {
        oss << ", ";
      }
    }
    oss << "}";

    return oss.str();
  }

  const EnumLiterals& get_literals() const
  { return f_literals; }

  void add_literal(Expr& lit)
  { f_literals.insert(&lit); }
};

class Module;
typedef Module* Module_ptr;

class Instance : public Type {
public:
  friend class TypeMgr;

  const Expr& f_identifier;
  Module_ptr f_module;
  Exprs f_params;

  // eager binding (not used by the parser)
  Instance(Module& module, Exprs params)
    : f_identifier(nil)
    , f_module(&module)
    , f_params(params)
  {}

  // lazy binding
  Instance(const Expr& identifier)
    : f_identifier(identifier)
    , f_module(NULL)
    , f_params()
  {}

  // const Expr& get_name() const
  // { return f_identifier; }

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
  { return true; }

  void add_param(Expr& expr)
  { f_params.push_back(&expr); }
};

typedef vector<Expr> Literals;

typedef unordered_map<Expr, Type, ExprHash, ExprEq> TypeRegister;
typedef pair<TypeRegister::iterator, bool> TypeHit;

class TypeMgr;
typedef TypeMgr* TypeMgr_ptr;

class TypeMgr {
public:
  static TypeMgr& INSTANCE() {
    if (! f_instance) f_instance = new TypeMgr();
    return (*f_instance);
  }

  // REVIEW ME
  const Type_ptr find_boolean()
  { return &f_register[ ExprMgr::INSTANCE().make_boolean() ]; }

  // REVIEW ME
  const Type_ptr find_uword(Expr& size)
  { return const_cast <const Type_ptr> (&nilType); }

  // REVIEW ME
  const Type_ptr find_sword(Expr& size)
  { return const_cast <const Type_ptr> (&nilType); }

  const Type_ptr find_range(const Expr& from, const Expr& to)
  { return const_cast <const Type_ptr> (&nilType); }

  const Type_ptr find_instance(const Expr& identifier)
  {
    Instance tmp(identifier);
    TypeHit hit = f_register.insert(make_pair(identifier, tmp));
    if (hit.second) {
      logger << "Added instance of module '" << identifier << "' to type register" << endl;
    }

    TypeRegister::pointer p = &(*hit.first);
    return &(p->second);
  }

protected:
  TypeMgr():
    f_register()
  {
    /* boolean is the only predefined type. Any other type will be
       declared by the user. */
    register_type(ExprMgr::INSTANCE().make_boolean(),
                  BooleanType());
  }

private:
  static TypeMgr_ptr f_instance;

  /* low-level services */
  void register_type(const Expr type_name, Type vtype)
  { f_register.insert(make_pair(type_name, vtype)); }

  /* local data */
  TypeRegister f_register;
};


#endif
