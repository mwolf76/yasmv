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
 * @file model.hh
 *
 * @brief Hierarchical modeling entities
 *
 * This module contains definitions and services that implement an
 * optimized storage for expressions. Expressions are stored in a
 * Directed Acyclic Graph (DAG) for data sharing.
 *
 *
 */

#ifndef MODEL_H
#define MODEL_H
#include <common.hh>
#include <expr.hh>

// -- interfaces --------------------------------------------------------------

class Module : public IModule {
  Expr f_name;
  Exprs f_formalParams;
  Variables f_localVars;

public:

  Module(const Expr name) :
    f_name(name),
    f_formalParams(),
    f_localVars() {}

  const Expr& get_name() const
  { return f_name; }

  const Exprs& get_formalParams() const
  { return f_formalParams; }

  void add_formalParam(Expr& identifier)
  { f_formalParams.push_back(&identifier); }

  const Variables& get_localVars() const
  { return f_localVars; }

  void add_localVar(IVariable& var)
  { f_localVars.push_back(&var); }
};

class Instance : public IVarType {
  friend class TypeRegister;

  const Expr* f_identifier;
  Module* f_module;
  Variables f_actualParams;

  // eager binding (not used by the parser)
  Instance(Module& module, Variables actualParams)
    : f_identifier(PX(ExprMgr::nil))
    , f_module(&module)
    , f_actualParams(actualParams)
  {}

  // lazy binding
  Instance(const Expr& identifier)
    : f_identifier(&identifier)
    , f_module(NULL)
    , f_actualParams()
  {}

  Expr get_name() const
  { return *f_identifier; }

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
};

class Variable : public IVariable {
  Expr f_name;
  Expr f_fqdn;

  IModule& f_owner;
  IVarType& f_type;

public:
  Variable(IModule& owner, const Expr name, IVarType& type)
    : f_owner(owner),
      f_type(type)
  {
    // f_fqdn = ExprMgr.INSTANCE().make_fqdn(owner.get_name(), name);
    f_name = name;
  }

  const IModule& get_owner() const
  { return f_owner; }

  const Expr& get_fqdn() const
  { return f_fqdn; }

  const Expr& get_name() const
  { return f_name; }
};

class StateVar : public Variable {
  StateVar (IModule& owner, const Expr name, IVarType& type_)
    : Variable(owner, name, type_)
  {}
};

class InputVar : public Variable {
  InputVar (IModule& owner, const Expr name, IVarType& type_)
    : Variable(owner, name, type_)
  {}
};

class FrozenVar: public Variable {
  FrozenVar (IModule& owner, const Expr name, IVarType& type_)
    : Variable(owner, name, type_)
  {}
};

class BooleanType : public IVarType {
  friend class TypeRegister;
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

  Expr get_name() const
  { return ExprMgr::INSTANCE().make_boolean(); }
};


// class IntRangeIterator {
// public:
//   IntRangeIterator(IVarType& vtype);

//   bool has_more() const;
//   Expr& next();
// };

class IntRangeType : public IVarType {
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

  Expr get_name() const
  {
    ostringstream oss;
    oss << "[" << get_min() << ".." << get_max() << "]";
    return oss.str();
  }
};

typedef vector<Expr> Literals;

// class EnumType : public IVarType {
//   Literals f_literals;

//   EnumType(Literals literals);
// };

// class InstanceType : public IVarType {
//   Expr f_moduleName;
//   Instance* f_binding; // reserved for type resolution

//   InstanceType(Expr moduleName) :
//     f_moduleName(moduleName),
//     f_binding(NULL) {}

// public:
//   Instance& get_instance();

//   bool is_unresolved() const;
// };

// class FiniteTypeIteratorException (Exception) {
// };

typedef unordered_map<Expr, IVarType_ptr, ExprHash, ExprEq> Expr2IVarTypeMap;
typedef pair<Expr2IVarTypeMap::iterator, bool> IVarTypeHit;

class TypeRegister {
  Expr2IVarTypeMap f_register;

public:
  TypeRegister():
    f_register()
  {
    /* boolean is the only predefined type. Any other type will be
     declared by the user. */
    register_type(ExprMgr::INSTANCE().make_boolean(),
                  new BooleanType());
  }

  // REVIEW ME
  const IVarType_ptr find_instance(const Expr& identifier)
  {
    Instance tmp(identifier);
    IVarTypeHit hit = f_register.insert(make_pair(identifier, &tmp));
    if (hit.second) {
      logger << "Added instance of module '" << identifier << "' to type register" << endl;
    }

    return f_register[identifier];
  }

private:
  void register_type(const Expr type_name, IVarType_ptr vtype)
  { f_register.insert(make_pair(type_name, vtype)); }

};

class Model : public IModel {
  Modules f_modules;

public:
  Model()
    : f_modules()
  {}

  const Modules& get_modules() const
  { return f_modules; }

  void add_module(IModule& module)
  { f_modules.push_back(&module); }

};

class ModelMgr;
typedef ModelMgr* ModelMgr_ptr;

class ModelMgr  {
  typedef ModelMgr* ModelMgr_ptr;

public:
  static ModelMgr& INSTANCE() {
    if (! f_instance) f_instance = new ModelMgr();
    return (*f_instance);
  }

protected:
  ModelMgr()
    : f_model()
  {}

private:
  static ModelMgr_ptr f_instance;

  /* low-level services */
  inline Model& get_model()
  { return f_model; }

  /* local data */
  Model f_model;
};

// static initialization
ModelMgr_ptr ModelMgr::f_instance = NULL;

#endif
