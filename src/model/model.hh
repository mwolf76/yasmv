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
  Defines f_localDefs;

  Exprs f_init;
  Exprs f_invar;
  Exprs f_trans;
  Exprs f_fair;
  Assigns f_assgn;

public:

  Module(const Expr name)
    : f_name(name)
    , f_formalParams()
    , f_localVars()
    , f_localDefs()
    , f_init()
    , f_invar()
    , f_trans()
    , f_fair()
    , f_assgn()
  {}

  const Expr& get_name() const
  { return f_name; }

  bool is_main() const
  { return f_name == ExprMgr::INSTANCE().make_main(); }

  const Exprs& get_formalParams() const
  { return f_formalParams; }

  void add_formalParam(Expr& identifier)
  { f_formalParams.push_back(&identifier); }

  const Variables& get_localVars() const
  { return f_localVars; }

  void add_localVar(IVariable& var)
  { f_localVars.push_back(&var); }

  const Defines& get_localDefs() const
  { return f_localDefs; }

  void add_localDef(IDefine& def)
  { f_localDefs.push_back(&def); }

  const Assigns& get_assign() const
  { return f_assgn; }

  void add_assign(IAssign& assign)
  { f_assgn.push_back(&assign); }

  const Exprs& get_init() const
  { return f_init; }

  void add_init(Expr& expr)
  { f_init.push_back(&expr); }

  const Exprs& get_invar() const
  { return f_invar; }

  void add_invar(Expr& expr)
  { f_invar.push_back(&expr); }

  const Exprs& get_trans() const
  { return f_trans; }

  void add_trans(Expr& expr)
  { f_trans.push_back(&expr); }

  const Exprs& get_fairness() const
  { return f_fair; }

  void add_fairness(Expr& expr)
  { f_fair.push_back(&expr); }

};

class Instance : public IVarType {
public:
  friend class TypeMgr;

  const Expr* f_identifier;
  Module* f_module;
  Exprs f_params;

  // eager binding (not used by the parser)
  Instance(Module& module, Exprs params)
    : f_identifier(PX(ExprMgr::nil))
    , f_module(&module)
    , f_params(params)
  {}

  // lazy binding
  Instance(const Expr& identifier)
    : f_identifier(&identifier)
    , f_module(NULL)
    , f_params()
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

  void add_param(Expr& expr)
  { f_params.push_back(&expr); }
};

class Variable : public IVariable {
  const Expr& f_name;
  IVarType& f_type;

public:
  Variable(const Expr& name, IVarType& type)
    : f_name(name)
    , f_type(type)
  {}

  const Expr& get_name() const
  { return f_name; }

  const IVarType& get_type() const
  { return f_type; }
};

class StateVar : public Variable {
public:
  StateVar (const Expr& name, IVarType& type_)
    : Variable(name, type_)
  {}
};

class InputVar : public Variable {
public:
  InputVar (const Expr& name, IVarType& type_)
    : Variable(name, type_)
  {}
};

class FrozenVar: public Variable {
public:
  FrozenVar (const Expr& name, IVarType& type_)
    : Variable(name, type_)
  {}
};

class Define : public IDefine {
  const Expr& f_name;
  const Expr& f_body;

public:
  Define(const Expr& name, const Expr& body)
    : f_name(f_name)
    , f_body(body)
  {}

  const Expr& get_name() const
  { return f_name; }

  const Expr& get_body() const
  { return f_body; }
};

class Assign : public IAssign {
  const Expr& f_name;
  const Expr& f_body;

public:
  Assign(const Expr& name, const Expr& body)
    : f_name(name)
    , f_body(body)
  {}

  const Expr& get_name() const
  { return f_name; }

  const Expr& get_body() const
  { return f_body; }
};

class BooleanType : public IVarType {
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

class TypeMgr;
typedef TypeMgr* TypeMgr_ptr;

class TypeMgr {
public:
  static TypeMgr& INSTANCE() {
    if (! f_instance) f_instance = new TypeMgr();
    return (*f_instance);
  }

  // REVIEW ME
  const IVarType_ptr find_boolean()
  { return f_register[ ExprMgr::INSTANCE().make_boolean() ]; }

  // REVIEW ME
  const IVarType_ptr find_uword(Expr& size)
  { return NULL; }

  // REVIEW ME
  const IVarType_ptr find_sword(Expr& size)
  { return NULL; }

  const IVarType_ptr find_range(const Expr& from, const Expr& to)
  { return NULL; }

  const IVarType_ptr find_instance(const Expr& identifier)
  {
    Instance tmp(identifier);
    IVarTypeHit hit = f_register.insert(make_pair(identifier, &tmp));
    if (hit.second) {
      logger << "Added instance of module '" << identifier << "' to type register" << endl;
    }

    return f_register[identifier];
  }

protected:
  TypeMgr():
    f_register()
  {
    /* boolean is the only predefined type. Any other type will be
     declared by the user. */
    register_type(ExprMgr::INSTANCE().make_boolean(),
                  new BooleanType());
  }

private:
  static TypeMgr_ptr f_instance;

  /* low-level services */
  void register_type(const Expr type_name, IVarType_ptr vtype)
  { f_register.insert(make_pair(type_name, vtype)); }

  /* local data */
  Expr2IVarTypeMap f_register;
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

  Module& new_module(Expr& identifier)
  {
    Module* m = new Module(identifier);
    add_module(*m);
    return *m;
  }

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

  inline Model& get_model()
  { return f_model; }

protected:
  ModelMgr()
    : f_model()
  {}

private:
  static ModelMgr_ptr f_instance;

  /* low-level services */
  /* local data */
  Model f_model;
};

#endif
