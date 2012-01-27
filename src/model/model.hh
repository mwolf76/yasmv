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
#include <types.hh>
#include <expr_mgr.hh>

// -- interfaces --------------------------------------------------------------

class IVariable {
public:
  virtual const Expr_ptr get_name() const =0;
  virtual const Type_ptr get_type() const =0;
};
typedef IVariable* IVariable_ptr;

class IDefine {
public:
  virtual const Expr_ptr get_name() const =0;
  virtual const Expr_ptr get_body() const =0;
};
typedef IDefine* IDefine_ptr;

class IAssign {
public:
  virtual const Expr_ptr get_name() const =0;
  virtual const Expr_ptr get_body() const =0;
};
typedef IAssign* IAssign_ptr;

class IModule {
public:
  virtual bool is_main() const =0;
  virtual const Expr_ptr get_name() const =0;

  virtual const Exprs& get_formalParams() const =0;
  virtual void add_formalParam(Expr_ptr identifier) =0;

  // virtual const ISADeclarations& get_isaDecls() =0;
  // virtual IModule& operator+=(ISADeclaration& identifier) =0;

  virtual const Variables& get_localVars() const =0;
  virtual void add_localVar(IVariable_ptr var) =0;

  virtual const Defines& get_localDefs() const =0;
  virtual void add_localDef(IDefine_ptr def) =0;

  virtual const Assigns& get_assign() const =0;
  virtual void add_assign(IAssign_ptr assgn) =0;

  virtual const Exprs& get_init() const =0;
  virtual void add_init(Expr_ptr expr) =0;

  virtual const Exprs& get_invar() const =0;
  virtual void add_invar(Expr_ptr expr) =0;

  virtual const Exprs& get_trans() const =0;
  virtual void add_trans(Expr_ptr expr) =0;

  virtual const Exprs& get_fairness() const =0;
  virtual void add_fairness(Expr_ptr expr) =0;
};

class IModel {
public:
  virtual const Modules& get_modules() const =0;
  virtual void add_module(IModule* module) =0;
};
typedef IModel* IModel_ptr;

class Module : public IModule {
  Expr_ptr f_name;
  Exprs f_formalParams;

  Variables f_localVars;
  Defines f_localDefs;

  Exprs f_init;
  Exprs f_invar;
  Exprs f_trans;
  Exprs f_fair;
  Assigns f_assgn;

public:

  Module(const Expr_ptr name)
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

  const Expr_ptr get_name() const
  { return f_name; }

  bool is_main() const
  { return f_name == ExprMgr::INSTANCE().make_main(); }

  const Exprs& get_formalParams() const
  { return f_formalParams; }

  void add_formalParam(Expr_ptr identifier)
  { f_formalParams.push_back(identifier); }

  const Variables& get_localVars() const
  { return f_localVars; }

  void add_localVar(IVariable_ptr var)
  { f_localVars.push_back(var); }

  const Defines& get_localDefs() const
  { return f_localDefs; }

  void add_localDef(IDefine_ptr def)
  { f_localDefs.push_back(def); }

  const Assigns& get_assign() const
  { return f_assgn; }

  void add_assign(IAssign_ptr assign)
  { f_assgn.push_back(assign); }

  const Exprs& get_init() const
  { return f_init; }

  void add_init(Expr_ptr expr)
  { f_init.push_back(expr); }

  const Exprs& get_invar() const
  { return f_invar; }

  void add_invar(Expr_ptr expr)
  { f_invar.push_back(expr); }

  const Exprs& get_trans() const
  { return f_trans; }

  void add_trans(Expr_ptr expr)
  { f_trans.push_back(expr); }

  const Exprs& get_fairness() const
  { return f_fair; }

  void add_fairness(Expr_ptr expr)
  { f_fair.push_back(expr); }
};

typedef IModule* IModule_ptr;
typedef vector<IModule_ptr> Modules;

class Variable : public IVariable {
  Expr_ptr f_name;
  Type_ptr f_type;

public:
  Variable(Expr_ptr name, Type_ptr type)
    : f_name(name)
    , f_type(type)
  {}

  const Expr_ptr get_name() const
  { return f_name; }

  const Type_ptr get_type() const
  { return f_type; }
};

class StateVar : public Variable {
public:
  StateVar (const Expr_ptr name, Type_ptr type_)
    : Variable(name, type_)
  {}
};

class InputVar : public Variable {
public:
  InputVar (const Expr_ptr name, Type_ptr type_)
    : Variable(name, type_)
  {}
};

class FrozenVar: public Variable {
public:
  FrozenVar (const Expr_ptr name, Type_ptr type_)
    : Variable(name, type_)
  {}
};

class Define : public IDefine {
  const Expr_ptr f_name;
  const Expr_ptr f_body;

public:
  Define(const Expr_ptr name, const Expr_ptr body)
    : f_name(f_name)
    , f_body(body)
  {}

  const Expr_ptr get_name() const
  { return f_name; }

  const Expr_ptr get_body() const
  { return f_body; }
};

class Assign : public IAssign {
  const Expr_ptr f_name;
  const Expr_ptr f_body;

public:
  Assign(const Expr_ptr name, const Expr_ptr body)
    : f_name(name)
    , f_body(body)
  {}

  const Expr_ptr get_name() const
  { return f_name; }

  const Expr_ptr get_body() const
  { return f_body; }
};

class Model : public IModel {
  Modules f_modules;

public:
  Model()
    : f_modules()
  {}

  const Modules& get_modules() const
  { return f_modules; }

  void add_module(IModule_ptr module)
  { f_modules.push_back(module); }

  IModule_ptr new_module(Expr_ptr identifier)
  {
    IModule_ptr m = new Module(identifier);
    add_module(m);

    return m;
  }

};

class ModelMgr;
typedef ModelMgr* ModelMgr_ptr;

class ModelMgr  {
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
