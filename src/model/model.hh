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

class IVariable;
typedef IVariable* IVariable_ptr;
typedef vector<IVariable_ptr> Variables;

class IVarType;
typedef IVarType* IVarType_ptr;

class IModule;
typedef IModule* IModule_ptr;

class IVarType {
public:
  virtual Atom get_name() const =0;
  virtual bool is_boolean() const =0;
  virtual bool is_intRange() const =0;
  virtual bool is_intEnum() const =0;
  virtual bool is_symb_enum() const =0;
  virtual bool is_mixed_enum() const =0;
  virtual bool is_instance() const =0;
};

typedef pair<Atom, IVarType_ptr> VarDecl;
typedef vector<VarDecl*> VarDecls;

class IModule {
public:
  virtual bool is_main() const =0;
  virtual const Atom& get_name() const =0;

  virtual const Atoms& get_formalParams() =0;
  virtual IModule& operator+=(Atom& identifier) =0;

  // virtual const ISADeclarations& get_isaDecls() =0;
  // virtual IModule& operator+=(ISADeclaration& identifier) =0;

  virtual const VarDecls& get_localVars() const =0;
  virtual IModule& operator+=(VarDecl& vdecl) =0;
};
typedef IModule* IModule_ptr;
typedef vector<IModule_ptr> Modules;

class IVariable {
public:
  virtual const Atom& get_fqdn() const =0;

  virtual const IModule& get_owner() const =0;
  virtual const Atom& get_name() const =0;

  virtual const IVarType& get_type() const =0;
};
typedef IVariable* IVariable_ptr;

class IModel {
public:
  virtual const string& get_origin() const =0;
  virtual const Modules& get_modules() const =0;
  virtual IModel& operator+=(IModule& module) =0;
};

// typedef pair<Atom, IVarType_ptr> ParamDeclaration;
// typedef vector<ParamDeclaration> ParamDeclarations;

class Module : public IModule {
  Atom f_name;
  Atoms f_formalParams;
  VarDecls f_localVars;

public:

  Module(const Atom name) :
    f_name(name),
    f_formalParams(),
    f_localVars() {}

  const Atom& get_name() const
  { return f_name; }

  const Atoms& get_formalParams() const
  { return f_formalParams; }

  IModule& operator+=(Atom& identifier)
  {
    f_formalParams.push_back(&identifier);
    return *this;
  }

  const VarDecls& get_localVars() const
  { return f_localVars; }

  IModule& operator+=(VarDecl& vdecl)
  {
    f_localVars.push_back(&vdecl);
    return *this;
  }
};

class Instance {
  Module& f_module;
  Variables f_actualParams;

  Instance(Module& module, Variables actualParams);
};

class Variable : public IVariable {
  Atom f_name;
  Atom f_fqdn;

  IModule& f_owner;
  IVarType& f_type;

public:
  Variable(IModule& owner, const Atom name, IVarType& type)
    : f_owner(owner),
      f_type(type)
  {
    ostringstream oss;
    oss << owner.get_name() << "." << name;
    f_fqdn = oss.str();
    f_name = name;
  }

  const IModule& get_owner() const
  { return f_owner; }

  const Atom& get_fqdn() const
  { return f_fqdn; }

  const Atom& get_name() const
  { return f_name; }
};

class StateVar : public Variable {
  StateVar (IModule& owner, const Atom name, IVarType& type_)
    : Variable(owner, name, type_)
  {}
};

class InputVar : public Variable {
  InputVar (IModule& owner, const Atom name, IVarType& type_)
    : Variable(owner, name, type_)
  {}
};

class FrozenVar: public Variable {
  FrozenVar (IModule& owner, const Atom name, IVarType& type_)
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

  Atom get_name() const
  { return "boolean"; }
};

class EnumType : public IVarType {
  friend class TypeRegister;
  EnumType() {}

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

  Atom get_name() const
  { return "boolean"; }

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

  Atom get_name() const
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
//   Atom f_moduleName;
//   Instance* f_binding; // reserved for type resolution

//   InstanceType(Atom moduleName) :
//     f_moduleName(moduleName),
//     f_binding(NULL) {}

// public:
//   Instance& get_instance();

//   bool is_unresolved() const;
// };

// class FiniteTypeIteratorException (Exception) {
// };

typedef unordered_map<Atom, IVarType_ptr> Atom2IVarTypeMap;
class TypeRegister {
  Atom2IVarTypeMap f_register;

public:
  TypeRegister():
    f_register()
  {
    /* predefined types */
    register_type("boolean", new BooleanType());
  }

  void register_type(const Atom type_name, IVarType_ptr vtype)
  { f_register.insert(VarDecl(type_name, vtype)); }

};

class Model : public IModel {
  string f_origin;
  Modules f_modules;

public:
  Model(const string origin)
    : f_origin(origin),
      f_modules()
  {}

  const string& get_origin() const
  { return f_origin; }

  const Modules& get_modules() const
  { return f_modules; }

  IModel& operator+=(IModule& module)
  { f_modules.push_back(&module); }

};



// int main()
// {
//   std::tr1::unordered_set<Expr*, ExprHash, ExprEq > terms;
//   // std::tr1::unordered_map<Expr, int, ExprHash, ExprEq> adds;
//   std::tr1::unordered_map<Expr*, int> adds;

//   return 0;
// }

#endif
