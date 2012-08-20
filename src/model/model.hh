/**
 *  @file model.hh
 *  @brief Model module
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
 *
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2.1 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/

#ifndef MODEL_H
#define MODEL_H

#include <common.hh>
#include <expr.hh>
#include <types.hh>
#include <expr_mgr.hh>

// -- interfaces --------------------------------------------------------------
class ISymbol : IObject {
public:
    virtual const Expr_ptr ctx() const =0;
    virtual const Expr_ptr expr() const =0;

    virtual const Type_ptr get_type() const =0;

    bool is_variable() const;
    IVariable& as_variable() const;

    bool is_define() const;
    IDefine& as_define() const;

    bool is_const() const;
    IConstant& as_const() const;
};

class IVariable : public ISymbol {
};

class IConstant : public ISymbol {
};

class IDefine : public ISymbol {
public:
    // move this to symbol??
    virtual const Expr_ptr get_body() const =0;
};

class IAssign : public IObject {
public:
    virtual const Expr_ptr get_lvalue() const =0;
    virtual const Expr_ptr get_body() const =0;
};

class IModule : public IObject {
public:
    virtual const Expr_ptr expr() const =0;

    virtual const ExprVector& get_formalParams() const =0;
    virtual void add_formalParam(Expr_ptr identifier) =0;

    virtual const ExprVector& get_isaDecls() const =0;
    virtual void add_isaDecl(Expr_ptr identifier) =0;

    virtual const Variables& get_localVars() const =0;
    virtual void add_localVar(Expr_ptr expr, IVariable_ptr var) =0;

    virtual const Constants& get_localConsts() const =0;
    virtual void add_localConst(Expr_ptr expr, IConstant_ptr k) =0;

    virtual const Defines& get_localDefs() const =0;
    virtual void add_localDef(Expr_ptr expr, IDefine_ptr def) =0;

    virtual const Assigns& get_assign() const =0;
    virtual void add_assign(IAssign_ptr assgn) =0;

    virtual const ExprVector& get_init() const =0;
    virtual void add_init(Expr_ptr expr) =0;

    virtual const ExprVector& get_invar() const =0;
    virtual void add_invar(Expr_ptr expr) =0;

    virtual const ExprVector& get_trans() const =0;
    virtual void add_trans(Expr_ptr expr) =0;

    virtual const ExprVector& get_fairness() const =0;
    virtual void add_fairness(Expr_ptr expr) =0;

    // properties management
    virtual const ExprVector& get_ltlspecs() const =0;
    virtual void add_ltlspec(Expr_ptr formula) =0;

    virtual const ExprVector& get_ctlspecs() const =0;
    virtual void add_ctlspec(Expr_ptr formula) =0;
};

class IModel : public IObject {
public:
    virtual void add_module(Expr_ptr name, IModule_ptr module) =0;
    virtual IModule& get_module(Expr_ptr name) =0;

    virtual const Modules& get_modules() const =0;
};

typedef IModel* IModel_ptr;

class Module : public IModule {
    Expr_ptr f_name;
    ExprVector f_formalParams;
    ExprVector f_isaDecls;

    Variables f_localVars;
    Defines f_localDefs;
    Constants f_localConsts;

    ExprVector f_init;
    ExprVector f_invar;
    ExprVector f_trans;
    ExprVector f_fair;
    Assigns f_assgn;

    ExprVector f_ltlspecs;
    ExprVector f_ctlspecs;

public:

    Module(const Expr_ptr name);

    inline const Expr_ptr expr() const
    { return f_name; }

    bool is_main() const
    { return f_name == ExprMgr::INSTANCE().make_main(); }

    void add_formalParam(Expr_ptr identifier);
    const ExprVector& get_formalParams() const
    { return f_formalParams; }

    void add_isaDecl(Expr_ptr identifier);
    const ExprVector& get_isaDecls() const
    { return f_isaDecls; }

    void add_localVar(Expr_ptr name, IVariable_ptr var);
    const Variables& get_localVars() const
    { return f_localVars; }

    void add_localDef(Expr_ptr name, IDefine_ptr def);
    const Defines& get_localDefs() const
    { return f_localDefs; }

    void add_localConst(Expr_ptr name, IConstant_ptr k);
    const Constants& get_localConsts() const
    { return f_localConsts; }

    void add_assign(IAssign_ptr assign);
    const Assigns& get_assign() const
    { return f_assgn; }

    void add_init(Expr_ptr expr);
    const ExprVector& get_init() const
    { return f_init; }

    void add_invar(Expr_ptr expr);
    const ExprVector& get_invar() const
    { return f_invar; }

    void add_trans(Expr_ptr expr);
    const ExprVector& get_trans() const
    { return f_trans; }

    void add_fairness(Expr_ptr expr);
    const ExprVector& get_fairness() const
    { return f_fair; }

    void add_ltlspec(Expr_ptr formula);
    const ExprVector& get_ltlspecs() const
    { return f_ltlspecs; }

    void add_ctlspec(Expr_ptr formula);
    const ExprVector& get_ctlspecs() const
    { return f_ctlspecs; }
};

ostream& operator<<(ostream& os, Module& module);

class Variable : public IVariable {
    Expr_ptr f_ctx;
    Expr_ptr f_name;
    Type_ptr f_type;

public:
    Variable(Expr_ptr ctx, Expr_ptr name, Type_ptr type)
        : f_ctx(ctx)
        , f_name(name)
        , f_type(type)
    {}

    const Expr_ptr ctx() const
    { return f_ctx; }

    const Expr_ptr expr() const
    { return f_name; }

    const Type_ptr get_type() const
    { return f_type; }
};

class StateVar : public Variable {
public:
    StateVar (const Expr_ptr ctx, const Expr_ptr name, Type_ptr type_)
        : Variable(ctx, name, type_)
    {}
};

class InputVar : public Variable {
public:
    InputVar (const Expr_ptr ctx, const Expr_ptr name, Type_ptr type_)
        : Variable(ctx, name, type_)
    {}
};

class FrozenVar: public Variable {
public:
    FrozenVar (const Expr_ptr ctx, const Expr_ptr name, Type_ptr type_)
        : Variable(ctx, name, type_)
    {}
};

class Define : public IDefine {
    const Expr_ptr f_ctx;
    const Expr_ptr f_name;
    const Expr_ptr f_body;

public:
    Define(const Expr_ptr ctx, const Expr_ptr name, const Expr_ptr body)
        : f_ctx(ctx)
        , f_name(f_name)
        , f_body(body)
    {}

    const Expr_ptr ctx() const
    { return f_ctx; }

    const Expr_ptr expr() const
    { return f_name; }

    const Expr_ptr get_body() const
    { return f_body; }

    const Type_ptr get_type() const
    { return TypeMgr::INSTANCE().get_type(FQExpr(f_ctx, f_name)); }

};

class Assign : public IAssign {
    const Expr_ptr f_name;
    const Expr_ptr f_body;

public:
    Assign(const Expr_ptr name, const Expr_ptr body)
        : f_name(name)
        , f_body(body)
    {}

    const Expr_ptr get_lvalue() const
    { return f_name; }

    const Expr_ptr get_body() const
    { return f_body; }
};

class Model : public IModel {
    Modules f_modules;

public:
    Model()
        : f_modules()
    { logger << "Initialized Model instance @" << this << endl; }

    const Modules& get_modules() const
    { return f_modules; }

    void add_module(Expr_ptr name, IModule_ptr module)
    { f_modules.insert( make_pair<Expr_ptr, IModule_ptr> (name, module)); }

    IModule& get_module(Expr_ptr name)
    {
        const pair <Expr_ptr const, IModule_ptr> found = (*f_modules.find(name));

        if (!found.second) {
            // throw ModuleNotFoundException(name);
        }

        return *found.second;
    }

    ISymbol_ptr fetch_symbol(const FQExpr& fqexpr);
};

class ModelMgr;
typedef ModelMgr* ModelMgr_ptr;

class ModelMgr  {
public:
    static ModelMgr& INSTANCE() {
        if (! f_instance) f_instance = new ModelMgr();
        return (*f_instance);
    }

    inline IModel_ptr get_model()
    { return &f_model; }

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
