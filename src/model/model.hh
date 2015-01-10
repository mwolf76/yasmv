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
#include <expr_mgr.hh>

#include <type.hh>
#include <enc.hh>

#include <symbol.hh>

/* -- Exception classes ----------------------------------------------------- */
class ModelException : public Exception {
public:
    virtual const char* what() const throw() =0;
};

class ModuleNotFound : public ModelException {
public:
    ModuleNotFound(Expr_ptr expr);

    const char* what() const throw();
    ~ModuleNotFound() throw();

private:
    Expr_ptr f_module_name;
};

class FailedResolution : public ModelException {

public:
    FailedResolution(Expr_ptr symbol);

    const char* what() const throw();
    ~FailedResolution() throw();

private:
    Expr_ptr f_symbol;
};

/* -- FSM decls ------------------------------------------------------------- */

class Module {
    Expr_ptr f_name;

    ExprVector f_locals;

    Variables f_localVars;
    Defines   f_localDefs;

    ExprVector f_init;
    ExprVector f_invar;
    ExprVector f_trans;

public:
    Module(Expr_ptr name);
    ~Module();

    inline const Expr_ptr name() const
    { return f_name; }

    /* Symbols management, preserves decl ordering */
    inline const ExprVector& locals() const
    { return f_locals; }

    inline const Variables& vars() const
    { return f_localVars; }
    void add_var(Expr_ptr expr, IVariable_ptr var);

    const Defines& defs() const
    { return f_localDefs; }
    void add_def(Expr_ptr expr, IDefine_ptr def);

    /* Finite State Machine definition */
    inline const ExprVector& init() const
    { return f_init; }
    void add_init(Expr_ptr expr);

    const ExprVector& invar() const
    { return f_invar; }
    void add_invar(Expr_ptr expr);

    inline const ExprVector& trans() const
    { return f_trans; }
    void add_trans(Expr_ptr expr);
};

typedef Module* Module_ptr;
typedef unordered_map<Expr_ptr, Module_ptr, PtrHash, PtrEq> Modules;
ostream& operator<<(ostream& os, Module& module);

class Model {
    Modules f_modules;

public:
    Model();
    ~Model();

    inline const Modules& modules() const
    { return f_modules; }

    Module& add_module(Module& module);
    Module& module(Expr_ptr module_name);
};

typedef Model* Model_ptr;

class Variable : public IVariable {
    Expr_ptr f_ctx;
    Expr_ptr f_name;
    Type_ptr f_type;
    bool     f_input;

public:
    Variable(Expr_ptr ctx, Expr_ptr name, Type_ptr type, bool input = false)
        : f_ctx(ctx)
        , f_name(name)
        , f_type(type)
        , f_input(input)
    {}

    const Expr_ptr ctx() const
    { return f_ctx; }

    const Expr_ptr expr() const
    { return f_name; }

    const Type_ptr type() const
    { return f_type; }

    bool input() const
    { return f_input; }
};

class Temporary : public ITemporary {
private:
    Expr_ptr f_ctx;
    Expr_ptr f_name;
    Type_ptr f_type;

public:
    Temporary(Expr_ptr name, Type_ptr type)
        : f_ctx(ExprMgr::INSTANCE().make_main())
        , f_name(name)
        , f_type(type)
    {}

    const Expr_ptr ctx() const
    { return f_ctx; }

    const Expr_ptr expr() const
    { return f_name; }

    const Type_ptr type() const
    { return f_type; }
};

class Constant : public IConstant {
    const Expr_ptr f_ctx;
    const Expr_ptr f_name;
    const Type_ptr f_type;
    value_t f_value;

public:
    Constant(const Expr_ptr ctx, const Expr_ptr name, Type_ptr type, value_t value)
        : f_ctx(ctx)
        , f_name(name)
        , f_type(type)
        , f_value(value)
    {}

    const Expr_ptr ctx() const
    { return f_ctx; }

    const Expr_ptr expr() const
    { return f_name; }

    const Type_ptr type() const
    { return f_type; }

    value_t value() const
    { return f_value; }
};

class Define : public IDefine {
    const Expr_ptr f_ctx;

    const Expr_ptr f_name;
    const ExprVector f_formals;
    const Expr_ptr f_body;

public:
    Define(const Expr_ptr ctx, const Expr_ptr name,
           const ExprVector& formals, const Expr_ptr body)
        : f_ctx(ctx)
        , f_name(name)
        , f_formals(formals)
        , f_body(body)
    {}

    const Expr_ptr ctx() const
    { return f_ctx; }

    const Expr_ptr expr() const
    { return f_name; }

    const Expr_ptr body() const
    { return f_body; }

    const ExprVector& formals() const
    { return f_formals; }
};

/**
 * Symbol iterator
 *
 * COI aware
 * Preserves ordering
 *
 */
class SymbIter {
public:
    /* Calculates COI if formula is non-NULL */
    SymbIter(Model& model, Expr_ptr formula = NULL);

    ~SymbIter();

    /* true iff there are more symbols to be processed */
    inline bool has_next() const
    { return f_iter != f_symbols.end(); }

    inline ISymbol_ptr next()
    {
        ISymbol_ptr res = (* f_iter);
        ++ f_iter;

        return res;
    }

private:
    Model&  f_model;
    Expr_ptr f_formula; /* for COI */

    vector<ISymbol_ptr> f_symbols;
    vector<ISymbol_ptr>::const_iterator f_iter;
};

#endif
