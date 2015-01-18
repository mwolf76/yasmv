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

#include <boost/unordered_map.hpp>

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <type/type.hh>
#include <enc/enc.hh>

#include <symb/symbol.hh>

/* -- Exception classes ----------------------------------------------------- */
class ModelException : public Exception {
public:
    virtual const char* what() const throw() =0;
};

class ModuleNotFound : public ModelException {
public:
    ModuleNotFound(Expr_ptr expr);
    const char* what() const throw();

private:
    Expr_ptr f_module_name;
};

class DuplicateIdentifier : public ModelException {
public:
    DuplicateIdentifier(Expr_ptr expr);
    const char* what() const throw();

private:
    Expr_ptr f_duplicate;
};

class BadParamCount : public ModelException {
public:
    BadParamCount(Expr_ptr instance, unsigned expected, unsigned got);
    const char* what() const throw();

private:
    Expr_ptr f_instance;
    unsigned f_expected;
    unsigned f_got;
};


class Module {
    friend std::ostream& operator<<(std::ostream& os, Module& module);

    Expr_ptr f_name;

    ExprVector f_locals;
    Expr_ptr f_input;

    Variables f_localVars;
    Parameters f_localParams;
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

    inline const Expr_ptr& input() const
    { return f_input; }
    void set_input(Expr_ptr input)
    { f_input = input; }

    inline const Variables& vars() const
    { return f_localVars; }
    void add_var(Expr_ptr expr, Variable_ptr var);

    inline const Parameters& parameters() const
    { return f_localParams; }
    void add_parameter(Expr_ptr expr, Parameter_ptr param);

    const Defines& defs() const
    { return f_localDefs; }
    void add_def(Expr_ptr expr, Define_ptr def);

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
typedef boost::unordered_map<Expr_ptr, Module_ptr, PtrHash, PtrEq> Modules;
std::ostream& operator<<(std::ostream& os, Module& module);

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

#endif
