/**
 * @file model/module.hh
 * @brief Model module, Module class declarations.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#ifndef MODEL_MODULE_H
#define MODEL_MODULE_H

#include <common/common.hh>
#include <expr/expr.hh>
#include <symb/symbol.hh>
#include <model/typedefs.hh>

class Module {
    friend std::ostream& operator<<(std::ostream& os, Module& module);

    Expr_ptr f_name;

    ExprVector f_locals;

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

    inline const Variables& vars() const
    { return f_localVars; }
    void add_var(Expr_ptr expr, Variable_ptr var);

    inline const Parameters& parameters() const
    { return f_localParams; }
    void add_parameter(Expr_ptr expr, Parameter_ptr param);

    const Defines& defs() const
    { return f_localDefs; }
    void add_def(Expr_ptr expr, Define_ptr def);
    void override(Expr_ptr expr, Define_ptr def);

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

#endif /* MODEL_MODULE_H */
