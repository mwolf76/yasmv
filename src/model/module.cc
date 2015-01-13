/**
 *  @file module.cc
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
#include <utility>
#include <model.hh>

std::ostream& operator<<(std::ostream& os, Module& module)
{ return os << module.name(); }

Module::Module(const Expr_ptr name)
    : f_name(name)

    , f_localVars()
    , f_localDefs()

    , f_init()
    , f_trans()
{}

void Module::add_var(Expr_ptr var_name, Variable_ptr var)
{
    Expr_ptr type_repr( var -> type() -> repr());
    DEBUG
        << "Module `" << (*this)
        << "`, added var `" << var_name
        << "`, of type `" << type_repr << "`"
        << std::endl;

    f_locals.push_back(var_name);

    FQExpr key (name(), var_name);
    f_localVars.insert(std::make_pair<FQExpr, Variable_ptr>
                       (key, var));

}

void Module::add_def(Expr_ptr def_name, Define_ptr body)
{
    DEBUG
        << "Module " << (*this)
        << ", added local def `"
        << def_name << "`"
        << std::endl;

    f_locals.push_back(def_name);

    FQExpr key (name(), def_name);
    f_localDefs.insert(std::make_pair<FQExpr, Define_ptr>
                       (key, body));
}

void Module::add_init(Expr_ptr expr)
{
    DEBUG
        << "Module `" << (*this) << "`, added INIT "
        << expr
        << std::endl;

    f_init.push_back(expr);
}

void Module::add_invar(Expr_ptr expr)
{
    DEBUG
        << "Module `" << (*this) << "`, added INVAR "
        << expr
        << std::endl;

    f_invar.push_back(expr);
}

void Module::add_trans(Expr_ptr expr)
{
    DEBUG
        << "Module `" << (*this) << "`, added TRANS "
        << expr
        << std::endl;

    f_trans.push_back(expr);
}

