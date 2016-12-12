/**
 * @file model/module.cc
 * @brief Model management subsystem, Module class implementation.
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

#include <algorithm>
#include <utility>
#include <string>

#include <model/exceptions.hh>
#include <model/model.hh>
#include <model/module.hh>

Module::Module(const Expr_ptr name)
    : f_owner(NULL)
    , f_name(name)
{
    const void *instance
        (this);

    DEBUG
        << "Initialized Module instance @"
        << instance
        << std::endl;
}

void Module::checkDuplicates(Expr_ptr identifier)
{
    if (f_locals.end() != std::find( f_locals.begin(),
                                     f_locals.end(), identifier))
        throw DuplicateIdentifier(identifier);

    /* avoid duplicates */
    f_locals.insert(identifier);

    /* keep track of decl ordering */
    owner().autoIndexSymbol(identifier);
}

void Module::add_var(Expr_ptr identifier, Variable_ptr var)
{
    Expr_ptr type_repr
        (var->type()->repr());

    std::ostringstream oss;

    if (var->is_hidden())
        oss
            << "hidden ";

    if (var->is_input())
        oss
            << "input ";

    if (var->is_frozen())
        oss
            << "frozen ";

    const std::string tmp
        (oss.str());

    DEBUG
        << "Module `"
        << (*this)
        << "`, added "
        << tmp
        << "var `" << identifier
        << "`, of type `" << type_repr << "`"
        << std::endl;

    checkDuplicates(identifier);
    f_localVars.insert(std::make_pair<Expr_ptr, Variable_ptr>
                       (identifier, var));
}

void Module::add_parameter(Expr_ptr identifier, Parameter_ptr param)
{
    Expr_ptr type_repr
        (param->type()->repr());

    DEBUG
        << "Module `" << (*this)
        << "`, added parameter `" << identifier
        << "`, of type `" << type_repr << "`"
        << std::endl;

    checkDuplicates(identifier);
    f_localParams.push_back( std::make_pair<Expr_ptr, Parameter_ptr>
                             (identifier, param));
}

void Module::add_def(Expr_ptr identifier, Define_ptr def)
{
    std::ostringstream oss;

    if (def->is_hidden())
        oss
            << "hidden ";

    oss
        << "DEFINE";

    const std::string tmp
        (oss.str());

    DEBUG
        << "Module "
        << (*this)
        << ", added "
        << tmp
        << " `" << identifier << "`"
        << std::endl;

    checkDuplicates(identifier);
    f_localDefs.insert(std::make_pair<Expr_ptr, Define_ptr>
                       (identifier, def));
}

void Module::override(Expr_ptr symb_name, Define_ptr def)
{
    std::ostringstream oss;

    if (def->is_hidden())
        oss
            << "hidden ";

    const std::string tmp
        (oss.str());

    if (f_locals.end() == std::find( f_locals.begin(),
                                     f_locals.end(), symb_name))
        throw UnknownIdentifier(symb_name);

    Expr_ptr body
        (def->body());

    DEBUG
        << "Module "
        << (*this)
        << ", overridden "
        << tmp
        << "define `"
        << symb_name << "`"
        << " to "
        << body
        << std::endl;

    f_localDefs.insert(std::make_pair<Expr_ptr, Define_ptr>
                       (symb_name, def));
}

void Module::add_init(Expr_ptr expr)
{
    DEBUG
        << "Module `"
        << (*this)
        << "`, added INIT "
        << expr
        << std::endl;

    f_init.push_back(expr);
}

void Module::add_invar(Expr_ptr expr)
{
    DEBUG
        << "Module `"
        << (*this)
        << "`, added INVAR "
        << expr
        << std::endl;

    f_invar.push_back(expr);
}

void Module::add_trans(Expr_ptr expr)
{
    DEBUG
        << "Module `"
        << (*this)
        << "`, added TRANS "
        << expr
        << std::endl;

    f_trans.push_back(expr);
}

