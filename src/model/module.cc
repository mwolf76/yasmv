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

#include <model/exceptions.hh>
#include <model/model.hh>
#include <model/module.hh>

#include <type/classes.hh>
#include <type/typedefs.hh>

#include <algorithm>
#include <string>
#include <utility>

namespace model {

    Module::Module(const expr::Expr_ptr name)
        : f_owner(NULL)
        , f_name(name)
    {
        const void* instance { this };

        DEBUG
            << "Initialized Module instance @"
            << instance
            << std::endl;
    }

    void Module::checkDuplicates(expr::Expr_ptr identifier)
    {
        if (f_locals.end() != std::find(f_locals.begin(),
                                        f_locals.end(), identifier)) {
            throw DuplicateIdentifier(identifier);
        }

        /* avoid duplicates */
        f_locals.insert(identifier);

        /* keep track of decl ordering */
        owner().autoIndexSymbol(identifier);
    }

    void Module::add_var(expr::Expr_ptr identifier, symb::Variable_ptr var)
    {
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

        type::Type_ptr type { var->type() };
        expr::Expr_ptr type_repr { type->repr() };

        std::ostringstream oss;

        if (var->is_hidden()) {
            oss
                << "hidden ";
        }

        if (var->is_input()) {
            oss
                << "input ";
        }

        if (var->is_inertial()) {
            oss
                << "inertial ";
        }

        if (var->is_frozen()) {
            oss
                << "frozen ";
        }

        const std::string tmp { oss.str() };

        DEBUG
            << "Module `"
            << (*this)
            << "`, added "
            << tmp
            << "var `" << identifier
            << "`, of type `" << type_repr << "`"
            << std::endl;

        checkDuplicates(identifier);
        f_localVars.insert(
            std::pair<expr::Expr_ptr, symb::Variable_ptr>(identifier, var));

        /* for enum vars, we need to add an INVAR x in { <lits > } */
        if (type->is_enum()) {
            type::EnumType_ptr enum_type {
                type->as_enum()
            };

            add_invar(
                em.make_eq(identifier,
                           enum_type->repr()));
        }
    }

    void Module::add_parameter(expr::Expr_ptr identifier, symb::Parameter_ptr param)
    {
        expr::Expr_ptr type_repr { param->type()->repr() };

        DEBUG
            << "Module `" << (*this)
            << "`, added parameter `" << identifier
            << "`, of type `" << type_repr << "`"
            << std::endl;

        checkDuplicates(identifier);
        f_localParams.push_back(
            std::pair<expr::Expr_ptr, symb::Parameter_ptr>(identifier, param));
    }

    void Module::add_def(expr::Expr_ptr identifier, symb::Define_ptr def)
    {
        std::ostringstream oss;

        if (def->is_hidden()) {
            oss
                << "hidden ";
        }

        oss
            << "DEFINE";

        const std::string tmp(oss.str());

        DEBUG
            << "Module "
            << (*this)
            << ", added "
            << tmp
            << " `" << identifier << "`"
            << std::endl;

        checkDuplicates(identifier);
        f_localDefs.insert(
            std::pair<expr::Expr_ptr, symb::Define_ptr>(identifier, def));
    }

    void Module::override(expr::Expr_ptr symb_name, symb::Define_ptr def)
    {
        std::ostringstream oss;

        if (def->is_hidden()) {
            oss
                << "hidden ";
        }

        const std::string tmp { oss.str() };

        if (f_locals.end() == std::find(f_locals.begin(),
                                        f_locals.end(), symb_name)) {
            throw UnknownIdentifier(symb_name);
        }

        expr::Expr_ptr body { def->body() };

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

        f_localDefs.insert(
            std::pair<expr::Expr_ptr, symb::Define_ptr>(symb_name, def));
    }

    void Module::add_init(expr::Expr_ptr expr)
    {
        DEBUG
            << "Module `"
            << (*this)
            << "`, added INIT "
            << expr
            << std::endl;

        f_init.push_back(expr);
    }

    void Module::add_invar(expr::Expr_ptr expr)
    {
        DEBUG
            << "Module `"
            << (*this)
            << "`, added INVAR "
            << expr
            << std::endl;

        f_invar.push_back(expr);
    }

    void Module::add_trans(expr::Expr_ptr expr)
    {
        DEBUG
            << "Module `"
            << (*this)
            << "`, added TRANS "
            << expr
            << std::endl;

        f_trans.push_back(expr);
    }

}; // namespace model
