/**
 * @file model/model.cc
 * @brief Model management subsystem, Model class implementation.
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

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <model/model.hh>
#include <model/module.hh>

namespace model {

    Model::Model()
        : f_modules()
    {
        const void* instance(this);

        DEBUG
            << "Initialized Model instance @"
            << instance
            << std::endl;
    }

    Model::~Model()
    {
        // TODO: free memory for symbols... (they've been allocated using new)
        assert(false); // XXX
    }

    Module& Model::add_module(Module& module)
    {
        expr::Expr_ptr name { module.name() };

        DEBUG
            << "Added module: `"
            << name << "`"
            << std::endl;

        f_modules.insert(
            std::pair<expr::Expr_ptr, Module_ptr>(name, &module));

        module.set_owner(this);
        return module;
    }

    Module& Model::module(expr::Expr_ptr module_name)
    {
        Modules::const_iterator i { f_modules.find(module_name) };

        if (i == f_modules.end()) {
            throw MainModuleNotFound();
        }

        return *(i->second);
    }

    Module& Model::main_module()
    {
        if (!f_modules.size()) {
            throw MainModuleNotFound();
        }

        Modules::const_iterator i { f_modules.begin() };

        return *(i->second);
    }

    void Model::autoIndexSymbol(expr::Expr_ptr identifier)
    {
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

        // TODO: this is not going to work for other modules
        expr::Expr_ptr ctx { em.make_empty() };
        expr::Expr_ptr full { em.make_dot(ctx, identifier) };

        f_symbol_index_map.insert(
            std::pair<expr::Expr_ptr, unsigned>(full, ++f_autoincrement));
    }

    unsigned Model::symbol_index(expr::Expr_ptr identifier)
    {
        SymbolIndexMap::const_iterator eye { f_symbol_index_map.find(identifier) };
        assert(f_symbol_index_map.end() != eye);

        unsigned res { eye->second };
        return res;
    }

}; // namespace model
