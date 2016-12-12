/**
 * @file resolver.cc
 * @brief Model management subsystem, symbol resolver class implementation.
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

#include <symb/symbol.hh>

#include <type/type.hh>

#include <model/model_resolver.hh>
#include <model/model_mgr.hh>
#include <model/model.hh>
#include <model/module.hh>

#include <algorithm>

ModelResolver::ModelResolver(ModelMgr& owner)
    : f_owner(owner)
{
    const void* instance
        (this);

    ExprMgr& em
        (ExprMgr::INSTANCE());

    DRIVEL
        << "Initialized Model Resolver instance @"
        << instance
        << std::endl;

    f_owner.symbols().insert( std::make_pair<Expr_ptr,
                              Constant_ptr>( em.make_false(),
                                             new Constant(ExprMgr::INSTANCE().make_empty(),
                                                          ExprMgr::INSTANCE().make_false(),
                                                          TypeMgr::INSTANCE().find_boolean(), 0)));

    f_owner.symbols().insert( std::make_pair<Expr_ptr,
                              Constant_ptr>( em.make_true(),
                                             new Constant(ExprMgr::INSTANCE().make_empty(),
                                                          ExprMgr::INSTANCE().make_true(),
                                                          TypeMgr::INSTANCE().find_boolean(), 1)));
}

ModelResolver::~ModelResolver()
{}

void ModelResolver::add_symbol(const Expr_ptr key, Symbol_ptr symb)
{
    // TODO: turn this into an exception
    assert( NULL == f_owner.symbols() [ key ]);

    f_owner.symbols()[ key ] = symb;
}

Symbol_ptr ModelResolver::symbol(const Expr_ptr key)
{
    // init lookup data
    ModelMgr& mm
        (ModelMgr::INSTANCE());
    ExprMgr& em
        (ExprMgr::INSTANCE());

    assert( em.is_dot(key));
    Module_ptr module
        (mm.scope(key -> lhs()));
    Expr_ptr symb_name
        (key -> rhs());

    { /* global constants and temporaries */
        const Symbols& symbols
            (f_owner.symbols());
        Symbols::const_iterator iter
            (symbols.find(symb_name));

        if (iter != f_owner.symbols().end()) {
            return (*iter).second;
        }
    }

    { /* variables */
        const Variables& vars
            (module->vars());
        Variables::const_iterator iter
            (vars.find(symb_name));

        if (iter != vars.end()) {
            return (*iter).second;
        }
    }

    { /* parameters */
        const Parameters& params
            (module->parameters());
        Parameters::const_iterator iter
            (params.begin());

        while (params.end() != iter) {
            if (iter -> first == symb_name)
                return iter -> second;

            ++ iter;
        }
    }

    { /* defines */
        const Defines& defs
            (module->defs());
        Defines::const_iterator iter
            (defs.find(symb_name));

        if (iter != defs.end()) {
            return (*iter).second;
        }
    }

    return NULL; // unresolved;
}
