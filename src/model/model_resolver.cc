/**
 *  @file resolver.cc
 *  @brief Symbol resolution module
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
#include <symbol.hh>
#include <model_resolver.hh>
#include <model_mgr.hh>
#include <type_exceptions.hh>

ModelResolver::ModelResolver(ModelMgr& owner)
    : f_owner(owner)
{
    DEBUG << "Initialized Model Resolver instance @" << this << endl;

    // initialize global constants
    f_owner.symbols().insert(make_pair<FQExpr,
                             IConstant_ptr>(FQExpr(ExprMgr::INSTANCE().make_false()),
                                            new Constant(ExprMgr::INSTANCE().make_main(), // default ctx
                                                         ExprMgr::INSTANCE().make_false(),
                                                         TypeMgr::INSTANCE().find_boolean(), 0)));

    f_owner.symbols().insert(make_pair<FQExpr,
                             IConstant_ptr>(FQExpr(ExprMgr::INSTANCE().make_true()),
                                            new Constant(ExprMgr::INSTANCE().make_main(), // default ctx
                                                 ExprMgr::INSTANCE().make_true(),
                                                         TypeMgr::INSTANCE().find_boolean(), 1)));
}

ModelResolver::~ModelResolver()
{}

void ModelResolver::add_symbol(const Expr_ptr ctx, const Expr_ptr expr, ISymbol_ptr symb)
{
    // global ctx, time arbitrarily set to 0.
    FQExpr key(ctx, expr, 0);

    // TODO: turn this into an exception
    assert( NULL == f_owner.symbols() [ key ]);

    f_owner.symbols()[ key ] = symb;
}

ISymbol_ptr ModelResolver::symbol(const Expr_ptr ctx, const Expr_ptr expr)
{
    /* Fetch modules from model */
    const Modules& f_modules = f_owner.model()->modules();

    Modules::const_iterator eye = f_modules.find(ctx);
    if (eye == f_modules.end()) return NULL;

    // init lookup data
    IModule_ptr module = (*eye).second;
    FQExpr key(ctx, expr, 0); // time arbitrarily set to 0

    { /* global constants and temporaries */
        const Symbols& symbols = f_owner.symbols();
        Symbols::const_iterator iter = symbols.find(key);
        if (iter != f_owner.symbols().end()) {
            return (*iter).second;
        }
    }

    { /* local consts */
        const Constants& cnts = module->consts();
        Constants::const_iterator iter = cnts.find(key);
        if (iter != cnts.end()) {
            return (*iter).second;
        }
    }

    { /* variables */
        const Variables& vars = module->vars();
        Variables::const_iterator iter = vars.find(key);
        if (iter != vars.end()) {
            return (*iter).second;
        }
    }

    { /* defines */
        const Defines& defs = module->defs();
        Defines::const_iterator iter = defs.find(key);
        if (iter != defs.end()) {
            return (*iter).second;
        }
    }

    return NULL; // unresolved;
}
