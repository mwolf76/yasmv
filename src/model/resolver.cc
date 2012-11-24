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

#include <model.hh>
#include <resolver.hh>

#include <model_mgr.hh>

#include <type_exceptions.hh>

Resolver::Resolver(ModelMgr& owner)
    : f_owner(owner)
{
    DEBUG << "Initialized Resolver instance @" << this << endl;

    // initialize global constants
    f_constants.insert(make_pair<FQExpr,
                       IConstant_ptr>(FQExpr(ExprMgr::INSTANCE().make_false()),
                                      new Constant(ExprMgr::INSTANCE().make_main(), // default ctx
                                                   ExprMgr::INSTANCE().make_false(),
                                                   TypeMgr::INSTANCE().find_boolean(), 0)));

    f_constants.insert(make_pair<FQExpr,
                       IConstant_ptr>(FQExpr(ExprMgr::INSTANCE().make_true()),
                                      new Constant(ExprMgr::INSTANCE().make_main(), // default ctx
                                                   ExprMgr::INSTANCE().make_true(),
                                                   TypeMgr::INSTANCE().find_boolean(), 1)));
}

Resolver::~Resolver()
{}

void Resolver::register_temporary(const Expr_ptr symb, ITemporary_ptr temp)
{
    // global ctx, time arbitrarily set to 0.
    FQExpr key(ExprMgr::INSTANCE().make_main(), symb, 0);

    // TODO: turn this into an exception
    assert( NULL == f_temporaries[ key ]);

    f_temporaries[ key ] = temp;
}

ISymbol_ptr Resolver::fetch_symbol(const Expr_ptr ctx, const Expr_ptr symb)
{
    /* Fetch modules from model */
    const Modules& f_modules = f_owner.model()->modules();

    Modules::const_iterator eye = f_modules.find(ctx);
    if (eye == f_modules.end()) throw BadContext(ctx);

    // init lookup data
    IModule_ptr module = (*eye).second;
    FQExpr key(ctx, symb, 0); // time arbitrarily set to 0.

    { /* Temp symbols are maintained here internally */
        Temporaries::iterator viter = f_temporaries.find(key);
        if (viter != f_temporaries.end()) {
            return (*viter).second;
        }
    }

    { /* local consts */
        Constants cnts = module->get_localConsts();
        Constants::iterator citer = cnts.find(key);
        if (citer != cnts.end()) {
            return (*citer).second;
        }
    }

    { /* global consts */
        Constants::iterator citer = f_constants.find(key);
        if (citer != f_constants.end()) {
            return (*citer).second;
        }
    }

    { /* params */
        // TODO: not yet implemented: params
    }

    { /* defines */
        Defines defs = module->get_localDefs();
        Defines::iterator diter = defs.find(key);
        if (diter != defs.end()) {
            return (*diter).second;
        }
    }

    { /* variables */
        Variables vars = module->get_localVars();
        Variables::iterator viter = vars.find(key);
        if (viter != vars.end()) {
            return (*viter).second;
        }
    }

    // if all of the above fail...
    WARN << "Could not resolve symbol " << ctx << "::" << symb << endl;
    throw UnresolvedSymbol(ctx, symb);
}
