/**
 *  @file resolver.hh
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

#ifndef RESOLVER_H
#define RESOLVER_H

#include <common.hh>

#include <expr.hh>
#include <expr_mgr.hh>

#include <type.hh>
#include <enc.hh>

#include <model.hh>

class ModelMgr;
class IResolver : public IObject {
public:
    /* fetch a symbol (model or temporary) */
    virtual ISymbol_ptr fetch_symbol(const Expr_ptr ctx, const Expr_ptr symb) =0;
    virtual void register_temporary(const Expr_ptr expr, ITemporary_ptr temp) =0;
};

typedef IResolver* IResolver_ptr;

class Resolver : public IResolver {
public:
    Resolver(ModelMgr& owner);
    ~Resolver();

    ISymbol_ptr fetch_symbol(const Expr_ptr ctx, const Expr_ptr symb);
    void register_temporary(const Expr_ptr symb, ITemporary_ptr temp);

private:
    ModelMgr& f_owner;

    Temporaries f_temporaries;
    Constants f_constants; // global consts
};

#endif
