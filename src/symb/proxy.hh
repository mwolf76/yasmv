/**
 *  @file proxy.hh
 *  @brief Resolver proxy
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

#ifndef RESOLVER_PROXY_H
#define RESOLVER_PROXY_H

#include <symb/resolver.hh>

#include <type/type_mgr.hh>

#include <model/model_mgr.hh>


class ResolverProxy : public Resolver {
    TypeMgr& f_tm;
    ModelMgr& f_mm;

public:
    ResolverProxy()
        : f_tm(TypeMgr::INSTANCE())
        , f_mm(ModelMgr::INSTANCE())
    {}

    /** @brief register a symbol in the underlying storage */
    void add_symbol(const Expr_ptr ctx, const Expr_ptr expr, Symbol_ptr symb)
    { assert(false); } // proxy is used read-only

    /** @brief fetch a symbol */
    Symbol_ptr symbol(const Expr_ptr ctx, const Expr_ptr expr)
    {
        Symbol_ptr res = NULL;

        res = f_tm.resolver()->symbol(ctx, expr);
        if (NULL != res)
            return res;

        res = f_mm.resolver()->symbol(ctx, expr);
        if (NULL != res)
            return res;

        /* if all of the above fail... */
        WARN
            << "Could not resolve symbol "
            << ctx << "::" << expr
            << std::endl;

        throw UnresolvedSymbol(ctx, expr);
    }
};

#endif
