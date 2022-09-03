/**
 * @file proxy.hh
 * @brief Resolver proxy
 *
 * This header file contains the declarations required by the Resolver
 * Proxy class.
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

#ifndef RESOLVER_PROXY_H
#define RESOLVER_PROXY_H

#include <expr/expr.hh>

#include <symb/exceptions.hh>
#include <symb/resolver.hh>
#include <symb/typedefs.hh>

#include <type/type_mgr.hh>

#include <model/model_mgr.hh>

namespace symb {

    class ResolverProxy: public Resolver {
        type::TypeMgr& f_tm;
        model::ModelMgr& f_mm;

    public:
        ResolverProxy()
            : f_tm(type::TypeMgr::INSTANCE())
            , f_mm(model::ModelMgr::INSTANCE())
        {}

        /** @brief register a symbol in the underlying storage */
        void add_symbol(const expr::Expr_ptr ctx, const expr::Expr_ptr expr, Symbol_ptr symb)
        {
            assert(false);
        } // proxy is used read-only

        /** @brief fetch a symbol */
        Symbol_ptr symbol(const expr::Expr_ptr key)
        {
            Symbol_ptr res = NULL;

            res = f_tm.resolver()->symbol(key);
            if (NULL != res)
                return res;

            res = f_mm.resolver()->symbol(key);
            if (NULL != res)
                return res;

            throw UnresolvedSymbol(key);
        }
    };

}; // namespace symb

#endif /* RESOLVER_PROXY_H */
