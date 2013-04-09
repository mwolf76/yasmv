/**
 *  @file meta_resolver.hh
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

#ifndef META_RESOLVER_H
#define META_RESOLVER_H

#include <resolver.hh>

class MetaResolver : public IResolver {
public:
    MetaResolver(TypeMgr& owner);
    ~MetaResolver();

    void add_symbol(const Expr_ptr ctx, const Expr_ptr expr, ISymbol_ptr symb);

    ISymbol_ptr fetch_symbol(const Expr_ptr ctx, const Expr_ptr symb);

private:
    TypeMgr& f_owner;
};

#endif
