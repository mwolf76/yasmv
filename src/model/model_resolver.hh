/**
 * @file model_resolver.hh
 * @brief Symbol resolution module
 *
 * This header file contains the declarations required to implement
 * the resolution of model symbols.
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

#ifndef MODEL_RESOLVER_H
#define MODEL_RESOLVER_H

#include <symb/resolver.hh>

class ModelMgr; // fwd
class ModelResolver : public Resolver {
public:
    ModelResolver(ModelMgr& owner);
    ~ModelResolver();

    void add_symbol(const Expr_ptr key, Symbol_ptr symb);
    Symbol_ptr symbol(const Expr_ptr key);

private:
    ModelMgr& f_owner;
    Constants f_constants; // global consts
};

#endif /* MODEL_RESOLVER_H */
