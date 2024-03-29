/**
 * @file type_resolver.hh
 * @brief Symbol resolution module
 *
 * This module contains the declarations required by the Type Resolver
 * class.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/

#ifndef TYPE_RESOLVER_H
#define TYPE_RESOLVER_H

#include <common/common.hh>
#include <symb/resolver.hh>

namespace type {

    class TypeMgr;
    class TypeResolver: public symb::Resolver {
    public:
        TypeResolver(TypeMgr& owner);
        ~TypeResolver();

        symb::Symbol_ptr symbol(const expr::Expr_ptr key);

    private:
        TypeMgr& f_owner;
    };

}; // namespace type

#endif /* TYPE_RESOLVER_H */
