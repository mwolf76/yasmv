/**
 * @file type_resolver.cc
 * @brief Type resolution module
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

#include <type/type.hh>
#include <type/type_mgr.hh>
#include <type/type_resolver.hh>

#include <symb/classes.hh>
#include <symb/typedefs.hh>

#include <utils/logging.hh>

namespace type {

    TypeResolver::TypeResolver(TypeMgr& owner)
        : f_owner(owner)
    {
        const void* instance { this };
        DEBUG
            << "Initialized Type Resolver instance @"
            << instance
            << std::endl;
    }

    TypeResolver::~TypeResolver()
    {
        const void* instance { this };
        DEBUG
            << "Destroyed Type Resolver instance @"
            << instance
            << std::endl;
    }

    symb::Symbol_ptr TypeResolver::symbol(const expr::Expr_ptr key)
    {
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };
        assert(em.is_dot(key));

        /* Types are globally scoped */
        expr::Expr_ptr key_ {
            em.make_dot(em.make_empty(), key->rhs())
        };

        const symb::Literals& lits {
            TypeMgr::INSTANCE().literals()
        };

        symb::Literals::const_iterator iter { lits.find(key_) };

        if (iter != lits.end()) {
            return dynamic_cast<symb::Symbol_ptr>((*iter).second);
        }

        return NULL; /* unresolved */
    }

}; // namespace type
