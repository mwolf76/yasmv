/**
 *  @file resolver.cc
 *  @brief Symbol resolution module
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

#include <type.hh>
#include <type_mgr.hh>
#include <type_resolver.hh>

TypeResolver::TypeResolver(TypeMgr& owner)
    : f_owner(owner)
{
    DEBUG << "Initialized Type Resolver instance @" << this << endl;
}

TypeResolver::~TypeResolver()
{}

void TypeResolver::add_symbol(const Expr_ptr ctx, const Expr_ptr expr, ISymbol_ptr symb)
{
    assert (false); // TODO
}

ISymbol_ptr TypeResolver::symbol(const Expr_ptr ctx, const Expr_ptr expr)
{
    FQExpr key(ctx, expr, 0); // time arbitrarily set to 0.

    { /* enum types */
        const Enums& enums = TypeMgr::INSTANCE().enums();
        Enums::const_iterator iter = enums.find(key);
        if (iter != enums.end()) {
            return (*iter).second;
        }
    }

    { /* enum literals */
        const Literals& lits = TypeMgr::INSTANCE().literals();
        Literals::const_iterator iter = lits.find(key);
        if (iter != lits.end()) {
            return (*iter).second;
        }
    }

    return NULL; /* unresolved */
}
