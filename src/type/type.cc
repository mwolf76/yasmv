/**
 *  @file type.cc
 *  @brief Type system classes
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

#include <type.hh>

ostream& operator<<(ostream& os, Type_ptr type_ptr)
{
    return os << type_ptr->get_repr();
}

bool EnumType::has_symbs() const
{
    bool res = false;
    ExprMgr& em = ExprMgr::INSTANCE();

    for (ExprSet::iterator eye = f_literals.begin();
         (!res) && (eye != f_literals.end()); eye ++) {

        res |= em.is_identifier(*eye);
    }

    return res;
}

bool EnumType::has_numbers() const
{
    bool res = false;
    ExprMgr& em = ExprMgr::INSTANCE();

    for (ExprSet::iterator eye = f_literals.begin();
         (!res) && (eye != f_literals.end()); eye ++) {

        res |= em.is_numeric(*eye);
    }

    return res;
}
