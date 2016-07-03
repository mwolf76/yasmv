/*
 * @file environment.hh
 * @brief Command environment subsystem related classes and definitions.
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
 *  Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/
#ifndef ENVIRONMENT_H
#define ENVIRONMENT_H

#include <expr/expr.hh>

#include <iostream>
#include <boost/unordered_map.hpp>

#include <common.hh>
#include <utils/pool.hh>

/* key -> value map for env */
typedef boost::unordered_map<Expr_ptr, Expr_ptr, PtrHash, PtrEq> Expr2ExprMap;

typedef class Environment* Environment_ptr;

class NoSuchIdentifier : public Exception
{
public:
    NoSuchIdentifier(Expr_ptr id)
        : f_id(id)
    {}

    virtual const char* what() const throw() {
        std::ostringstream oss;
        oss
            << "No such identifier: `" << f_id << "`";

        return oss.str().c_str();
    }

private:
    Expr_ptr f_id;
};

class Environment {
public:
    // singleton
    static Environment& INSTANCE();

    Expr_ptr get(Expr_ptr id) const;
    void set(Expr_ptr id, Expr_ptr value); /* use NULL to unset */

    void clear();

    inline const ExprSet& identifiers() const
    { return f_identifiers; }

private:
    Expr2ExprMap f_env;
    ExprSet f_identifiers;

    Expr2ExprMap::iterator f_env_iter;

    static Environment_ptr f_instance;
};

#endif
