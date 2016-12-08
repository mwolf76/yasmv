/*
 * @file environment.hh
 * @brief Command environment subsystem related classes and definitions.
 *
 * This header file contains the declarations required to implement
 * the shell environment of user-defined assignments of INPUTs.
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

#ifndef ENVIRONMENT_H
#define ENVIRONMENT_H

#include <expr/expr.hh>

#include <iostream>
#include <boost/unordered_map.hpp>

#include <common/common.hh>
#include <utils/pool.hh>

/* key -> value map for env */
typedef boost::unordered_map<Expr_ptr, Expr_ptr, PtrHash, PtrEq> Expr2ExprMap;

typedef class Environment* Environment_ptr;

class EnvironmentException : public Exception
{
public:
    EnvironmentException(const std::string& subtype,
                         const std::string& message="")
        : Exception("EnvironmentException", subtype, message)
    {}
};

// helpers
std::string build_no_such_identifier_error_message(Expr_ptr expr);

class NoSuchIdentifier : public EnvironmentException
{
public:
    NoSuchIdentifier(Expr_ptr expr)
        : EnvironmentException("NoSuchIdentifier",
                               build_no_such_identifier_error_message(expr))
    {}
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

    void add_extra_init(Expr_ptr constraint);
    inline const ExprVector& extra_init() const
    { return f_extra_inits; }

    void add_extra_invar(Expr_ptr constraint);
    inline const ExprVector& extra_invar() const
    { return f_extra_invars; }

    void add_extra_trans(Expr_ptr constraint);
    inline const ExprVector& extra_trans() const
    { return f_extra_transes; }

private:

    /* input vars */
    Expr2ExprMap f_env;
    ExprSet f_identifiers;
    Expr2ExprMap::iterator f_env_iter;

    /* additional INIT, INVAR and TRANS constraints */
    ExprVector f_extra_inits;
    ExprVector f_extra_invars;
    ExprVector f_extra_transes;

    static Environment_ptr f_instance;
};

#endif /* ENVIRONMENT_H */
