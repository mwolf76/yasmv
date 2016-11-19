/*
 * @file environment.hh
 * @brief Command environment subsystem implementation.
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

#include <environment.hh>

#include <utils/misc.hh>

const char* NoSuchIdentifier::what() const throw() {
    std::ostringstream oss;
    oss
        << "No such identifier: `" << f_id << "`";

    return oss2cstr(oss);
}

Environment_ptr Environment::f_instance = NULL;
Environment& Environment::INSTANCE()
{
    if (! f_instance)
        f_instance = new Environment();

    return *f_instance;
}

Expr_ptr Environment::get(Expr_ptr id) const
{
    Expr2ExprMap::const_iterator eye
        (f_env.find(id));

    if (eye == f_env.end())
        throw NoSuchIdentifier(id);

    /* NULL value means deleted entry */
    if (! eye -> second)
        throw NoSuchIdentifier(id);

    return eye -> second; /* non-NULL */
}

void Environment::set(Expr_ptr id, Expr_ptr value)
{
    if (value)
        f_identifiers.insert(id);
    else
        f_identifiers.erase(id);

    Expr2ExprMap::const_iterator eye
        (f_env.find(id));

    if (eye != f_env.end())
        f_env.erase(eye);

    f_env.insert(std::make_pair<Expr_ptr, Expr_ptr> (id, value));
}

void Environment::clear()
{
    f_identifiers.clear();
    f_env.clear();
}

void Environment::add_extra_init(Expr_ptr constraint)
{
    assert(constraint);
    f_extra_inits.push_back(constraint);
}

void Environment::add_extra_invar(Expr_ptr constraint)
{
    assert(constraint);
    f_extra_invars.push_back(constraint);
}

void Environment::add_extra_trans(Expr_ptr constraint)
{
    assert(constraint);
    f_extra_transes.push_back(constraint);
}
