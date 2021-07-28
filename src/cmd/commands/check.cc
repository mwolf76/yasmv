/**
 * @file check.cc
 * @brief Command `check` class implementation.
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

#include <cstdlib>
#include <cstring>

#include <cmd/commands/commands.hh>
#include <cmd/commands/check.hh>

#include <algorithms/check/check.hh>

namespace cmd {

Check::Check(Interpreter& owner)
    : Command(owner)
    , f_out(std::cout)
{}

Check::~Check()
{}

void Check::set_property(expr::Expr_ptr property)
{
    f_property = property;
}

void Check::add_constraint(expr::Expr_ptr constraint)
{
    f_constraints.push_back(constraint);
}

bool Check::check_requirements()
{
    model::ModelMgr& mm
        (model::ModelMgr::INSTANCE());

    model::Model& model
         (mm.model());

    if (0 == model.modules().size()) {
        f_out
            << wrnPrefix
            << "Model not loaded."
            << std::endl;

        return false;
    }

    return true;
}

utils::Variant Check::operator()()
{
    bool res { false };

    DEBUG
        << "Property to check is `"
        << f_property
        << "`."
        << std::endl;

    return utils::Variant(res ? okMessage : errMessage);
}

CheckTopic::CheckTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

CheckTopic::~CheckTopic()
{
    TRACE
        << "Destroyed check topic"
        << std::endl;
}

void CheckTopic::usage()
{ display_manpage("check"); }

};
