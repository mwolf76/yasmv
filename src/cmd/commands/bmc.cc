/**
 * @file bmc.cc
 * @brief Command `bmc` class implementation.
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
#include <cmd/commands/bmc.hh>

#include <algorithms/bmc/bmc.hh>

Bmc::Bmc(Interpreter& owner)
    : Command(owner)
    , f_out(std::cout)
{}

Bmc::~Bmc()
{}

void Bmc::add_constraint(Expr_ptr constraint)
{
    f_constraints.push_back(constraint);
}

bool Bmc::check_requirements()
{
    ModelMgr& mm
        (ModelMgr::INSTANCE());

    Model& model
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

Variant Bmc::operator()()
{
    bool res { false };

    return Variant(res ? okMessage : errMessage);
}

BmcTopic::BmcTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

BmcTopic::~BmcTopic()
{
    TRACE
        << "Destroyed bmc topic"
        << std::endl;
}

void BmcTopic::usage()
{ display_manpage("bmc"); }

