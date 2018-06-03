/*
 * @file reach.cc
 * @brief Command `reach` class implementation.
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
#include <cmd/commands/reach.hh>

Reach::Reach(Interpreter& owner)
    : Command(owner)
    , f_out(std::cout)
    , f_target(NULL)
    , f_constraints()
{}

Reach::~Reach()
{
    f_constraints.clear();
}

void Reach::set_target(Expr_ptr target)
{
    f_target = target;
}

void Reach::add_constraint(Expr_ptr constraint)
{
    f_constraints.push_back(constraint);
}

bool Reach::check_requirements()
{
    ModelMgr& mm
        (ModelMgr::INSTANCE());

    Model& model
        (mm.model());

    if (! f_target) {
        f_out
            << wrnPrefix
            << "No target given. Aborting..."
            << std::endl;

        return false;
    }

    if (0 == model.modules().size()) {
        f_out
            << wrnPrefix
            << "Model not loaded."
            << std::endl;

        return false;
    }

    return true;
}

Variant Reach::operator()()
{
    OptsMgr& om
        (OptsMgr::INSTANCE());

    bool res { false };

    if (! check_requirements())
        return Variant(errMessage);

    BMC bmc { *this, ModelMgr::INSTANCE().model() };
    bmc.process(f_target, f_constraints);

    switch (bmc.status()) {
    case BMC_REACHABLE:
        if (! om.quiet())
            f_out
                << outPrefix;
        f_out
            << "Target is reachable";

        if (bmc.has_witness()) {
            Witness& w
                (bmc.witness());

            f_out
                << ", registered witness `"
                << w.id()
                << "`, "
                << w.size()
                << " steps."
                << std::endl;
        }
        res = true;
        break;

    case BMC_UNREACHABLE:
        if (! om.quiet())
            f_out
                << wrnPrefix;
        f_out
            << "Target is unreachable."
            << std::endl;
        break;

    case BMC_UNKNOWN:
        f_out
            << "Reachability could not be decided."
            << std::endl;
        break;

    case BMC_ERROR:
        f_out
            << "Unexpected error."
            << std::endl;

        break;

    default: assert(false); /* unexpected */
    } /* switch */

    return Variant(res ? okMessage : errMessage);
}

ReachTopic::ReachTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

ReachTopic::~ReachTopic()
{
    TRACE
        << "Destroyed check-target topic"
        << std::endl;
}

void ReachTopic::usage()
{
    std::cout
        << "reach < expression > - Verify reachability of given expression.\n\n"
        << "If a state satisfying the target expression is unreachable yields TRUE.\n"
        << "Otherwise, a BMC counterexample witness trace for the given property is generated.\n" ;
}
