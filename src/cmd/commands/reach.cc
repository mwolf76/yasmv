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
    , f_target(NULL)
{}

Reach::~Reach()
{}

void Reach::set_target(Expr_ptr target)
{
    f_target = target;
}

Variant Reach::operator()()
{
    OptsMgr& om { OptsMgr::INSTANCE() };
    std::ostream& out { std::cout };
    bool res { false };

    if (! f_target) {
        out
            << wrnPrefix
            << "No property given. Aborting..."
            << std::endl;

        return Variant(errMessage);
    }

    Model& model { ModelMgr::INSTANCE().model() };
    if (0 < model.modules().size()) {
        BMC bmc { *this, model };
        bmc.process(f_target);

        switch (bmc.status()) {
        case BMC_REACHABLE:
            res = true;
            if (! om.quiet())
                out
                    << outPrefix;
            out
                << "Target is reachable";

            if (bmc.has_witness()) {
                Witness& w
                    (bmc.witness());

                out
                    << ", registered witness `"
                    << w.id()
                    << "`, "
                    << w.size()
                    << " steps."
                    << std::endl;
            }
            break;

        case BMC_UNREACHABLE:
            if (! om.quiet())
                out
                    << wrnPrefix;
            out
                << "Target is unreachable."
                << std::endl;
            break;

        case BMC_UNKNOWN:
            out
                << "Reachability could not be decided."
                << std::endl;
            break;

        case BMC_ERROR:
            /* ssshhh... */
            break;

        default: assert(false); /* unexpected */
        }
    } else {
        out
            << wrnPrefix
            << "Model not loaded."
            << std::endl;
    }

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
