/**
 * @file check_init.cc
 * @brief Command `check-init` class implementation.
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
#include <cmd/commands/check_init.hh>

#include <algorithms/fsm/fsm.hh>

CheckInit::CheckInit(Interpreter& owner)
    : Command(owner)
    , f_out(std::cout)
{}

CheckInit::~CheckInit()
{}

void CheckInit::add_constraint(Expr_ptr constraint)
{
    f_constraints.push_back(constraint);
}

bool CheckInit::check_requirements()
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

Variant CheckInit::operator()()
{
    OptsMgr& om
        (OptsMgr::INSTANCE());

    bool res { false };

    if (check_requirements()) {
        CheckInitConsistency check_init { *this,
                ModelMgr::INSTANCE().model() };
        check_init.process(f_constraints);

        switch (check_init.status()) {
        case FSM_CONSISTENCY_OK:
            if (! om.quiet())
                f_out
                    << outPrefix;
            f_out
                << "Initial states consistency check ok."
                << std::endl;

            res = true;
            break;

        case FSM_CONSISTENCY_KO:
            if (! om.quiet())
                f_out
                    << outPrefix;
            f_out
                << "Initial states consistency check failed."
                << std::endl;
            break;

        case FSM_CONSISTENCY_UNDECIDED:
            if (! om.quiet())
                f_out
                    << outPrefix;
            f_out
                << "Could not decide initial states consistency check."
                << std::endl;
            break;

        default: assert(false); /* unreachable */
        } /* switch */
    }

    return Variant(res ? okMessage : errMessage);
}

CheckInitTopic::CheckInitTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

CheckInitTopic::~CheckInitTopic()
{
    TRACE
        << "Destroyed check-init topic"
        << std::endl;
}

void CheckInitTopic::usage()
{
    std::cout
        << "check-init - Checks propositional satisfiability for INIT formulas.\n\n"
        << "Initial states are checked for consistency. Returns `OK` if initial\n"
        << "states are consistent, `KO` if initial are found to be inconsistent.\n"
        << "If no decision could be made returns `??`."
        << std::endl;
}
