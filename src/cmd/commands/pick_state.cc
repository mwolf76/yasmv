/**
 * @file pick_state.cc
 * @brief Command `pick-state` class implementation.
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

#include <cmd/commands/commands.hh>
#include <cmd/commands/pick_state.hh>

namespace cmd {

PickState::PickState(Interpreter& owner)
    : Command(owner)
    , f_out(std::cout)
    , f_allsat(false)
    , f_limit(-1)
{}

PickState::~PickState()
{}

void PickState::set_allsat(bool allsat)
{
    f_allsat = allsat;
}

void PickState::set_limit(value_t limit)
{
    f_limit = limit;
}

void PickState::add_constraint(expr::Expr_ptr constraint)
{
    f_constraints.push_back(constraint);
}

bool PickState::check_requirements()
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

utils::Variant PickState::operator()()
{
    opts::OptsMgr& om
        (opts::OptsMgr::INSTANCE());

    bool res { false };

    if (check_requirements()) {

        sim::Simulation simulation { *this, ModelMgr::INSTANCE().model() };
        simulation.pick_state(f_allsat, f_limit, f_constraints);

        switch (simulation.status()) {
        case sim::simulation_status_t::SIMULATION_DONE:
            res = true;
            if (! om.quiet())
                f_out
                    << outPrefix;
            f_out
                << "Simulation done";

            assert (simulation.has_witness());
            f_out
                << ", registered witness `"
                << simulation.witness().id()
                << "`"
                << std::endl;
            break;

        case sim::simulation_status_t::SIMULATION_INITIALIZED:
            res = true;
            if (! om.quiet())
                f_out
                    << outPrefix;
            f_out
                << "Simulation initialized" ;

            assert (simulation.has_witness());
            f_out
                << ", registered witness `"
                << simulation.witness().id()
                << "`"
                << std::endl;
            break;

        case sim::simulation_status_t::SIMULATION_DEADLOCKED:
            if (! om.quiet())
                f_out
                    << wrnPrefix;
            f_out
                << "Simulation deadlocked"
                << std::endl;
            break;

        case sim::simulation_status_t::SIMULATION_INTERRUPTED:
            if (! om.quiet())
                f_out
                    << wrnPrefix;
            f_out
                << "Simulation interrupted"
                << std::endl;
            break;

        default: assert( false ); /* unreachable */
        } /* switch */
    }

    return utils::Variant(res ? okMessage : errMessage);
}

PickStateTopic::PickStateTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

PickStateTopic::~PickStateTopic()
{
    TRACE
        << "Destroyed pick-state topic"
        << std::endl;
}

void PickStateTopic::usage()
{ display_manpage("pick-state"); }

};
