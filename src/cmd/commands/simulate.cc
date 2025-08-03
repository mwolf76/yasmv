/*
 * @file simulate.cc
 * @brief Command `simulate` class implementation.
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

#include <cmd/commands/commands.hh>
#include <cmd/commands/simulate.hh>

namespace cmd {

    Simulate::Simulate(Interpreter& owner)
        : Command(owner)
        , f_out(std::cout)
        , f_until_condition(nullptr)
        , f_k(1)
        , f_trace_uid(nullptr)
    {}


    Simulate::~Simulate()
    {
        free(f_trace_uid);
        f_trace_uid = nullptr;
    }

    void Simulate::add_constraint(const expr::Expr_ptr constraint)
    {
        f_constraints.push_back(constraint);
    }

    void Simulate::set_until_condition(const expr::Expr_ptr until_condition)
    {
        f_until_condition = until_condition;
    }

    void Simulate::set_trace_uid(const pconst_char trace_uid)
    {
        free(f_trace_uid);
        f_trace_uid = strdup(trace_uid);
    }

    void Simulate::set_k(step_t k)
    {
        f_k = k;
    }

    utils::Variant Simulate::operator()()
    {
        const opts::OptsMgr& om { opts::OptsMgr::INSTANCE() };
        model::ModelMgr& mm { model::ModelMgr::INSTANCE() };

        sim::Simulation simulation(*this, mm.model());

        bool res { false };

        const sim::simulation_status_t rc {
            simulation.simulate(f_constraints, f_trace_uid, f_until_condition, f_k)
        };

        switch (rc) {
            case sim::simulation_status_t::SIMULATION_DONE:
                res = true;
                if (!om.quiet()) {
                    f_out
                        << outPrefix;
                }

                f_out
                    << "Simulation done"
                    << std::endl;
                break;

            case sim::simulation_status_t::SIMULATION_DEADLOCKED:
                if (!om.quiet()) {
                    f_out
                        << wrnPrefix;
                }

                f_out
                    << "Simulation deadlocked"
                    << std::endl;
                break;

            case sim::simulation_status_t::SIMULATION_INTERRUPTED:
                if (!om.quiet()) {
                    f_out
                        << wrnPrefix;
                }

                f_out
                    << "Simulation interrupted"
                    << std::endl;
                break;

            default:
                assert(false); /* unreachable */
        }

        return utils::Variant(res ? okMessage : errMessage);
    }

    SimulateTopic::SimulateTopic(Interpreter& owner)
        : CommandTopic(owner)
    {}

    SimulateTopic::~SimulateTopic()
    {
        TRACE
            << "Destroyed simulate topic"
            << std::endl;
    }

    void SimulateTopic::usage()
    {
        display_manpage("simulate");
    }

}; // namespace cmd
