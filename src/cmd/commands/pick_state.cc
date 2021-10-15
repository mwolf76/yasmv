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

    PickState::PickState(Interpreter &owner)
            : Command(owner), f_out(std::cout), f_allsat(false), f_count(false), f_limit(-1)
    {}

    PickState::~PickState() {}

    void PickState::set_allsat(bool allsat) {
        f_allsat = allsat;
    }

    void PickState::set_count(bool count) {
        f_count = count;
    }

    void PickState::set_limit(value_t limit) {
        f_limit = limit;
    }

    void PickState::add_constraint(expr::Expr_ptr constraint) {
        f_constraints.push_back(constraint);
    }

    bool PickState::check_requirements() {
        model::ModelMgr &mm
                (model::ModelMgr::INSTANCE());

        model::Model &model
                (mm.model());

        if (0 == model.modules().size()) {
            f_out
                    << wrnPrefix
                    << "Model not loaded."
                    << std::endl;

            return false;
        }

        if (f_allsat && f_count) {
            f_out
                    << wrnPrefix
                    << "ALLSAT counting and enumeration are mutually exclusive."
                    << std::endl;

            return false;
        }

        return true;
    }

    void PickState::wrn_prefix() {
        opts::OptsMgr &om{opts::OptsMgr::INSTANCE()};
        if (!om.quiet()) {
            f_out << wrnPrefix;
        }
    }

    void PickState::out_prefix() {
        opts::OptsMgr &om{opts::OptsMgr::INSTANCE()};
        if (!om.quiet()) {
            f_out << outPrefix;
        }
    }

    utils::Variant PickState::operator()() {
        bool res{false};
        if (check_requirements()) {
            sim::Simulation simulation{*this, model::ModelMgr::INSTANCE().model()};
            value_t states{ simulation.pick_state(f_constraints, f_allsat, f_count, f_limit) };

            if (0 == states) {
                wrn_prefix();
                f_out
                        << "No feasible initial states found"
                        << std::endl;
            } else if (1 == states) {
                res = true;
                out_prefix();
                f_out
                        << "One feasible initial state found"
                        << std::endl;
            } else {
                res = true;
                out_prefix();
                f_out
                        << states
                        << " feasible initial states"
                        << std::endl;
            }
        }

        return utils::Variant(res ? okMessage : errMessage);
    }

    PickStateTopic::PickStateTopic(Interpreter & owner)
            : CommandTopic(owner) {}

    PickStateTopic::~PickStateTopic()
    {
        TRACE
                << "Destroyed pick-state topic"
                << std::endl;
    }

    void PickStateTopic::usage() { display_manpage("pick-state"); }
};
