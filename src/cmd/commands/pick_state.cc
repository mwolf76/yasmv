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
        , f_count(false)
        , f_limit(-1)
    {}

    PickState::~PickState()
    {}

    void PickState::set_allsat(const bool value)
    {
        f_allsat = value;
    }

    void PickState::set_count(const bool value)
    {
        f_count = value;
    }

    void PickState::set_limit(const value_t value)
    {
        f_limit = value;
    }

    void PickState::add_constraint(const expr::Expr_ptr constraint)
    {
        f_constraints.push_back(constraint);
    }

    bool PickState::check_requirements() const
    {
        model::ModelMgr& mm { model::ModelMgr::INSTANCE() };
        model::Model& model { mm.model() };

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

    void PickState::wrn_prefix() const
    {
        opts::OptsMgr& om { opts::OptsMgr::INSTANCE() };
        if (!om.quiet()) {
            f_out << wrnPrefix;
        }
    }

    void PickState::out_prefix() const
    {
        opts::OptsMgr& om { opts::OptsMgr::INSTANCE() };
        if (!om.quiet()) {
            f_out << outPrefix;
        }
    }

    utils::Variant PickState::operator()()
    {
        bool res { false };
        if (check_requirements()) {
            model::Model& model { model::ModelMgr::INSTANCE().model() };
            sim::Simulation simulation { *this, model };
            value_t states { simulation.pick_state(f_constraints, f_allsat, f_count, f_limit) };

            const expr::Expr_ptr model_name { model.main_module().name() };
            const size_t num_constraints { f_constraints.size() };

            if (0 == states) {
                wrn_prefix();
                f_out
                    << "Model `" << model_name << "` has no feasible initial states";
                if (num_constraints > 0) {
                    f_out << " (with " << num_constraints << " additional constraint" 
                          << (num_constraints > 1 ? "s" : "") << ")";
                }
                f_out << std::endl;
            } else if (1 == states) {
                res = true;
                out_prefix();
                f_out
                    << "Model `" << model_name << "` has only one feasible initial state";
                if (num_constraints > 0) {
                    f_out << " (with " << num_constraints << " additional constraint" 
                          << (num_constraints > 1 ? "s" : "") << ")";
                }
                f_out << std::endl;
            } else {
                res = true;
                out_prefix();
                f_out
                    << "Model `" << model_name << "` has " << states
                    << " feasible initial states";
                if (num_constraints > 0) {
                    f_out << " (with " << num_constraints << " additional constraint" 
                          << (num_constraints > 1 ? "s" : "") << ")";
                }
                f_out << std::endl;
            }
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
    {
        display_manpage("pick-state");
    }
}; // namespace cmd
