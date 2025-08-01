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

#include <expr/time/analyzer/analyzer.hh>

#include <cmd/commands/commands.hh>
#include <cmd/commands/dump_trace.hh>
#include <cmd/commands/reach.hh>

namespace cmd {

    Reach::Reach(Interpreter& owner)
        : Command(owner)
        , f_out(std::cout)
        , f_target(nullptr)
        , f_quiet(false)
    {}

    Reach::~Reach()
    {
        f_constraints.clear();
    }

    void Reach::set_target(expr::Expr_ptr target)
    {
        f_target = target;
    }

    void Reach::add_constraint(expr::Expr_ptr constraint)
    {
        expr::time::Analyzer eta { expr::ExprMgr::INSTANCE() };
        eta.process(constraint);

        if (eta.has_forward_time()) {
            TRACE
                << "Adding FORWARD constraint to reachability problem: "
                << constraint
                << std::endl;
        } else if (eta.has_backward_time()) {
            TRACE
                << "Adding BACKWARD constraint to reachability problem: "
                << constraint
                << std::endl;
        } else {
            TRACE
                << "Adding GLOBAL constraint to reachability problem: "
                << constraint
                << std::endl;
        }

        f_constraints.push_back(constraint);
    }

    void Reach::go_quiet()
    {
        f_quiet = true;
    }

    bool Reach::check_requirements() const
    {
        if (!f_target) {
            f_out
                << wrnPrefix
                << "No target given. Aborting..."
                << std::endl;

            return false;
        }

        model::ModelMgr& mm { model::ModelMgr::INSTANCE() };
        model::Model& model { mm.model() };
        if (model.empty()) {
            f_out
                << wrnPrefix
                << "Model not loaded."
                << std::endl;

            return false;
        }

        return true;
    }

    utils::Variant Reach::operator()()
    {
        opts::OptsMgr& om { opts::OptsMgr::INSTANCE() };
        model::ModelMgr& mm { model::ModelMgr::INSTANCE() };
        bool res { false };

        if (!check_requirements()) {
            return utils::Variant { errMessage };
        }

        reach::Reachability bmc { *this, mm.model() };
        bmc.process(f_target, f_constraints);

        switch (bmc.status()) {
            case reach::reachability_status_t::REACHABILITY_REACHABLE:
                if (!om.quiet()) {
                    f_out
                        << outPrefix;
                }
                if (!f_quiet) {
                    f_out
                        << "Target is reachable";
                }

                if (bmc.has_witness()) {
                    witness::Witness& w { bmc.witness() };

                    if (!f_quiet) {
                        f_out
                            << ", registered witness `"
                            << w.id()
                            << "`, "
                            << w.size()
                            << " steps."
                            << std::endl;

                        DumpTrace { this->f_owner }();
                    }
                }
                res = true;
                break;

            case reach::reachability_status_t::REACHABILITY_UNREACHABLE:
                if (!om.quiet()) {
                    f_out
                        << wrnPrefix;
                }
                if (!f_quiet) {
                    f_out
                        << "Target is unreachable."
                        << std::endl;
                }
                break;

            case reach::reachability_status_t::REACHABILITY_UNKNOWN:
                if (!om.quiet()) {
                    f_out
                        << outPrefix;
                }

                // cannot be quiet about undecidability
                f_out
                    << "Reachability could not be decided."
                    << std::endl;
                break;

            case reach::reachability_status_t::REACHABILITY_ERROR:
                if (!om.quiet()) {
                    f_out
                        << outPrefix;
                }

                // cannot be quiet about errors
                f_out
                    << "Unexpected error."
                    << std::endl;
                break;

            default:
                assert(false); /* unexpected */
        }

        return utils::Variant { res ? okMessage : errMessage };
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
        display_manpage("reach");
    }

} // namespace cmd
