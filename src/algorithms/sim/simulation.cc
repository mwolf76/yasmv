/**
 * @file simulation.cc
 * @brief SAT-based BMC simulation algorithm implementation.
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

#include <sstream>

#include <compiler/typedefs.hh>

#include <sim/simulation.hh>

#include <symb/typedefs.hh>
#include <symb/classes.hh>
#include <symb/symb_iter.hh>

namespace sim {

    // reserved for witnesses
    static unsigned progressive = 0;
    static const char *simulation_trace_prfx = "sim-";

    Simulation::Simulation(cmd::Command &command, model::Model &model)
    : Algorithm(command, model) {
        const void *instance{this};
        TRACE
        << "Created Simulation @"
        << instance
        << std::endl;
    }

    Simulation::~Simulation() {
        const void *instance{this};
        TRACE
        << "Destroyed Simulation @"
        << instance
        << std::endl;
    }

    void Simulation::extract_witness(sat::Engine &engine, bool select_current_witness) {
        witness::WitnessMgr &wm{witness::WitnessMgr::INSTANCE()};
        witness::Witness_ptr w{new SimulationWitness(model(), engine, 0)};

        {
            std::ostringstream oss;
            oss
            << simulation_trace_prfx
            << (++progressive);

            w->set_id(oss.str());
        }

        {
            std::ostringstream oss;

            oss
            << "Simulation trace for module `"
            << model().main_module().name()
            << "`";

            w->set_desc(oss.str());
        }

        wm.record(*w);
        if (select_current_witness) {
            set_witness(*w);
            wm.set_current(*w);
        }
    }

    void Simulation::exclude_state(sat::Engine &engine) {
        /* In ALLSAT mode, for each bit int the encoding, fetch UCBI, time it into TCBI at time 0, fetch its
           value in MiniSAT model and negate it in the exclusion clause. */
        enc::EncodingMgr &enc_mgr{enc::EncodingMgr::INSTANCE()};

        vec <Lit> exclusion;
        symb::SymbIter symbols{model()};

        while (symbols.has_next()) {
            std::pair<expr::Expr_ptr, symb::Symbol_ptr> pair{symbols.next()};

            expr::Expr_ptr ctx{pair.first};
            symb::Symbol_ptr symb{pair.second};
            expr::Expr_ptr symb_name{symb->name()};
            expr::Expr_ptr key{em().make_dot(ctx, symb_name)};

            if (symb->is_variable()) {
                symb::Variable &var{symb->as_variable()};

                /* INPUT vars are not really vars ... */
                if (var.is_input()) {
                    continue;
                }

                /* time it, and fetch encoding for enc mgr */
                enc::Encoding_ptr enc{enc_mgr.find_encoding(expr::TimedExpr(key, 0))};

                if (!enc) {
                    continue;
                }

                /* for each bit in this encoding, fetch UCBI, time it into TCBI at time 0, fetch its
                   value in MiniSAT model and append its negation to exclusion clause. */
                dd::DDVector::const_iterator di;
                unsigned ndx;
                for (ndx = 0, di = enc->bits().begin();
                enc->bits().end() != di; ++ndx, ++di) {
                    unsigned bit{(*di).getNode()->index};
                    const enc::UCBI &ucbi{enc_mgr.find_ucbi(bit)};
                    const enc::TCBI tcbi{enc::TCBI(ucbi, 0)};

                    Var var{engine.tcbi_to_var(tcbi)};
                    exclusion.push(mkLit(var, engine.value(var)));
                }
            }

            /* add exclusion clause to SAT instance */
            engine.add_clause(exclusion);
        }
    }

    value_t Simulation::pick_state(expr::ExprVector constraints,
                                   bool all_sat, bool count, value_t limit) {

        value_t feasible {0};

        clock_t t0{clock()}, t1;
        double secs;

        sat::Engine engine{"pick_state"};
        expr::Expr_ptr ctx{em().make_empty()};

        compiler::Units constraint_cus;
        unsigned no_constraints{0};

        std::for_each(
                begin(constraints),
                end(constraints),
                [this, ctx, &no_constraints, &constraint_cus](expr::Expr_ptr expr) {
                    INFO
                    << "Compiling constraint `"
                    << expr
                    << "` ..."
                    << std::endl;

                    compiler::Unit unit{compiler().process(ctx, expr)};
                    constraint_cus.push_back(unit);
                    ++no_constraints;
                });

        INFO
        << no_constraints
        << " constraints found."
        << std::endl;

        /* INITs and INVARs at time 0 */
        assert_fsm_init(engine, 0);
        assert_fsm_invar(engine, 0);

        /* Additional constraints */
        std::for_each(
                begin(constraint_cus),
                end(constraint_cus),
                [this, &engine](compiler::Unit &cu) {
                    this->assert_formula(engine, 0, cu);
                });

        while (true) {
            if (sat::status_t::STATUS_SAT != engine.solve()) {
                break;
            }

            t1 = clock();
            secs = (double) (t1 - t0) / (double) CLOCKS_PER_SEC;

            TRACE
            << "found feasible initial state, took "
            << secs << " seconds"
            << std::endl;

            if (++ feasible >= limit) {
                TRACE
                << "Reached limit: "
                << limit
                << ", leaving."
                << std::endl;
                break;
            }

            if (!count) {
                extract_witness(engine, !all_sat);
            }

            if (!all_sat && !count) {
                /* no further work needed here ... */
                break;
            } else {
                exclude_state(engine);
            }
        } /* while (true) */

        TRACE
                << "Found "
                << feasible
                << " feasible states"
                << std::endl;

        return feasible;
    }

    simulation_status_t Simulation::simulate(expr::ExprVector constraints,
                                             pconst_char trace_name)
    {
        sat::status_t last_sat;

        clock_t t0{ clock() }, t1;
        double secs;

        sat::Engine engine {"simulation" };

        witness::WitnessMgr &wm { witness::WitnessMgr::INSTANCE() };
        expr::Atom trace_uid { trace_name ? expr::Atom(trace_name) : wm.current().id() };
        witness::Witness &trace { wm.witness(trace_uid) };

        set_witness(trace);

        // here we need to push all the values for variables in the last
        // state of resuming witness. A complete assignment to *all* state
        // variables guarantees full deterministic behavior.
        step_t init_time { trace.last_time() }, k { init_time };
        witness::TimeFrame &last { trace.last() };

        assert_time_frame(engine, k, last);

        /* inject full transition relation, trace may not be compatible
           with current state's INVARs */
        assert_fsm_invar(engine, k);
        assert_fsm_trans(engine, k);
        assert_fsm_invar(engine, 1 + k);

        DEBUG
        << "Running simulation..."
        << std::endl;

        if (sat::status_t::STATUS_SAT == (last_sat = engine.solve())) {
            ++k;

            t1 = clock();
            secs = (double) (t1 - t0) / (double) CLOCKS_PER_SEC;

            TRACE
            << "simulation completed step " << k
            << ", took " << secs << " seconds"
            << std::endl;

            t0 = t1; // resetting clock

            witness::Witness &w { *new SimulationWitness(model(), engine, k) };
            witness().extend(w);
        }

        if (sat::status_t::STATUS_SAT == last_sat) {
            INFO
                    << "Simulation completed."
                    << std::endl;

            return SIMULATION_DONE;
        }

        if (sat::status_t::STATUS_UNKNOWN == last_sat) {
            INFO
                    << "Simulation interrupted."
                    << std::endl;

            return SIMULATION_INTERRUPTED;
        }

        if (sat::status_t::STATUS_UNSAT == last_sat) {
            INFO
                    << "Inconsistency detected in transition relation at step " << k
                    << std::endl;

            return SIMULATION_DEADLOCKED;
        }

        return SIMULATION_UNKNOWN;
    }
} // namespace sim
