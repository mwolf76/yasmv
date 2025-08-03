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

#include <symb/classes.hh>
#include <symb/symb_iter.hh>
#include <symb/typedefs.hh>

static unsigned progressive = 0;
static auto simulation_trace_prefix = "sim-";

namespace sim {
    Simulation::Simulation(cmd::Command& command, model::Model& model)
        : Algorithm(command, model)
    {
        const void* instance { this };
        TRACE
            << "Created Simulation @"
            << instance
            << std::endl;
    }

    Simulation::~Simulation()
    {
        const void* instance { this };
        TRACE
            << "Destroyed Simulation @"
            << instance
            << std::endl;
    }

    void Simulation::extract_witness(sat::Engine& engine, const bool select_current_witness)
    {
        witness::WitnessMgr& wm { witness::WitnessMgr::INSTANCE() };
        witness::Witness& w { *new SimulationWitness(model(), engine, 0) };

        {
            std::ostringstream oss;
            oss
                << simulation_trace_prefix
                << ++progressive;

            w.set_id(oss.str());
        }

        {
            std::ostringstream oss;

            oss
                << "Simulation trace for module `"
                << model().main_module().name()
                << "`";

            w.set_desc(oss.str());
        }

        wm.record(w);
        if (select_current_witness) {
            set_witness(w);
            wm.set_current(w);
        }
    }

    void Simulation::exclude_state(sat::Engine& engine)
    {
        /* In ALLSAT mode, for each bit int the encoding, fetch UCBI,
           time it into TCBI at time 0, fetch its value in MiniSAT
           model and negate it in the exclusion clause. */
        enc::EncodingMgr& bm { enc::EncodingMgr::INSTANCE() };

        vec<Lit> exclusion;
        symb::SymbIter symbols { model() };

        while (symbols.has_next()) {
            const auto [fst, snd] { symbols.next() };

            const expr::Expr_ptr ctx { fst };
            const symb::Symbol_ptr symb { snd };
            const expr::Expr_ptr symb_name { symb->name() };
            const expr::Expr_ptr key { em().make_dot(ctx, symb_name) };

            if (symb->is_variable()) {

                /* INPUT vars are not really vars ... */
                if (symb::Variable & var { symb->as_variable() }; var.is_input()) {
                    continue;
                }

                /* time it, and fetch encoding for enc mgr */
                const enc::Encoding_ptr enc {
                    bm.find_encoding(expr::TimedExpr(key, 0))
                };

                if (!enc) {
                    continue;
                }

                /* for each bit in this encoding, fetch UCBI, time it
                   into TCBI at time 0, fetch its value in MiniSAT
                   model and append its negation to exclusion
                   clause. */
                dd::DDVector::const_iterator di;
                unsigned ndx;
                for (ndx = 0, di = enc->bits().begin();
                     enc->bits().end() != di; ++ndx, ++di) {

                    const unsigned bit { di->getNode()->index };
                    const enc::UCBI& ucbi { bm.find_ucbi(bit) };
                    const auto tcbi { enc::TCBI(ucbi, 0) };

                    const Var minisat_var { engine.tcbi_to_var(tcbi) };
                    exclusion.push(mkLit(minisat_var, engine.value(minisat_var)));
                }
            }

            /* add exclusion clause to SAT instance */
            engine.add_clause(exclusion);
        }
    }

    value_t Simulation::pick_state(expr::ExprVector constraints,
                                   const bool all_sat,
                                   const bool count,
                                   const value_t limit)
    {
        value_t feasible { 0 };

        const clock_t t0 { clock() };

        sat::Engine engine { "pick_state" };
        expr::Expr_ptr ctx { em().make_empty() };

        compiler::Units constraint_cus;
        unsigned no_constraints { 0 };

        std::for_each(
            begin(constraints), end(constraints),
            [this, ctx, &no_constraints, &constraint_cus](expr::Expr_ptr expr) {
                INFO
                    << "Compiling constraint `"
                    << expr
                    << "` ..."
                    << std::endl;

                const compiler::Unit unit { compiler().process(ctx, expr) };
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
            begin(constraint_cus), end(constraint_cus),
            [this, &engine](compiler::Unit& cu) {
                this->assert_formula(engine, 0, cu);
            });

        while (true) {
            if (sat::status_t::STATUS_SAT != engine.solve()) {
                break;
            }

            const clock_t t1 = clock();
            double secs = static_cast<double>(t1 - t0) / static_cast<double>(CLOCKS_PER_SEC);

            TRACE
                << "found feasible initial state, took "
                << secs << " seconds"
                << std::endl;

            if (++feasible >= limit) {
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
            }

            exclude_state(engine);
        } /* while (true) */

        TRACE
            << "Found "
            << feasible
            << " feasible states"
            << std::endl;

        return feasible;
    }

    simulation_status_t Simulation::simulate(expr::ExprVector constraints,
                                             pconst_char trace_name,
                                             expr::Expr_ptr until_condition,
                                             step_t k_steps)
    {
        witness::WitnessMgr& wm { witness::WitnessMgr::INSTANCE() };
        sat::status_t last_sat = sat::status_t::STATUS_UNKNOWN;

        const clock_t t0 { clock() };

        sat::Engine engine { "simulation" };
        expr::Expr_ptr ctx { em().make_empty() };

        compiler::Units constraint_cus;
        unsigned no_constraints { 0 };
        bool has_until { until_condition != nullptr };

        // Compile constraints
        std::for_each(
            begin(constraints), end(constraints),
            [this, ctx, &no_constraints, &constraint_cus](expr::Expr_ptr expr) {
                INFO
                    << "Compiling constraint `"
                    << expr
                    << "` ..."
                    << std::endl;

                const compiler::Unit unit { compiler().process(ctx, expr) };
                constraint_cus.push_back(unit);
                ++no_constraints;
            });

        INFO
            << no_constraints
            << " constraints found."
            << std::endl;


        // Default k_steps to 1 if not specified
        if (k_steps == 0) {
            k_steps = 1;
        }

        INFO
            << "Simulating up to "
            << k_steps
            << " steps";
        
        if (has_until) {
            INFO
                << " or until condition is satisfied";
        }
        
        INFO
            << std::endl;

        const expr::Atom trace_uid {
            trace_name ? expr::Atom(trace_name) : wm.current().id()
        };
        witness::Witness& trace { wm.witness(trace_uid) };

        set_witness(trace);

        const step_t init_time { trace.last_time() };
        step_t k { init_time };

        // Main simulation loop
        for (step_t step = 0; step < k_steps; ++step) {
            step_t current_step = step + 1;
            DEBUG
                << "Running simulation step "
                << current_step
                << " of "
                << k_steps
                << "..."
                << std::endl;

            // Get current state from witness
            witness::TimeFrame& current_frame { witness().last() };
            
            // Push current state
            assert_time_frame(engine, k, current_frame);

            // Assert invariants and transition relation
            assert_fsm_invar(engine, k);
            assert_fsm_trans(engine, k);
            assert_fsm_invar(engine, k + 1);

            // Apply constraints at current time
            std::for_each(
                begin(constraint_cus), end(constraint_cus),
                [this, &engine, k](compiler::Unit& cu) {
                    this->assert_formula(engine, k, cu);
                });

            // Solve for next state
            last_sat = engine.solve();

            if (sat::status_t::STATUS_SAT == last_sat) {
                ++k;

                const clock_t t1 = clock();
                double secs = static_cast<double>(t1 - t0) / static_cast<double>(CLOCKS_PER_SEC);

                TRACE
                    << "simulation completed step " << k
                    << ", took " << secs << " seconds"
                    << std::endl;

                // Create new witness state
                witness::Witness& w { *new SimulationWitness(model(), engine, k) };
                witness().extend(w);


                // Check until condition if provided
                if (has_until) {
                    // Evaluate the until condition in the current state
                    witness::WitnessMgr& wm { witness::WitnessMgr::INSTANCE() };
                    expr::Expr_ptr result { wm.eval(witness(), em().make_empty(), until_condition, k) };
                    
                    // Check if the result is TRUE
                    if (em().is_true(result)) {
                        INFO
                            << "Until condition satisfied at step "
                            << k
                            << std::endl;
                        
                        return SIMULATION_DONE;
                    }
                }
            } else {
                // Simulation cannot continue
                break;
            }
        }

        // Determine final status
        if (sat::status_t::STATUS_SAT == last_sat) {
            step_t total_steps = k - init_time;
            INFO
                << "Simulation completed "
                << total_steps
                << " steps."
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
