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

#include <model/compiler/typedefs.hh>

#include <sim/simulation.hh>

#include <symb/typedefs.hh>
#include <symb/classes.hh>
#include <symb/symb_iter.hh>

namespace sim {

// reserved for witnesses
static unsigned progressive = 0;
static const char *simulation_trace_prfx = "sim_";

Simulation::Simulation(cmd::Command& command, model::Model& model)
    : Algorithm(command, model)
{
    setup();

    if (!ok())
        throw FailedSetup();
}

Simulation::~Simulation()
{}

void Simulation::pick_state(bool allsat,
                            value_t limit,
                            expr::ExprVector constraints)
{
    enc::EncodingMgr& bm
        (enc::EncodingMgr::INSTANCE());

    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    witness::WitnessMgr& wm
        (witness::WitnessMgr::INSTANCE());

    int k = ! allsat
        ? 1
        : limit;

    bool first
        (true);

    clock_t t0 = clock(), t1;
    double secs;

    sat::Engine engine { "pick_state" };

    expr::Expr_ptr ctx { em.make_empty() };

    model::CompilationUnits constraint_cus;
    unsigned nconstraints { 0 };
    std::for_each(begin(constraints),
                  end(constraints),
                  [this, ctx, &nconstraints, &constraint_cus](expr::Expr_ptr expr) {
                      INFO
                          << "Compiling constraint `"
                          << expr
                          << "` ..."
                          << std::endl;

                      model::CompilationUnit unit
                          (compiler().process(ctx, expr));

                      constraint_cus.push_back(unit);
                      ++ nconstraints;
                  });

    INFO
        << nconstraints
        << " constraints found."
        << std::endl;

    /* INITs and INVARs at time 0 */
    assert_fsm_init(engine, 0);
    assert_fsm_invar(engine, 0);

    /* Additional constraints */
    std::for_each(begin(constraint_cus),
                  end(constraint_cus),
                  [this, &engine](model::CompilationUnit& cu) {
                      this->assert_formula(engine, 0, cu);
                  });

    while ( k -- ) {

        if (allsat) {

            /* skip first cycle */
            if (first) {
                first = false;
            }
            else {
                /* In ALLSAT mode, for each bit int the encoding,
                   fetch UCBI, time it into TCBI at time 0, fetch its
                   value in MiniSAT model and negate it in the
                   exclusion clause. */
                vec<Lit> exclusion;

                symb::SymbIter symbols
                    (model());

                while (symbols.has_next()) {
                    std::pair <expr::Expr_ptr, symb::Symbol_ptr> pair
                        (symbols.next());

                    expr::Expr_ptr ctx
                        (pair.first);

                    symb::Symbol_ptr symb
                        (pair.second);

                    expr::Expr_ptr symb_name
                        (symb->name());

                    expr::Expr_ptr key
                        (em.make_dot( ctx, symb_name));

                    if (symb->is_variable()) {

                        symb::Variable& var
                            (symb->as_variable());

                        /* INPUT vars are not really vars ... */
                        if (var.is_input())
                            continue;

                        /* time it, and fetch encoding for enc mgr */
                        enc::Encoding_ptr enc
                            (bm.find_encoding( expr::TimedExpr(key, 0)));

                        if ( ! enc )
                            continue;

                        /* for each bit in this encoding, fetch UCBI,
                           time it into TCBI at time 0, fetch its
                           value in MiniSAT model and append its
                           negation to exclusion clause.. */
                        dd::DDVector::const_iterator di;
                        unsigned ndx;
                        for (ndx = 0, di = enc->bits().begin();
                             enc->bits().end() != di; ++ ndx, ++ di) {

                            unsigned bit
                                ((*di).getNode()->index);

                            const enc::UCBI& ucbi
                                (bm.find_ucbi(bit));

                            const enc::TCBI tcbi
                                (enc::TCBI(ucbi, 0));

                            Var var
                                (engine.tcbi_to_var(tcbi));

                            int value
                                (engine.value(var)); /* don't cares assigned to 0 */

                            exclusion.push( mkLit(var, value));
                        }
                    }
                }

                /* add exclusion clause to SAT instance */
                engine.add_clause(exclusion);
            }
        } /* if (allsat) */

        witness::Witness_ptr w;
        if (sat::status_t::STATUS_SAT == engine.solve()) {
            t1 = clock(); secs = (double) (t1 - t0) / (double) CLOCKS_PER_SEC;

            TRACE
                << "simulation initialized, took " << secs
                << " seconds" << std::endl;

            w = new SimulationWitness( model(), engine, 0);;

            {
                std::ostringstream oss;
                oss
                    << simulation_trace_prfx
                    << (++ progressive);

                w->set_id(oss.str());
            }

            {
                std::ostringstream oss;

                oss
                    << "Simulation trace for module `"
                    << model().main_module().name()
                    << "`" ;

                w->set_desc(oss.str());
            }

            /* REVIEW THESE */
            set_witness(*w);

            wm.record(*w);
            wm.set_current(*w);

            f_status = SIMULATION_INITIALIZED;
        }
        else {
            WARN
                << "Inconsistency detected trying to pick-state"
                << std::endl;
            f_status = SIMULATION_DEADLOCKED;
            break;
        }
    } /* while ( -- k ) */
}

void Simulation::simulate(expr::Expr_ptr invar_condition,
                          expr::Expr_ptr until_condition,
                          expr::ExprVector constraints,
                          step_t steps,
                          pconst_char trace_name)
{
    sat::status_t last_sat;

    clock_t t0 = clock(), t1;
    double secs;

    sat::Engine engine
        ("simulation");

    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    witness::WitnessMgr& wm
        (witness::WitnessMgr::INSTANCE());

    expr::Atom trace_uid
        (trace_name ? expr::Atom(trace_name) : wm.current().id());

    witness::Witness& trace
        (wm.witness(trace_uid));

    set_witness(trace);

    // here we need to push all the values for variables in the last
    // state of resuming witness. A complete assignment to *all* state
    // variables guarantees full deterministic behavior.
    step_t init_time
        (trace.last_time());

    step_t k
        (init_time);

    witness::TimeFrame& last
        (trace.last());

    assert_time_frame(engine, k, last);

    /* inject full transition relation, trace may not be compatible
       with current state's INVARs */
    assert_fsm_invar(engine, k );
    assert_fsm_trans(engine, k );
    assert_fsm_invar(engine, 1 + k);

    /* assert additional constraints */
    if (invar_condition) {

        model::Compiler& cmpl
            (compiler()); // just a local ref

        expr::Expr_ptr ctx
            (em.make_empty());

        try {
            model::CompilationUnit term
                (cmpl.process(ctx, invar_condition));

            assert_formula( engine, 1 + k, term, 0);
        }
        catch (Exception& ae) {
            pconst_char what
                (ae.what());

            WARN
                << what
                << std::endl
                << "  in additional constraint"
                << ctx << "::" << invar_condition
                << std::endl;

            free((void *) what);
            return;
        }
    }

    DEBUG
        << "Resuming simulation..."
        << std::endl;

    while (sat::status_t::STATUS_SAT == (last_sat = engine.solve())) {

        ++ k;

        t1 = clock(); secs = (double) (t1 - t0) / (double) CLOCKS_PER_SEC;

        TRACE
            << "simulation completed step " << k
            << ", took " << secs << " seconds"
            << std::endl;

        t0 = t1; // resetting clock

        witness::Witness& w
            (*new SimulationWitness( model(), engine, k));
        witness().extend(w);

        /* no more steps? */
        if (! -- steps) {
            f_status = SIMULATION_INTERRUPTED;
            break;
        }

        /* until condition reached? */
        if (NULL != until_condition && wm.eval (witness(),
                                                em.make_empty(),
                                                until_condition, k)) {
            f_status = SIMULATION_HALTED;
            break;
        }

        // TODO: SAT restart after a given number of steps (e.g. 10) would help
        // preventing performance degradation as k grows larger.
        assert_fsm_trans(engine, k);
        assert_fsm_invar(engine, k);
    }

    if (last_sat == sat::status_t::STATUS_UNKNOWN)
        f_status = SIMULATION_INTERRUPTED;

    else if (last_sat == sat::status_t::STATUS_UNSAT) {
        WARN
            << "Inconsistency detected in transition relation at step " << k
            << std::endl;

        f_status = SIMULATION_DEADLOCKED;
    }
}

} // namespace sim
