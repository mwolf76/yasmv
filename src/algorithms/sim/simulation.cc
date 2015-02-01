/**
 *  @file simulation.cc
 *  @brief SAT-based BMC simulation algorithm
 *
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2.1 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/
#include <sstream>
#include <sim/simulation.hh>
#include <model/compiler/unit.hh>

// reserved for witnesses
static unsigned progressive = 0;
static const char *simulation_trace_prfx = "sim_";

Simulation::Simulation(Command& command, Model& model)
    : Algorithm(command, model)
{
    setup();
}

Simulation::~Simulation()
{}

void Simulation::pick_state(Expr_ptr init_condition, pconst_char trace_name)
{
    clock_t t0 = clock(), t1;
    double secs;

    Engine engine;

    WitnessMgr& wm
        (WitnessMgr::INSTANCE());

    assert_fsm_init(engine, 0);
    assert_fsm_invar(engine, 0);

    if (init_condition) {

        Compiler& cmpl
            (compiler()); // just a local ref

        Expr_ptr ctx
            (em().make_empty());


        try {
            CompilationUnit term
                (cmpl.process(ctx, init_condition));

            assert_formula( engine, 0, term, 0);
        }
        catch (Exception& ae) {
            std::string tmp
                (ae.what());
            WARN
                << tmp
                << std::endl
                << "  in initial condition"
                << ctx << "::" << init_condition
                << std::endl;
            return;
        }
    }

    if (STATUS_SAT == engine.solve()) {
        t1 = clock(); secs = (double) (t1 - t0) / (double) CLOCKS_PER_SEC;

        TRACE
            << "simulation initialized, took " << secs
            << " seconds" << std::endl;

        Witness& w
            (*new SimulationWitness( model(), engine, 0));

        if (trace_name)
            w.set_id(Atom(trace_name));
        else {
            std::ostringstream oss;
            oss
                << simulation_trace_prfx
                << (++ progressive);
            w.set_id(oss.str());
        }
        {
            std::ostringstream oss;
            oss
                << "Simulation trace";
            w.set_desc(oss.str());
        }

        set_witness(w);

        wm.record(w);
        wm.set_current(w);

        f_status = SIMULATION_INITIALIZED;
    }
    else {
        WARN << "Inconsistency detected in initial states"
             << std::endl;
        f_status = SIMULATION_DEADLOCKED;
    }
}

void Simulation::simulate(Expr_ptr invar_condition,
                          Expr_ptr until_condition,
                          step_t steps,
                          pconst_char trace_name)
{
    status_t last_sat;

    clock_t t0 = clock(), t1;
    double secs;

    Engine engine;

    ExprMgr& em
        (ExprMgr::INSTANCE());

    WitnessMgr& wm
        (WitnessMgr::INSTANCE());

    Atom trace_uid
        (trace_name ? Atom(trace_name) : wm.current().id());

    Witness& trace
        (wm.witness(trace_uid));

    set_witness(trace);

    // here we need to push all the values for variables in the last
    // state of resuming witness. A complete assignment to *all* state
    // variables guarantees full deterministic behavior.
    step_t init_time
        (trace.last_time());
    step_t k
        (init_time);
    TimeFrame& last
        (trace.last());

    assert_time_frame( engine, k, last);

    /* inject full transition relation, trace may not be compatible
       with current state's INVARs */
    assert_fsm_invar(engine, k );
    assert_fsm_trans(engine, 1 + k);
    assert_fsm_invar(engine, 1 + k);

    DEBUG
        << "Resuming simulation..."
        << std::endl;

    while (STATUS_SAT == (last_sat = engine.solve())) {

        t1 = clock(); secs = (double) (t1 - t0) / (double) CLOCKS_PER_SEC;

        if (init_time == k) {
            TRACE
                << "simulation initialized, took " << secs
                << " seconds" << std::endl;
        } else {
            TRACE
                << "simulation completed step " << k
                << ", took " << secs << " seconds"
                << std::endl;
        }
        t0 = t1; // resetting clock

        Witness& w
            (*new SimulationWitness( model(), engine, k));
        witness().extend(w);

        /* interrupted by the user? */
        if (sigint_caught) {
            f_status = SIMULATION_INTERRUPTED;
            break;
        }

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
        assert_fsm_trans(engine, k ++ );
        assert_fsm_invar(engine, k);
    }

    if (last_sat == STATUS_UNSAT) {
        WARN
            << "Inconsistency detected in transition relation at step " << k
            << std::endl;
        f_status = SIMULATION_DEADLOCKED;
    }
}


