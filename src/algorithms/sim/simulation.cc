/**
 *  @file MC Algorithm.hh
 *  @brief SAT Simulation Algorithm
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
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
#include <sim/simulation.hh>

Simulation::Simulation(IModel& model,
                       Expr_ptr halt_cond,
                       ExprVector& constraints,
                       Expr_ptr witness_id)
    : Algorithm()
    , f_model(model)
    , f_witness(NULL)
    , f_halt_cond(halt_cond)
    , f_constraints(constraints)
{
    /* Resuming a simulation requires given witness to be SAT */
    if (witness_id) {
        Witness& w = WitnessMgr::INSTANCE().witness( witness_id );
        set_witness(w);
    }

    /* ensure internal structures are empty */
    assert( 0 == f_init_adds.size());
    assert( 0 == f_invar_adds.size());
    assert( 0 == f_trans_adds.size());

    const Modules& modules = f_model.modules();
    for (Modules::const_iterator m = modules.begin();
         m != modules.end(); ++ m) {

        Module& module = dynamic_cast <Module&> (*m->second);

        /* INIT */
        const ExprVector init = module.init();
        for (ExprVector::const_iterator init_eye = init.begin();
             init_eye != init.end(); ++ init_eye) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*init_eye);

            f_init_adds.push_back(compiler().process(ctx, body));
        }

        /* INVAR */
        const ExprVector invar = module.invar();
        for (ExprVector::const_iterator invar_eye = invar.begin();
             invar_eye != invar.end(); ++ invar_eye) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*invar_eye);

            f_invar_adds.push_back(compiler().process(ctx, body));
        }

        /* TRANS */
        const ExprVector trans = module.trans();
        for (ExprVector::const_iterator trans_eye = trans.begin();
             trans_eye != trans.end(); ++ trans_eye) {

            Expr_ptr ctx = module.expr();
            Expr_ptr body = (*trans_eye);

            f_trans_adds.push_back(compiler().process(ctx, body));
        }
    }
}

Simulation::~Simulation()
{}

void Simulation::set_status(simulation_status_t status)
{ f_status = status; }

void Simulation::set_witness(Witness& witness)
{
    if (f_witness) {
        delete f_witness;
    }

    f_witness = & witness;
}

void Simulation::process()
{
    ExprMgr& em = ExprMgr::INSTANCE();
    WitnessMgr& wm = WitnessMgr::INSTANCE();

    bool halt = false;

    step_t j = 0;
    step_t k = f_witness ? f_witness -> length() : 0;

    set_status( SIMULATION_SAT ); // optimic assumption

    // if a witness is already there, we're resuming a previous
    // simulation. Hence, no need for initial states.
    if (!k) {
        assert_fsm_init(0);
        assert_fsm_invar(0);
        TRACE << "Starting simulation..." << endl;
    }
    else {
        // here we need to push all the values for variables in the
        // last state of resuming witness. A complete assignment to
        // all state variables ensures full deterministic behavior.
        assert( false) ; // TODO
        TRACE << "Resuming simulation..." << endl;
    }

    if (STATUS_SAT == engine().solve()) {
        Witness_ptr w = new SimulationWitness( model(), engine(), j, k);

        if (! has_witness()) set_witness(*w);
        else witness().extend(*w);

        halt = wm.eval ( witness(), em.make_main(), f_halt_cond, k);
        if (!halt) {
            do {
                assert_fsm_trans(k ++);
                assert_fsm_invar(k);
                TRACE << "Simulating step " << k << endl;

                if (STATUS_SAT == engine().solve()) {
                    Witness_ptr w = new SimulationWitness( model(), engine(), k, k);

                    witness().extend(*w);
                    halt = wm.eval ( witness(), em.make_main(), f_halt_cond, k);
                }
            } while (STATUS_SAT == engine().status() && ! halt);
        }
        else {
            TRACE << "Inconsistency detected in transition relation at step " << k
                  << ". Simulation aborted."
                  << endl;

            set_status( SIMULATION_UNSAT );
        }
    }
    else {
        TRACE << "Inconsistency detected in initial states. Simulation aborted."
              << endl;

        set_status( SIMULATION_UNSAT );
    }

    if (halt) {
        TRACE << "Simulation reached HALT condition"
              << endl;
    }

    TRACE << "Done." << endl;
}

void Simulation::assert_fsm_init(step_t time, group_t group, color_t color)
{
    clock_t t0 = clock();
    unsigned n = f_init_adds.size();
    TRACE << "CNFizing INITs @" << time
          << "... (" << n << " formulas)"
          << endl;

    ADDVector::iterator i;
    for (i = f_init_adds.begin(); f_init_adds.end() != i; ++ i) {
        engine().push( *i, time, group, color);
    }

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    TRACE << "Done. (took " << secs << " seconds)" << endl;
}

void Simulation::assert_fsm_invar(step_t time, group_t group, color_t color)
{
    clock_t t0 = clock();
    unsigned n = f_invar_adds.size();
    TRACE << "CNFizing INVARs @" << time
          << "... (" << n << " formulas)"
          << endl;

    ADDVector::iterator i;
    for (i = f_invar_adds.begin(); f_invar_adds.end() != i; ++ i) {
        engine().push( *i, time, group, color);
    }

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    TRACE << "Done. (took " << secs << " seconds)" << endl;
}

void Simulation::assert_fsm_trans(step_t time, group_t group, color_t color)
{
    clock_t t0 = clock();
    unsigned n = f_trans_adds.size();

    TRACE << "CNFizing TRANSes @" << time
          << "... (" << n << " formulas)"
          << endl;

    ADDVector::iterator i;
    for (i = f_trans_adds.begin(); f_trans_adds.end() != i; ++ i) {
        engine().push( *i, time, group, color);
    }

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;
    TRACE << "Done. (took " << secs << " seconds)" << endl;
}
