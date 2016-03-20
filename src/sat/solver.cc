/**
 *  @file solver.cc
 *  @brief SAT interface implementation
 *
 *  This module contains the interface for services that implement an
 *  CNF clauses generation in a form that is suitable for direct
 *  injection into the SAT solver.
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
#include <sat.hh>
#include <cstdlib>

#include <sat/helpers.hh>

EngineMgr_ptr EngineMgr::f_instance = NULL;

EngineMgr::EngineMgr()
{
    const void* instance
        (this);

    DRIVEL
        << "Initialized EngineMgr @ " << instance
        << std::endl;
}

EngineMgr::~EngineMgr()
{
    const void* instance
        (this);

    DRIVEL
        << "Deinitialized EngineMgr @ " << instance
        << std::endl;
}

void EngineMgr::register_instance(Engine_ptr engine)
{
    boost::mutex::scoped_lock lock
        (f_mutex);

    /* this engine is not yet registered */
    assert (f_engines.find(engine) == f_engines.end());

    DEBUG
        << "Registered engine instance"
        << "@"
        << engine
        << std::endl;

    f_engines.insert(engine);
}

void EngineMgr::unregister_instance(Engine_ptr engine)
{
    boost::mutex::scoped_lock lock
        (f_mutex);

    /* this engine is registered */
    assert (f_engines.find(engine) != f_engines.end());

    DEBUG
        << "Unregistered engine instance"
        << "@"
        << engine
        << std::endl;

    f_engines.erase(engine);
}

void EngineMgr::interrupt()
{
    boost::mutex::scoped_lock lock
        (f_mutex);

    EngineSet::iterator esi;
    for (esi = f_engines.begin(); f_engines.end() != esi; ++ esi) {
        Engine_ptr pe
            (*esi);

        pe -> interrupt();
    }
}

void EngineMgr::dump_stats(std::ostream& os)
{
    boost::mutex::scoped_lock lock
        (f_mutex);

    if (f_engines.empty()) {
        os
            << "Solver is not running. No stats available."
            << std::endl;
    }

    else {
        EngineSet::iterator esi;
        for (esi = f_engines.begin(); f_engines.end() != esi; ++ esi) {
            Engine_ptr pe
                (*esi);

            os
                << (*pe)
                << std::endl ;
        }

        os
            << std::endl ;
    }
}

std::ostream& operator<<(std::ostream& os, const Engine& engine)
{
    const Solver& solver
        (engine.f_solver);

    os
        << "Solver: `"
        << engine.f_instance_name

        << "`, solves: "
        << solver.solves

        << ", starts: "
        << solver.starts

        << ", decs: "
        << solver.decisions

        << ", rnd decs: "
        << solver.rnd_decisions

        << ", props: "
        << solver.propagations

        << ", conflicts: "
        << solver.conflicts

        << ", dec vars: "
        << solver.dec_vars

        << ", clause lits: "
        << solver.clauses_literals

        << ", learnt lits: "
        << solver.learnts_literals

        << ", max lits: "
        << solver.max_literals

        << ", tot lits: "
        << solver.tot_literals

        ;

    return os;
}


/**
 * @brief SAT instancte ctor
 */
Engine::Engine(const char* instance_name)
    : f_instance_name(instance_name)
    , f_enc_mgr(EncodingMgr::INSTANCE())
    , f_mapper(* new TimeMapper(*this))
    , f_registry(* new CNFRegistry(*this))
    , f_solver()
{
    const void* instance
        (this);

    /* Default configuration */
    f_solver.random_var_freq = .1;
    // f_solver.ccmin_mode = 0;
    // f_solver.phase_saving = 0;
    f_solver.rnd_init_act = true;
    f_solver.garbage_frac = 0.50;

    /* MAINGROUP (=0) is already there. */
    f_groups.push(new_sat_var());

    EngineMgr::INSTANCE()
        .register_instance(this);

    DEBUG
        << "Initialized Engine instance @"
        << instance
        << std::endl;
}

Engine::~Engine()
{
    EngineMgr::INSTANCE()
        .unregister_instance(this);
}

status_t Engine::sat_solve_groups(const Groups& groups)
{
    vec<Lit> assumptions;

    clock_t t0 = clock();
    for (int i = 0; i < groups.size(); ++ i) {
        Var grp = groups[i];

        /* Assumptions work like "a -> phi", thus a non-negative
           value enables group, whereas a negative value disables it. */
        assumptions.push( mkLit( abs(grp), grp < 0));
    }

    DEBUG
        << "Solving ..."
        << std::endl;

    Minisat::lbool status
        (f_solver.solveLimited(assumptions));

    if (status == l_True)
        f_status = STATUS_SAT;
    else if (status == l_False)
        f_status = STATUS_UNSAT;
    else if (status == l_Undef)
        f_status = STATUS_UNKNOWN;
    else assert(false); /* unreachable */

    clock_t elapsed = clock() - t0;
    double secs = (double) elapsed / (double) CLOCKS_PER_SEC;

    DEBUG
        << "Took "
        << secs
        << " seconds. Status is "
        << f_status << "."
        << std::endl;

    return f_status;
}

void Engine::push(CompilationUnit cu, step_t time, group_t group)
{
    /* push DDs */
    {
        const DDVector& dv
            (cu.dds());
        DDVector::const_iterator i;
        for (i = dv.begin(); dv.end() != i; ++ i)
            cnf_push_single_cut( *i, time, group );
    }

    /* push CNF for inlined operators */
    {
        const InlinedOperatorDescriptors& inlined_operator_descriptors
            (cu.inlined_operator_descriptors());
        InlinedOperatorDescriptors::const_iterator i;
        for (i = inlined_operator_descriptors.begin(); inlined_operator_descriptors.end() != i; ++ i) {
            CNFOperatorInliner worker
                (*this, time, group);

            worker(*i);
        }
    }

    /* push ITE muxes */
    {
        const Expr2BinarySelectionDescriptorsMap& binary_selection_descriptors_map
            (cu.binary_selection_descriptors_map());
        Expr2BinarySelectionDescriptorsMap::const_iterator mmi
            (binary_selection_descriptors_map.begin());

        while (binary_selection_descriptors_map.end() != mmi) {
            Expr_ptr toplevel
                (mmi -> first);
            BinarySelectionDescriptors descriptors
                (mmi -> second);

            BinarySelectionDescriptors::const_iterator i;
            for (i = descriptors.begin(); descriptors.end() != i; ++ i) {
                CNFBinarySelectionInliner worker
                    (*this, time, group);

                worker(*i);
            }

            ++ mmi ;
        }
    }

    /* push Array muxes */
    {
        const MultiwaySelectionDescriptors& muxes
            (cu.array_mux_descriptors());
        MultiwaySelectionDescriptors::const_iterator i;
        for (i = muxes.begin(); muxes.end() != i; ++ i) {

            CNFMultiwaySelectionInliner worker
                (*this, time, group);

            worker(*i);
        }

    }
}
