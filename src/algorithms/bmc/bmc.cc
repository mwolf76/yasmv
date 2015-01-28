/**
 *  @file bmc.cc
 *  @brief SAT-based BMC Algorithms for property checking
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
#include <boost/thread.hpp>
#include <boost/thread/mutex.hpp>

#include <algorithms/bmc/bmc.hh>
#include <witness/witness_mgr.hh>

// reserved for witnesses
static unsigned progressive = 0;
static const char *cex_trace_prfx = "cex_";

BMC::BMC(Command& command, Model& model)
    : Algorithm(command, model)
{
    setup();
    DRIVEL
        << "Created BMC @"
        << this
        << std::endl;
}

BMC::~BMC()
{
    DRIVEL
        << "Destroyed BMC @"
        << this
        << std::endl;
}

void BMC::falsification( Expr_ptr phi )
{
    Engine engine;
    Expr_ptr ctx = em().make_empty();

    Expr_ptr invariant
        (phi);

    CompilationUnit ii (compiler().process( ctx, invariant));

    Expr_ptr violation = em().make_not(invariant);
    CompilationUnit vv (compiler().process( ctx, violation));

    step_t k = 0; // to infinity...
    bool leave = false; // TODO: somebody telling us to stop

    assert_fsm_init(engine, 0);
    assert_fsm_invar(engine, 0);

    do {
        /* assert violation in a separate group */
        assert_formula(engine, k, vv, engine.new_group());

        TRACE
            << "Falsification: looking for CEX (k = " << k << ")..."
            << std::endl;

        if (STATUS_SAT == engine.solve()) {
            test_and_set_status( MC_FALSE );

            WitnessMgr& wm = WitnessMgr::INSTANCE();
            TRACE
                << "CEX witness exists (k = " << k << "), invariant `" << invariant
                << "` is FALSE."
                << std::endl;

            Witness& w(* new BMCCounterExample(phi, model(), engine, k, false));
            {
                std::ostringstream oss;
                oss
                    << cex_trace_prfx
                    << (++ progressive);
                w.set_id(oss.str());
            }
            {
                std::ostringstream oss;
                oss
                    << "CEX witness for invariant`"
                    << phi
                    << "`"
                ;
                w.set_desc(oss.str());
            }

            wm.register_witness(w);
            set_witness(w);

            break;
        }

        /* disable violation and add invariant */
        engine.groups().last() *= -1;
        assert_formula(engine, k, ii, engine.new_group());

        /* unrolling */
        assert_fsm_trans(engine, k ++);
        assert_fsm_invar(engine, k);

    } while (f_status == MC_UNKNOWN && !leave);
}

void BMC::kinduction( Expr_ptr phi )
{
    /* thread locals */
    Engine engine;
    Expr_ptr ctx = em().make_empty();

    Expr_ptr invariant
        (phi);

    CompilationUnit ii (compiler().process( ctx, invariant));

    Expr_ptr violation = em().make_not(invariant);
    CompilationUnit vv (compiler().process( ctx, violation));

    step_t j, k = 0; // to infinity...
    bool leave = false; // TODO: somebody telling us to stop

    do {
        /* assert violation in a separate group */
        assert_formula(engine, k, vv, engine.new_group());

        TRACE
            << "K-induction: looking for proof (k = " << k << ")..."
            << std::endl;

        if (STATUS_UNSAT == engine.solve()) {
            TRACE
                << "Found k-induction proof (k = " << k << "), invariant `" << invariant
                << "` is TRUE."
                << std::endl;
            test_and_set_status( MC_TRUE );
            return;
        }

        /* disable violation and add invariant */
        engine.groups().last() *= -1;

        assert_formula(engine, k, ii, engine.new_group());

        /* unrolling */
        assert_fsm_trans(engine, k ++);
        assert_fsm_invar(engine, k);

        /* build state uniqueness constraint for each pair of states
           (j, k), where j < k */
        for (j = 0; j < k; ++ j)
            assert_fsm_uniqueness(engine, j, k);

    } while (f_status == MC_UNKNOWN && !leave);

    TRACE
        << "K-induction: giving up."
        << std::endl;
}

// comment out when debugging
#define ENABLE_FALSIFICATION
#define ENABLE_KINDUCTION

void BMC::process(const Expr_ptr phi)
{
    f_status = MC_UNKNOWN;

    /* launch parallel threads */
    #ifdef ENABLE_FALSIFICATION
    boost::thread base(&BMC::falsification, this, phi);
    #endif

    #ifdef ENABLE_KINDUCTION
    boost::thread step(&BMC::kinduction, this, phi);
    #endif

    #ifdef ENABLE_FALSIFICATION
    base.join();
    #endif

    #ifdef ENABLE_KINDUCTION
    step.join();
    #endif

    TRACE
        << "Done."
        << std::endl;
}

// synchronized
mc_status_t BMC::status()
{
    boost::mutex::scoped_lock lock
        (f_status_mutex);

    return f_status;
}

// synchronized
mc_status_t BMC::test_and_set_status(mc_status_t status)
{
    assert(status != MC_UNKNOWN);
    boost::mutex::scoped_lock lock
        (f_status_mutex);

    if (f_status == MC_UNKNOWN)
        f_status = status;

    return f_status;
}
