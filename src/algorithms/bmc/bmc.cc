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
    const void* instance(this);
    setup();
    DRIVEL
        << "Created BMC @"
        << instance
        << std::endl;
}

BMC::~BMC()
{
    const void* instance(this);
    DRIVEL
        << "Destroyed BMC @"
        << instance
        << std::endl;
}

void BMC::forward( Expr_ptr phi,
                   CompilationUnit& ii,
                   CompilationUnit& vv)
{
    Engine engine;
    step_t k = 0;

    /* initial constraints */
    assert_fsm_init(engine, 0);
    assert_fsm_invar(engine, 0);

    do {
        /* assert violation in a new group */
        assert_formula(engine, k, vv,
                       engine.new_group());

        TRACE
            << "forward: looking for CEX (k = " << k << ")..."
            << std::endl;

        if (STATUS_SAT == engine.solve()) {
            test_and_set_status( MC_FALSE );

            WitnessMgr& wm = WitnessMgr::INSTANCE();
            TRACE
                << "CEX witness exists (k = " << k << "), invariant `"
                << phi
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
                    << "CEX witness for invariant `"
                    << phi
                    << "`"
                ;
                w.set_desc(oss.str());
            }

            wm.record(w);
            wm.set_current(w);
            set_witness(w);
            return;
        }

        /* disable violation */
        engine.disable_last_group();

        /* assert invariant in main group */
        assert_formula(engine, k, ii);

        /* unrolling */
        assert_fsm_trans(engine, k ++);
        assert_fsm_invar(engine, k);

        /* does a new unseen state exist? assert uniqueness main
           group and test for satisfiability */
        TRACE
            << "forward: looking for proof (k = " << k << ")..."
            << std::endl;

        /* build state uniqueness constraint for each pair of states
           (j, k), where j < k */
        for (step_t j = 0; j < k; ++ j)
            assert_fsm_uniqueness(engine, j, k);

        if (STATUS_UNSAT == engine.solve()) {
            TRACE
                << "Found forward proof (k = " << k << "), invariant `"
                << phi
                << "` is TRUE."
                << std::endl;
            test_and_set_status( MC_TRUE );
            return;
        }

        /* handle user interruption */
        if (sigint_caught)
            break;
    } while (f_status == MC_UNKNOWN);
} /* forward() */

void BMC::backward( Expr_ptr phi,
                    CompilationUnit& ii,
                    CompilationUnit& vv)
{
    /* thread locals */
    Engine engine;
    step_t k = 0;

    do {
        /* assert violation in a separate group */
        assert_formula(engine, k, vv, engine.new_group());

        TRACE
            << "backward: looking for proof (k = " << k << ")..."
            << std::endl;

        if (STATUS_UNSAT == engine.solve()) {
            TRACE
                << "Found backward proof (k = " << k << "), invariant `"
                << phi
                << "` is TRUE."
                << std::endl;
            test_and_set_status( MC_TRUE );
            return;
        }

        /* disable violation */
        engine.disable_last_group();

        /* add invariant ... */
        assert_formula(engine, k, ii);

        /* ... and unrolling in main group */
        assert_fsm_invar(engine, k);
        assert_fsm_trans(engine, k ++);

        /* build state uniqueness constraint for each pair of states
           (j, k), where j < k */
        for (step_t j = 0; j < k; ++ j)
            assert_fsm_uniqueness(engine, j, k);

        if (sigint_caught)
            break;

    } while (f_status == MC_UNKNOWN);

} /* backward() */

void BMC::process(const Expr_ptr phi)
{
    /* check everyting is ok before spawning */
    Expr_ptr ctx
        (em().make_empty());

    try {
        TRACE
            << "Compiling formula..."
            << std::endl;

        CompilationUnit ii
            (compiler().process( ctx, phi));

        CompilationUnit vv
            (compiler().process( ctx, em().make_not(phi)));

        f_status = MC_UNKNOWN;

        /* launch parallel checking strategies */
        boost::thread fwd(&BMC::forward, this, phi, ii, vv);
        boost::thread bwd(&BMC::backward, this, phi, ii, vv);

        fwd.join();
        bwd.join();
    }
    catch (Exception& e) {
        const char* tmp
            (strdup(e.what()));

        std::cerr
            << tmp
            << std::endl;

        f_status = MC_ERROR;
        return;
    }

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
