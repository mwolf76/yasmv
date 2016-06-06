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
    , f_k(0)
{
    const void* instance
        (this);

    setup();
    assert(ok());

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
    Engine engine
        ("Forward");

    step_t k = 0;

    /* initial constraints */
    assert_fsm_init(engine, 0);
    assert_fsm_invar(engine, 0);

    do {

        { /* looking for CEX : BMC(k-1) ^ ! P(k) */
            assert_formula(engine, k, vv,
                           engine.new_group());

            INFO
                << "Forward: now looking for CEX (k = " << k << ")..."
                << std::endl
                ;

            status_t status
                (engine.solve());

            if (STATUS_UNKNOWN == status) {
                goto cleanup;
            }
            if (STATUS_UNSAT == status) {
                INFO
                    << "Forward: no CEX found (k = " << k << ")..."
                    << std::endl
                    ;
            }
            else if (STATUS_SAT == status) {
                sync_set_status( MC_FALSE );

                WitnessMgr& wm = WitnessMgr::INSTANCE();
                INFO
                    << "Forward: CEX witness exists (k = " << k << "), invariant `"
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
                        << "BMC CEX witness for invariant `"
                        << phi
                        << "`" ;

                    w.set_desc(oss.str());
                }

                wm.record(w);
                wm.set_current(w);
                set_witness(w);

                goto cleanup;
            }
        }

        if (sync_status() == MC_UNKNOWN) {

            /* disable violation */
            engine.disable_last_group();

            /* assert invariant in main group */
            assert_formula(engine, k, ii);

            /* unrolling */
            assert_fsm_trans(engine, k ++);
            assert_fsm_invar(engine, k);

#if 0
            /* TODO: enabling the next line turns full forward
               strategy into pure BMC falsification */ continue;
#endif

            {
                /* looking for exploration proof: does a new unseen state
                   exist?  assert uniqueness and test for unsatisfiability */
                INFO
                    << "Forward: looking for proof (k = " << k << ")..."
                    << std::endl
                    ;

                /* build state uniqueness constraint for each pair of states
                   (j, k), where j < k */
                for (step_t j = 0; j < k; ++ j)
                    assert_fsm_uniqueness(engine, j, k);

                status_t status
                    (engine.solve());

                if (STATUS_UNKNOWN == status) {
                    goto cleanup;
                }
                if (STATUS_UNSAT == status) {
                    INFO
                        << "Forward: found proof (k = " << k << "), invariant `"
                        << phi
                        << "` is TRUE."
                        << std::endl;

                    sync_set_status( MC_TRUE );
                    goto cleanup;
                }

                else if (STATUS_SAT == status) {
                    INFO
                        << "Forward: no proof found (k = " << k << ")"
                        << std::endl;

                    /* signal backward that a k-path is
                       possible. Backwards check on a k-long path now
                       makes sense.*/
                    sync_set_k(k);
                }
            }
        }
    } while (sync_status() == MC_UNKNOWN);

 cleanup:
    /* signal other threads it's time to go home */
    EngineMgr::INSTANCE()
        .interrupt();

    INFO
        << engine
        << std::endl;
} /* forward() */

void BMC::backward( Expr_ptr phi,
                    CompilationUnit& ii,
                    CompilationUnit& vv)
{
    /* thread locals */
    Engine engine
        ("Backward");

    step_t k = 0;

    do {

        /* wait for forward strategy to check a k-long path feasibility */
        while (sync_k() <= k) {
            sleep(1);

            /* quit immediately if forward solved the instance or a
               user interrupt has been signalled */
            if (sync_status() != MC_UNKNOWN)
                goto cleanup;
        }

        /* assert violation in a separate group */
        assert_formula(engine, k, vv, engine.new_group());

        INFO
            << "Backward: looking for proof (k = " << k << ")..."
            << std::endl
            ;

        status_t status
            (engine.solve());

        if (STATUS_UNKNOWN == status) {
            goto cleanup;
        }
        else if (STATUS_UNSAT == status) {
            INFO
                << "Backward: found proof (k = " << k << "), invariant `"
                << phi
                << "` is TRUE."
                << std::endl;

            sync_set_status( MC_TRUE );
            goto cleanup;
        }
        else if (STATUS_SAT == status) {
            INFO
                << "Backward: found no proof (k = " << k << ")"
                << std::endl;
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

    } while (sync_status() == MC_UNKNOWN);

 cleanup:
    /* signal other threads it's time to go home */
    EngineMgr::INSTANCE()
        .interrupt();

    INFO
        << engine
        << std::endl;
} /* backward() */


void BMC::process(const Expr_ptr phi)
{
    /* check everyting is ok before spawning */
    Expr_ptr ctx
        (em().make_empty());

    try {
        INFO
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

    INFO
        << "Done."
        << std::endl;
}

mc_status_t BMC::status()
{ return sync_status(); }

/* synchronized */
mc_status_t BMC::sync_status()
{
    boost::mutex::scoped_lock lock
        (f_status_mutex);

    return f_status;
}

/* synchronized */
void BMC::sync_set_status(mc_status_t status)
{
    boost::mutex::scoped_lock lock
        (f_status_mutex);

    /* consistency check */
    assert(f_status == status ||
           (status != MC_UNKNOWN && f_status == MC_UNKNOWN));

    f_status = status;
}

/* synchronized */
step_t BMC::sync_k()
{
    boost::mutex::scoped_lock lock
        (f_status_mutex);

    return f_k;
}

void BMC::sync_set_k(step_t k)
{
    boost::mutex::scoped_lock lock
        (f_status_mutex);

    /* consistency check */
    assert(k >= f_k);

    f_k = k;
}
