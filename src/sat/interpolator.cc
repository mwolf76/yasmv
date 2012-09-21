/**
 *  @file interpolator.cc
 *  @brief Craig interpolation implementation (following McMillan's definition)
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

namespace Minisat {

    Term SAT::itp_build_interpolant(const Colors& a)
    {
        // local accessors
        ProofManager& pm = f_solver.proof_manager();
        const ClauseAllocator& ca = f_solver.clause_allocator();
        InferenceRule& unsat_proof = pm.proof();

        // internal cache for memoizing
        R2T_Map r2t;

        // [MP] setup internal structures
        itp_init_interpolation(a);

        typedef vec<InferenceRule *> RulesStack;
        RulesStack to_process; to_process.push(&unsat_proof);

        while (0 != to_process.size()) {
            InferenceRule *r = to_process.last();

            if (r2t.has(r)) { to_process.pop(); continue; }

            ClauseHypRule *hyp = NULL;
            ResRule *rr = NULL;

            // if c is root (hypothesis)
            if (NULL != (hyp = dynamic_cast<ClauseHypRule *>(r))) {
                CRef cr = hyp->cref();

                to_process.pop();

                // if c in A -> p(c) := global(c)
                if (clause_is_of_A(cr)) {
                    assert(!r2t.has(hyp));

                    // [MP] inlined make_global
                    const Clause& c = ca[cr];
                    Term trm = f_factory.make_false();

                    for (int i = 0, sz = c.size(); i < sz; ++i) {
                        Lit p = c[i];

                        if (lit_is_of_B(p)) {
                            Var v = var(p);
                            assert(var_is_of_A(v) && var_is_of_B(v));

                            Term t = f_factory.make_var(v);
                            if (NULL == t) continue; /* cnf var */

                            if (sign(p)) { t = f_factory.make_not(t); }

                            trm = f_factory.make_or(trm, t);
                        }
                    }

                    if (NULL == trm) trm = f_factory.make_false(); // empty clause
                    // -- (end of inlined)

                    r2t.insert(hyp, trm);
                } /* clause is of A */

                else { // p(c) := TRUE
                    assert(!r2t.has(hyp));
                    r2t.insert(hyp, f_factory.make_true());
                }
            }

            else if (NULL != (rr = dynamic_cast<ResRule *>(r))) {
                InferenceRule* start = &rr->get_start();

                Term s = r2t.has(start) ? r2t[start] : f_factory.make_false();
                if (f_factory.is_false(s)) to_process.push(start);

                bool children_done = (!f_factory.is_false(s));
                for (int i = 0; i < rr->chain_size(); ++ i) {
                    InferenceRule* ir = rr->chain_get_ith_rule(i);

                    if (!r2t.has(ir)) {
                        to_process.push(ir);
                        children_done = false;
                    }
                }

                if (children_done) {
                    to_process.pop();

                    for (int i = 0; i < rr->chain_size(); ++i) {

                        Var pivot = rr->chain_get_ith_var(i);
                        InferenceRule* ir = rr->chain_get_ith_rule(i);

                        Term p = r2t.has(ir) ? r2t[ir] : f_factory.make_false();
                        Term cur = f_factory.make_false();
                        if (var_is_A_local(pivot)) {
                            cur = f_factory.make_or(s, p);
                        }
                        else {
                            cur = f_factory.make_and(s, p);
                        }

                        s = cur;
                    }

                    assert( !r2t.has(rr) ); r2t.insert(rr, s);
                }
            } else assert(false);
        } /* while */

        assert (r2t.has(&unsat_proof));
        return r2t[&unsat_proof];
    } // SAT::interpolant()

    void SAT::itp_init_interpolation(const Colors& ga)
    {
        // local accessors
        ProofManager& pm = f_solver.proof_manager();
        const ClauseAllocator& ca = f_solver.clause_allocator();

        // logger << loglevel(2)
        TRACE << "Initializing interpolation" << endl;

        a_variables.clear();
        b_variables.clear();

        // // The set of input groups for A
        // Set<int> ga;
        // for (unsigned i = 0; i < n; ++ i) { int group = *(groups_of_a+i); ga.insert(group); }

        /* [MP]: WTF?!? this is plain wrong design. There is no need to
        // interfer with the solver to fetch this kind of
        // information. This belongs to CNFizer, not the solver. */

        // load clauses from Solver, for each clause
        // decide whether its A or B according to the color in the
        // hypothesis for that (original) clause
        for (int i = 0, nclauses = f_solver.nClauses(); i < nclauses; i ++ ) {
            CRef cr = f_solver.clauses[i];
            ClauseHypRule& hyp = dynamic_cast<ClauseHypRule&> (pm.proof(cr));
            const Clause& c = ca[cr];

            if (ga.has(hyp.color())) {
                DEBUG << "clause " << c << " to A" << endl;
                assert (! a_clauses.has(cr));
                a_clauses.insert(cr);

                // register each var in the clause as belonging to A
                for (int j = 0, cl_size = c.size(); j < cl_size; j ++ ) {
                    Var v = var(c[j]);
                    if (! a_variables.has(v)) {
                        DEBUG << "itp: adding var " << v << " to A" << endl;
                        a_variables.insert(v);
                    }
                }
            }

            else {
                DEBUG << "clause " << c << " to B" << endl;

                // register each var in the clause as belonging to B
                for (int j = 0, cl_size = c.size(); j < cl_size; j ++ ) {
                    Var v = var(c[j]);
                    if (! b_variables.has(v)) {
                        DEBUG << "itp: adding var " << v << " to B" << endl;
                        b_variables.insert(v);
                    }
                }
            }
        } // for each literal in the clause
    } // SAT::init_interpolation
};
