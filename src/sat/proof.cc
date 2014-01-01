/**
 *  @file proof.cc
 *  @brief UNSAT proof logging
 *
 *  This module contains the definitions for Unsatisfiability proof
 *  logging.
 *
 *  Authors: Alberto Griggio, Marco Pensallorto
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the addterms of the GNU Lesser General Public
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
#include <algorithm>
#include <cassert>
#include <map>
#include <stack>

#include "proof.hh"
#include <mtl/Sort.hh>

namespace Minisat {

    ProofManager::ProofManager(Solver* owner)
        : f_owner(owner)
        , f_unsat_proof(NULL)
        , f_c2r(new C2R_Map())
        , f_reloc_c2r(NULL)
    {
#ifdef DEBUG_PROOF_LOGGING
        Logger& logger = Logger::get();
        logger << loglevel(2) << "Proof Manager initialized" << endlog;
#endif
    }

    ProofManager::~ProofManager()
    {
        C2R_Map& c2r = (*f_c2r);
        assert( NULL == f_reloc_c2r );

        /* free CRef -> IR mapping */
        for (int i = c2r.bucket_count() -1; 0 <= i; -- i) {
            const vec<C2R_Pair>& bucket = c2r.bucket(i);

            for (int j = bucket.size() -1; 0 <= j; --j)
                if (NULL != bucket[j].data) delete bucket[j].data;
        }

        delete f_c2r;

#ifdef DEBUG_PROOF_LOGGING
        Logger& logger = Logger::get();
        logger << loglevel(2) << "Proof manager destroyed" << endlog;
#endif
    }

    // [AG] confl_ref is the conflicting clause with all variables
    // assigned at level zero. To build the proof, we keep resolving each
    // literal with its reason, until we get the empty clause
    void ProofManager::build_toplevel_conflict_proof(CRef confl_ref)
    {
        assert(confl_ref != CRef_Undef);

#ifdef DEBUG_PROOF_LOGGING
        Logger& logger = Logger::get();
        logger << loglevel(4)
               << "Building UNSAT proof, clause: "
               << f_owner->ca[confl_ref] << endlog;
#endif

#ifdef PROOF_CHECK
        check_reasons();
#endif

        vec<char> seen(f_owner->nVars(), 0);
        ResRule *res = NULL;
        int j, trail_last = f_owner->trail.size() -1;

        Lit p = lit_Undef;
        do {
            assert(confl_ref != CRef_Undef);
            Clause &confl = f_owner->ca[confl_ref];
            // Logger::get() << loglevel(8) << "Current clause: " << confl << endlog;

            j = 0; if (p == lit_Undef) { res = new ResRule( proof(confl_ref).ref()); }
            else { j ++; }

            // update seen vars
            while (j < confl.size()) { seen[var(confl[j ++])] = 1; }

            // Select next clause to look at:
            do {
                if (trail_last < 0) goto finished;

                p = f_owner->trail[trail_last --];
                confl_ref = f_owner->reason(var(p));
            } while (!seen[var(p)]);

            if (p != lit_Undef) {
                seen[var(p)] = 0;

#ifdef DEBUG_PROOF_LOGGING
                logger << loglevel(8)
                       << " Chaining reason for p:" << p << ", @" << confl_ref << endlog;
#endif
                if (CRef_Undef != confl_ref) {
                    res->add_to_chain(var(p), proof(confl_ref).ref());
                }
            }
        } while (trail_last >= 0);

    finished:
        /* assign result to internal field */
        f_unsat_proof = res;

#ifdef PROOF_CHECK
        assert(NULL != f_unsat_proof);
        vec<Lit> empty; check_unsat_proof(*f_unsat_proof, empty);
#endif
    }


    // Debug code, to be disabled upon release
    //
#ifdef PROOF_CHECK

    static void sort_for_check(vec<Lit> &out);

    // check unsat proof
    bool ProofManager::check_unsat_proof(InferenceRule& rule, const vec<Lit>& expected_) {

        Logger& logger = Logger::get();

        vec<Lit> expected; expected_.copyTo(expected);
        sort_for_check(expected);

        logger << loglevel(1)
               << "Checking UNSAT proof (" << expected_.size() << " literals expected) ... ";

        std::stack<InferenceRule *> to_process;
        to_process.push(&rule);

        typedef std::map<InferenceRule *, vec<Lit> *> Cache;
        Cache cache;

        while ( !to_process.empty() ) {
            ResRule *res = NULL;
            ClauseHypRule *hyp = NULL;

            InferenceRule *r = to_process.top();
            if (NULL != cache[r]) { to_process.pop();  continue;}

            if (NULL != (res = dynamic_cast<ResRule *>(r))) {
                InferenceRule* start = &res->get_start();
                vec<Lit> *c1 = cache[start];
                if (!c1) to_process.push(start);

                bool done = (c1 != NULL);

                for (int i =0; i < res->chain_size(); ++ i ) {
                    InferenceRule* ir = res->chain_get_ith_rule(i);

                    vec<Lit> *c = cache[ir];
                    if (!c) { to_process.push(ir);  done = false; }
                }
                if (done) {
                    to_process.pop();
                    vec<Lit> *out = new vec<Lit>();
                    bool first_time = true;

                    for (int i = 0; i < res->chain_size(); ++i) {
                        Var v = res->chain_get_ith_var(i);
                        InferenceRule* ir = res->chain_get_ith_rule(i);

                        vec<Lit> *c2 = cache[ir];
                        if (!c2) abort();
                        bool pos_found = false, neg_found = false;
                        bool err = false;
                        for (int j = 0; j < 2; ++j) {
                            vec<Lit> *cur = j ? c2 : c1;
                            for (int i = 0; i < cur->size(); ++i) {
                                err = false;
                                Lit l = (*cur)[i];
                                if (var(l) == v) {
                                    if (sign(l)) {
                                        if (neg_found) err = true;
                                        else neg_found = true;
                                    } else {
                                        if (pos_found) err = true;
                                        else pos_found = true;
                                    }
                                } else {
                                    out->push(l);
                                }
                                if (err) break;
                            }
                            if (err) break;
                        }
                        if (!pos_found || !neg_found || err) {
                            std::cout << "WRONG RESOLUTION:, c1 = "
                                      << *c1 << ", c2 = " << *c2 << ", pivot = "
                                      << v << std::endl;

                            abort();
                            return false;
                        }
                        sort_for_check(*out);
                        if (!first_time) delete c1;
                        else first_time = false;
                        c1 = out;
                        out = new vec<Lit>();
                    }
                    if (first_time) {
                        //assert(false);
                        vec<Lit> *t = new vec<Lit>();
                        c1->copyTo(*t);
                        c1 = t;
                    }
                    sort_for_check(*c1);
                    cache[r] = c1;
                }
            } // ResRule

            else if (NULL != (hyp = dynamic_cast<ClauseHypRule *>(r))) {
                to_process.pop();
                Clause& c = f_owner->ca[hyp->cref()];

                vec<Lit> *out = new vec<Lit>();
                for (int i = 0; i < c.size(); ++i) { out->push(c[i]); }

                sort_for_check(*out); cache[r] = out;
            } // HypRule

            else assert(0); // ??
        }

        vec<Lit> *result = cache[&rule];
        if (0 < expected.size()) {
            bool ok = true;

            // vec<Lit> tmp;  expected.copyTo(tmp);
            // sort(tmp);
            sort(*result);

            if (expected.size() != result->size()) {
                ok = false;
            } else {
                for (int i = 0; i < expected.size(); ++i) {
                    if (expected[i] != (*result)[i]) {
                        ok = false;
                        break;
                    }
                }
            }
            if (!ok) {
                std::cout << "ERROR: EXPECTED " << expected << ", GOT " << *result
                          << " INSTEAD" << std::endl;
                abort();
            }
        } else {
            if (result->size()) {
                std::cout << "ERROR: EXPECTED <empty>, GOT " << *result
                          << " INSTEAD" << std::endl;
                abort();
            }
        }

        // clear the cache
        for (Cache::iterator i = cache.begin(), end = cache.end(); i != end; ++i) {
            delete (i->second);
        }

        logger << loglevel(1) << "OK" << endlog;
        return true;
    }

    // [MP] check that for each assigned variable in the trail, a reason is available
    bool ProofManager::check_reasons()
    {
        assert(f_owner->decisionLevel() == 0);
        for (int i = 0; i < f_owner->trail.size(); ++i) {

            if (CRef_Undef == f_owner->reason(var(f_owner->trail[i]))) {
                std::cout << "ERROR! TRAIL:\n";
                for (int j = 0; j < f_owner->trail.size(); ++j) {
                    CRef cr = f_owner->reason(var(f_owner->trail[j]));
                    if (CRef_Undef != cr) {
                        Clause& c = f_owner->ca[cr];
                        std::cout << f_owner->trail[j] << ": " << c << std::endl;
                    } else std::cout << f_owner->trail[j] << ": <NULL>" << std::endl;
                }

                abort();
            }
        }

        return true;
    }

    // internal services
    //
    static void sort_for_check(vec<Lit> &out)
    {
        if (out.size() == 0) return;

        sort(out);
        Lit *p = std::unique(&(out[0]), &(out[0])+out.size());
        out.shrink(out.size() - (p-&(out[0])));
    }

#endif
}
