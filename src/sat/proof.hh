/**
 *  @file proof.hh
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
#ifndef PROOF_H_DEFINED
#define PROOF_H_DEFINED

#include <Vec.hh>
#include <Map.hh>

#include "core/Solver.hh"

#include <common.hh>
#include "utils/solverlogger.hh"

// comment this out to disable debugging
// #define DEBUG_PROOF_LOGGING

namespace Minisat {

    // a generic inference rule (base, abstract class)
    class InferenceRule {
        int f_refcount;

        // Don't allow copying (error prone):
        InferenceRule&  operator= (InferenceRule& other) { assert(0); return *this; }
        InferenceRule (InferenceRule& other) { assert(0); }

    public:
        InferenceRule(): f_refcount(1) {}
        virtual ~InferenceRule() {};

        // reference counting
        inline int nrefs() const { return f_refcount; }
        inline InferenceRule& ref() {
            ++ f_refcount;

#ifdef DEBUG_PROOF_LOGGING
            Logger::get() << loglevel(20)
                          << "Inc ref count for InferenceRule @" << this
                          << " (now is " << f_refcount << ")" << endlog;
#endif
            return *this;
        }

        inline void unref() {
            -- f_refcount;

#ifdef DEBUG_PROOF_LOGGING
            assert(0 <= f_refcount);
            Logger::get() << loglevel(20)
                          << "Dec ref count for InferenceRule @" << this
                          << " (now is " << f_refcount << ")" << endlog;
#endif

            if (0 == f_refcount) { delete this; }
        }
    };

    struct VR_Pair_TAG {
        Var v; InferenceRule* ir;
        VR_Pair_TAG(Var v_, InferenceRule& ir_) : v(v_), ir(&ir_) {}
    };
    typedef vec<struct VR_Pair_TAG> Chain;

    // a rule to introduce hypotheses from the context
    class ClauseHypRule: public InferenceRule {
        CRef f_cref;
        long f_color;

    public:
        ClauseHypRule(CRef cr, long color)
            : f_cref(cr)
            , f_color(color)
        {}

        virtual ~ClauseHypRule() {}

        inline int  color() const { return f_color; }
        inline CRef cref() const { return f_cref; }
        inline void set_cref(CRef cr) { f_cref = cr; } // reserved for update
    };

    // resolution chain rule
    class ResRule: public InferenceRule {

    protected:
        InferenceRule *start;
        Chain chain;

    public:
        ResRule(InferenceRule& s) { start = &s; }
        virtual ~ResRule() {};

        inline void add_to_chain(Var pivot, InferenceRule& r) {
            chain.push(VR_Pair_TAG(pivot, r));
        }

        inline int chain_size() { return chain.size(); }
        inline InferenceRule& get_start() { return *start; }

        inline Var chain_get_ith_var(int i) { return chain[i].v; }
        inline InferenceRule* chain_get_ith_rule(int i) { return chain[i].ir; }
    };

    class ProofManager {
        // keep a ref to owner Solver to access its internal data (dirty
        // but necessary, minimize impact on Minisat code).
        Solver* f_owner;

        InferenceRule* f_unsat_proof;

        /* Clause (cref actually) to Inference rule mapping */
        typedef Map<CRef, InferenceRule*> C2R_Map;
        typedef Map<CRef, InferenceRule*>::Pair C2R_Pair;
        C2R_Map* f_c2r;
        C2R_Map* f_reloc_c2r; // used for clause relocation

    public:
        ProofManager(Solver*);
        ~ProofManager();

        inline void store_hyp_proof(CRef cr, long color) {
            store_proof(cr, *(new ClauseHypRule(cr, color)));
        }

        // store proof associated to clause
        inline InferenceRule& store_proof(CRef cr, InferenceRule& ir) {

            C2R_Map& c2r = (*f_c2r);

#ifdef DEBUG_PROOF_LOGGING
            Clause& c = f_owner->ca[cr];
            Logger::get() << loglevel(10) << "Storing proof for Clause @" << cr << ", " << c << endlog;
#endif

            assert( ! c2r.has(cr) );
            c2r.insert( cr, &ir);

            return ir;
        }

        // true iff cref occurs in more than one proof
        inline bool is_shared_cref(CRef cr)
        {
            C2R_Map& c2r = (*f_c2r);
            return (c2r.has(cr) && (1 < c2r[cr]->nrefs()));
        }

        // remove proof associated to clause
        inline void remove_proof(CRef cr) {

            C2R_Map& c2r = (*f_c2r);

#ifdef DEBUG_PROOF_LOGGING
            Clause& c = f_owner->ca[cr];
            Logger::get() << loglevel(8) << "Removing proof for Clause @" << cr << endlog;
#endif

            assert( c2r.has(cr) );
            InferenceRule* ir = c2r[cr];

            c2r.remove(cr);
            ir->unref();
        }

        // begin update transaction (used by relocAll)
        inline void begin_update() {

#ifdef DEBUG_PROOF_LOGGING
            C2R_Map& c2r = (*f_c2r);

            Logger::get()
                << loglevel(4)
                << "Update transaction started, "
                << c2r.elems() << " elements need remapping."
                << endlog;
#endif

            assert (NULL == f_reloc_c2r);
            f_reloc_c2r = new C2R_Map();
        }

        // end update transaction (used by relocAll)
        inline void end_update() {
            C2R_Map& c2r = (*f_c2r);

            assert (NULL != f_reloc_c2r);
            assert (NULL != f_c2r);

            if (0 < c2r.elems()) {
                ERR << "Incomplete update, following elements were missing" << endl;

                for (int i = c2r.bucket_count() -1; 0 <= i; -- i) {
                    const vec<C2R_Pair>& bucket = c2r.bucket(i);

                    for (int j = bucket.size() -1; 0 <= j; --j) {
                        const C2R_Pair& c2r = bucket[j];
                        ERR << c2r.key << endl;
                    }
                }

                abort();
            }

            delete f_c2r;
            f_c2r = f_reloc_c2r;
            f_reloc_c2r = NULL;

#ifdef DEBUG_PROOF_LOGGING
            Logger::get() << loglevel(4) << "Update transaction finished." << endlog;
#endif
        }

        inline void update( CRef new_cr, CRef orig_cr ) {

            C2R_Map& orig_c2r = (*f_c2r);
            C2R_Map& temp_c2r = (*f_reloc_c2r);

#ifdef DEBUG_PROOF_LOGGING
            Logger::get() << loglevel(8) <<
                "updating @" << orig_cr << " --> @" << new_cr << endlog;
#endif
            assert( orig_c2r.has(orig_cr) );

            InferenceRule* ir = orig_c2r[orig_cr];
            assert (NULL != ir);

            ClauseHypRule* hyp;
            if (NULL != (hyp = dynamic_cast<ClauseHypRule *>(ir))) {
                assert(orig_cr == hyp->cref()); hyp->set_cref(new_cr);
            }

            assert( ! temp_c2r.has( new_cr) );
            temp_c2r.insert(new_cr, ir);
            orig_c2r.remove(orig_cr);
        }

        inline InferenceRule& proof(CRef cr) const {
            C2R_Map& c2r = (*f_c2r);

            if (! c2r.has(cr) ) {
                ERR << "Missing rule for Clause @" << cr << std::endl;
                abort();
            }
            return *c2r[cr];
        }

        // proof of unsatisfiability
        inline InferenceRule& proof() {

            if (NULL == f_unsat_proof) {
                ERR << "proof of unsatisfiability not available!" << std::endl;
                abort();
            }
            return *f_unsat_proof;
        }

        // build UNSAT proof for conflicting clause
        void build_toplevel_conflict_proof(CRef cr);

#ifdef PROOF_CHECK
        // debug
        bool check_unsat_proof(InferenceRule& rule, const vec<Lit>& expected);
        bool check_reasons();
#endif
    };
}

#endif
