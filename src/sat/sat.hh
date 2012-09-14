/**
 *  @file sat.hh
 *  @brief SAT interface
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
#ifndef SAT_H
#define SAT_H

// general purpose decls
#include "satdefs.hh"
#include "terms/terms.hh"
#include "proof/proof.hh"
#include "cuddObj.hh"

#include <Map.hh>
#include <Set.hh>
#include <Vec.hh>

// the glorious Minisat SAT solver
#include "core/Solver.hh"

namespace Minisat {

    template <class Term>
    class SAT;

    class BDDTermFactory : public TermFactory<BDD> {
    public:
        BDDTermFactory(Cudd& cudd)
            : f_cudd(cudd)
        { TRACE << "Initialized BDD Factory instance @" << this << endl; }

        ~BDDTermFactory()
        { TRACE << "Destroyed BDD Factory instance @" << this << endl; }

        // constants
        virtual BDD make_true()
        { return f_cudd.bddOne(); }
        virtual bool is_true(BDD t)
        { return t.IsOne(); }

        virtual BDD make_false()
        { return f_cudd.bddZero(); }
        virtual bool is_false(BDD t)
        { return t.IsZero(); }

        // variables
        virtual BDD make_var(Var v)
        { return f_cudd.bddVar(v); }

        // basic logical operators
        virtual BDD make_and(BDD t1, BDD t2)
        { return t1 & t2; }
        virtual BDD make_or(BDD t1, BDD t2)
        { return t1 | t2; }
        virtual BDD make_not(BDD t)
        { return !t; }

    private:
        Cudd& f_cudd;
    }; // Term Factory

    template <class Term>
    class CNFizer {
    public:
        CNFizer(SAT<Term>* owner)
            : f_owner(*owner)
        { TRACE << "Initialized CNFizer instance @" << this << endl; }

        ~CNFizer()
        { TRACE << "Destroyed CNFizer instance @" << this << endl; }

        void push(Term phi, const group_t group, const color_t color);

    private:
        SAT<Term>& f_owner; // the SAT instance
    }; // CNFizer

    template <class Term>
    class ModelExtractor {
    public:
        ModelExtractor(SAT<Term>* owner)
            : f_owner(*owner)
        { TRACE << "Initialized ModelExtractor instance @" << this << endl; }

        ~ModelExtractor()
        { TRACE << "Destroyed ModelExtractor instance @" << this << endl; }

        Term model()
        { return f_owner.factory().make_false(); }

    private:
        SAT<Term>& f_owner; // the SAT instance
    }; // ModelExtractor

    template <class Term>
    class Interpolator {

    public:
        Interpolator(SAT<Term>* owner)
            : f_owner(*owner)
        { TRACE << "Initialized Interpolator instance @" << this << endl; }

        ~Interpolator()
        { TRACE << "Destroyed Interpolator instance @" << this << endl; }

        Term interpolant(const Colors& a)
        {
            // local accessors
            // ProofManager& pm = *(f_owner.pm);
            ProofManager& pm = f_owner.solver().proof_manager();
            const ClauseAllocator& ca = f_owner.solver().clause_allocator();
            InferenceRule& unsat_proof = pm.proof();
            TermFactory<Term>& f_factory = f_owner.factory();

            // internal cache for memoizing
            R2T_Map r2t;

            // [MP] setup internal structures
            init_interpolation(a);

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
        } // interpolant()

    protected:
        typedef struct ptr_hasher<InferenceRule*> InferenceRuleHasher;
        typedef Map< InferenceRule* , Term, InferenceRuleHasher> R2T_Map;

        // The set of clauses belonging to A (B is the complement)
        Set<CRef> a_clauses;

        // The set of variables belonging to A
        Set<Var> a_variables;
        Set<Var> b_variables;

        // owner instance
        SAT<Term>& f_owner;

        void init_interpolation(const Colors& ga)
        {
            // local accessors
            const Solver& solver = f_owner.solver();
            ProofManager& pm = solver.proof_manager();
            const ClauseAllocator& ca = solver.clause_allocator();

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
            for (int i = 0, nclauses = solver.nClauses(); i < nclauses; i ++ ) {
                CRef cr = solver.clauses[i];
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
        } // init_interpolation

        // [AG] here the definition of "local" is that given by McMillan:
        // for a pair of formulas (A, B), an atom x is local if it
        // contains a variable or uninterpreted function symbol not in B
        // and global otherwise.
        inline bool atom_is_A_local(Var atom) const
        { return !atom_is_of_B(atom); }

        inline bool var_is_A_local(Var var) const
        { return atom_is_A_local(var); }

        inline bool lit_is_A_local(Lit lit) const
        { return atom_is_A_local(var(lit)); }

        inline bool var_is_of_B(Var var) const
        { return atom_is_of_B(var); }

        inline bool lit_is_of_B(Lit lit) const
        { return atom_is_of_B(var(lit)); }

        inline bool var_is_of_A(Var var) const
        { return atom_is_of_A(var); }

        inline bool lit_is_of_A(Lit lit) const
        { return atom_is_of_A(var(lit)); }

        inline bool atom_is_of_A(Var atom) const
        { return a_variables.has(atom); }

        inline bool atom_is_of_B(Var atom) const
        { return b_variables.has(atom); }

        inline bool clause_is_of_A(CRef cr) const
        { return a_clauses.has(cr); }
    }; // Interpolator

    template <class Term>
    class SAT : public IObject {
        friend class ModelExtractor<Term>;
        friend class Interpolator<Term>;

    public:
        /**
         * @brief Adds a new formula group to the SAT instance.
         */
        group_t new_group()
        {
            group_t res = ++ f_next_group;
            f_groups.insert(res);

            return res;
        }

        /**
         * @brief Returns the complete set of defined SAT groups.
         */
        Groups& groups()
        { return f_groups; }

        /**
         * @brief Adds a new interpolation color to the SAT instance.
         */
        color_t new_color()
        {
            color_t res = ++ f_next_color;
            f_colors.insert(res);

            return res;
        }

        /**
         * @brief Returns the complete set of defined interpolation
         * colors.
         */
        Colors& colors()
        { return f_colors; }

        /**
         * @brief add a formula with a given group and color to the
         * SAT instance.
         */
        void push(Term t,
                  group_t group = MAINGROUP,
                  color_t color = BACKGROUND)
        { f_cnfizer.push(t, group, color); }

        /**
         * @brief Solve all groups.
         */
        status_t solve()
        { return solve_groups(f_groups); }

        /**
         * @brief Solve only given groups.
         */
        status_t solve(const Groups& groups)
        { return solve_groups(groups); }

        /**
         * @brief Last solving status
         */
        status_t status()
        { return f_status; }

        /**
         * @brief Retrieve a model from the SAT instance. Remark:
         * current status must be STATUS_SAT. An exception will be
         * raised otherwise.
         */
        Term model()
        {
            assert (f_status == STATUS_SAT);
            return f_model_extractor.model();
        }

        /**
         * @brief Retrieve an interpolant model from the SAT
         * instance. Remark: current status must be STATUS_UNSAT. An
         * exception will be raised otherwise.
         */
        Term interpolant(const Colors& a)
        {
            assert (f_status == STATUS_UNSAT);
            return f_interpolator.interpolant(a);
        }

        SAT(TermFactory<Term>& factory)
            : f_factory(factory)
            , f_solver()
            , f_cnfizer(this)
            , f_model_extractor(this)
            , f_interpolator(this)
            , f_next_group(0)
            , f_next_color(0)
        { TRACE << "Initialized SAT instance @" << this << endl; }

        ~SAT()
        { TRACE << "Destroyed SAT instance@" << this << endl; }

    protected:
        // these methods are reserved for internal usage by sub-components.
        TermFactory<Term>& factory() const
        { return f_factory; }

        const Solver& solver() const
        { return f_solver; }

    private:
        // Term factory
        TermFactory<Term>& f_factory;

        // SAT solver
        Solver f_solver;

        // CNFizer
        CNFizer<Term> f_cnfizer;

        // ModelExtractor
        ModelExtractor<Term> f_model_extractor;

        // Interpolator
        Interpolator <Term> f_interpolator;

        Groups f_groups;
        group_t f_next_group;

        Colors f_colors;
        color_t f_next_color;

        status_t f_status;

        // services
        status_t solve_groups(const Groups& groups)
        {
            vec<Lit> assumptions;

            // MTL Set interface is a bit awkard here :-/
            int bckt, bckts = groups.bucket_count();
            for (bckt = 0; bckt < bckts ; ++ bckt) {
                const vec<group_t>& gs = groups.bucket(bckt);
                for (int i = 0; i < gs.size(); ++ i) {
                    assumptions.push(mkLit(gs[i], true)); // a -> phi, negate a
                }
            }

            f_status = f_solver.solve()
                ? STATUS_SAT
                : STATUS_UNSAT
                ;

            return f_status;
        }

    }; // SAT instance

}; // minisat

#endif
