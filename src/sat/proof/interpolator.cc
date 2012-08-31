// interpolator.cc: Craig interpolation-related interfaces and classes
// Author: Alberto Griggio
//         Marco Pensallorto

#include "interpolator.h"
#include "Solver.h"

#include <cassert>
#include <sstream>

namespace Minisat {

  Interpolator::Interpolator(Solver& owner, TermFactory& factory)
    : f_owner(owner)
    , f_factory(factory)
  {
    Logger::get().set_output_level(0);
  }
  
  Interpolator::~Interpolator()
  {
    // Cache elements needs no cleanup here because allocated memory
    // belongs to the term factory, thus it is its own responsibility
    // to free it.
  }

  void Interpolator::init_interpolation(int* groups_of_a, unsigned n)
  {
    // local accessors
    ProofManager& pm = *(f_owner.pm);
    ClauseAllocator& ca = f_owner.ca;

    Logger& logger = Logger::get();
    
    logger << loglevel(2) 
           << "Initializing interpolation" << endlog;
    
    a_variables.clear();
    b_variables.clear();

    // The set of input groups for A
    Set<int> ga; 
    for (unsigned i = 0; i < n; ++ i) { int group = *(groups_of_a+i); ga.insert(group); }

    // load clauses from Solver, for each clause decide whether its A or B
    // according to the color in the hypothesis for that (original) clause
    for (int i = 0, nclauses = f_owner.nClauses(); i < nclauses; i ++ ) {
      CRef cr = f_owner.clauses[i];
      ClauseHypRule& hyp = dynamic_cast<ClauseHypRule&> (pm.proof(cr));
      Clause& c = ca[cr];

      if (ga.has(hyp.color())) {
        logger << loglevel(2) << "clause " << c << " to A" << endlog;
        assert (! a_clauses.has(cr)); 
        a_clauses.insert(cr); 

        // register each var in the clause as belonging to A
        for (int j = 0, cl_size = c.size(); j < cl_size; j ++ ) {
          Var v = var(c[j]);
          if (! a_variables.has(v)) {
            logger << loglevel(2) << "itp: adding var " << v << " to A" << endlog;
            a_variables.insert(v);
          }
        }
      }

      else {
        logger << loglevel(2) << "clause " << c << " to B" << endlog;

        // register each var in the clause as belonging to B
        for (int j = 0, cl_size = c.size(); j < cl_size; j ++ ) {
          Var v = var(c[j]);
          if (! b_variables.has(v)) {
            logger << loglevel(2) << "itp: adding var " << v << " to B" << endlog;
            b_variables.insert(v);
          }
        }
      }
    } // for each literal in the clause
  }

  Term Interpolator::interpolant(int* groups_of_a, unsigned n)
  {
    // local accessors
    ProofManager& pm = *(f_owner.pm);
    ClauseAllocator& ca = f_owner.ca;
    InferenceRule& unsat_proof = pm.proof();

    // internal cache for memoizing
    R2T_Map r2t;
    
    // [MP] setup internal structures
    init_interpolation(groups_of_a, n);

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
          Clause& c = ca[cr];
          Term trm = NULL;
    
          for (int i = 0, sz = c.size(); i < sz; ++i) {
            Lit p = c[i];

            if (lit_is_of_B(p)) {
              Var v = var(p);
              assert(var_is_of_A(v) && var_is_of_B(v));
              
              Term t = f_factory.make_var(v);
              if (NULL == t) continue; /* cnf var */

              if (sign(p)) { t = f_factory.make_not(t); }

              if (NULL == trm) { trm = t;} 
              else { trm = f_factory.make_or(trm, t); }
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

        Term s = r2t.has(start) ? r2t[start] : NULL;
        if (NULL == s) to_process.push(start);

        bool children_done = (NULL != s);
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

            Term p = r2t.has(ir) ? r2t[ir] : NULL;
            Term cur = NULL;
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
  }

} // namespace Minisat

