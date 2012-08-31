/*****************************************************************************************[Main.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/
#include <stdlib.h>
#include <errno.h>
#include <fstream>

#include <signal.h>
#include <zlib.h>

#include <iostream>

#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "core/Solver.h"

#include "proof/terms.h"
#include "proof/interpolator.h"

#include "proof/simple.h"
#include "proof/aigterms.h"

using namespace Minisat;

//=================================================================================================


void printStats(Solver& solver)
{
  double cpu_time = cpuTime();
  double mem_used = memUsedPeak();
  printf("restarts              : %"PRIu64"\n", solver.starts);
  printf("conflicts             : %-12"PRIu64"   (%.0f /sec)\n", solver.conflicts   , solver.conflicts   /cpu_time);
  printf("decisions             : %-12"PRIu64"   (%4.2f %% random) (%.0f /sec)\n", solver.decisions, (float)solver.rnd_decisions*100 / (float)solver.decisions, solver.decisions   /cpu_time);
  printf("propagations          : %-12"PRIu64"   (%.0f /sec)\n", solver.propagations, solver.propagations/cpu_time);
  printf("conflict literals     : %-12"PRIu64"   (%4.2f %% deleted)\n", solver.tot_literals, (solver.max_literals - solver.tot_literals)*100 / (double)solver.max_literals);
  if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
  printf("CPU time              : %g s\n", cpu_time);
}


static Solver* solver;
// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int signum) { solver->interrupt(); }

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int signum) {
  printf("\n"); printf("*** INTERRUPTED ***\n");
  if (solver->verbosity > 0){
    printStats(*solver);
    printf("\n"); printf("*** INTERRUPTED ***\n"); }
  _exit(1); }


static void dump_cnf(std::ostream& o, const AIG2CNFAdapter::ClausesVec& clauses)
{
  // determine max var
  int maxvar = 0;
  for (unsigned i=0, size = clauses.size(); i < size; i ++) {
    const AIG2CNFAdapter::LitVec& c = *(clauses[i]);
    for (unsigned j=0, csize = c.size(); j < csize; j ++ ) {
      Var v = var(c[j]);
      if (maxvar < v) maxvar = v;
    }
  }

  // dump cnf in DIMACS format
  o << "p cnf "
    << maxvar
    << " " 
    << clauses.size()
    << std::endl;

  for (unsigned i=0, size = clauses.size(); i < size; i ++) {
    const AIG2CNFAdapter::LitVec& c = *(clauses[i]);

    for (unsigned j=0, csize = c.size(); j < csize; j ++ ) {
      Lit p = c[j];
     
      o << (sign(p) ? var(p) : -var(p)) << " ";
    }
    o << "0" << std::endl;
  }

}


static Term mk_impl(AIGTermFactory& tf, Term a, Term b)
{ return tf.make_or(tf.make_not(a), b); }

static void aigio_test(const std::string& aig_fname)
{
  AIGTermFactory tf; // private factory, shared
  std::ofstream out(aig_fname.c_str());

  AIGTermWriter writer(tf, out), console(tf, std::cout);

  Term a = tf.make_var(0);
  Term b = tf.make_var(1);
  Term c = tf.make_var(2);

  Term e = mk_impl(tf, a, b);
  Term f = mk_impl(tf, a, c);
  Term g = mk_impl(tf, b, tf.make_not(c));

  // formula
  Term z = tf.make_and(tf.make_and(e, f), tf.make_and(a, g));

  std::cout << "TERM = " << tf.repr(z) << std::endl;
  console << z;
  writer << z;
  out.close();

  // re-read file to check equivalence
  Term q;

  // open argv1 with an istream
  std::ifstream is(aig_fname.c_str()); assert(is.is_open());

  AIGTermReader reader( tf, is );

  // reads file back.
  reader >> q;

  Term t = tf.make_not( tf.make_and( tf.make_not(tf.make_and( tf.make_not(z), q)),
                                     tf.make_not(tf.make_and( tf.make_not(q), z))));

  std::ofstream eq("neq.aig");
  AIGTermWriter eq_writer(tf, eq);

  eq_writer << t;
  eq.close();
}

static void dump_problems(Solver& solver, AIGTermFactory& tf, Term a, Term b, int* ga, int ga_size)
{
  Interpolator interpolator(solver, tf);

  std::cout << "Writing test problems..." << std::endl;
  
  // run the interpolator
  Term itp = interpolator.interpolant(ga, ga_size);
  // std::cout << "ITP = " << tf.repr(itp) << std::endl << std::endl;

  { // build cnf for !(A -> I)
    
    Term p = tf.make_not(tf.make_or(tf.make_not(a), itp));
    // std::cout << "P = " << tf.repr(p) << std::endl;

    std::ofstream os("p.aag");
    AIGTermWriter aig_writer(tf, os);
    // AIGTermWriter console(tf, std::cout);
    // console << p;
    aig_writer << p;
    os.close();
  }

  std::cout << std::endl;


  { // build cnf for (B & I)
    
    Term q = tf.make_and(b, itp);
    // std::cout << "Q = " << tf.repr(q) << std::endl;
    
    std::ofstream os("q.aag");
    AIGTermWriter aig_writer(tf, os);
    // AIGTermWriter console(tf, std::cout);
    // console << q;
    aig_writer << q;
    os.close();
  }

  std::cout << std::endl << std::endl;
}

//=================================================================================================
// Main:

// verbosity level
#define LOGGER_VERBOSITY 0

int main(int argc, char** argv)
{
  // shared instances
  AIGTermFactory tf;

  // [MP] IMPORTANT!!! the adapter must be created just-in-time, because it does
  // [MP] not currently support language extension. Thus, the tf should be "stable"
  // whe CNF adaption is to be performed.
  // AIG2CNFAdapter cnf_adapter(tf);

  Term A_aig;
  Term B_aig;
  int* ga, ga_size;

  Logger& logger = Logger::get();
  logger.set_output_level(LOGGER_VERBOSITY);

  try {
    setUsageHelp("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");
    // printf("This is MiniSat 2.0 beta\n");

#if 0 // defined(__linux__) // disabled for PPC
    fpu_control_t oldcw, newcw;
    _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
    printf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif
    // Extra options:
    //
    IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
    IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
    IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));

    parseOptions(argc, argv, true);

    Solver S(PROOF_LOGGING_CHAIN);
    // const ClauseAllocator& ca = S.clause_allocator(); // needed to access clauses
    // const vec<CRef>& clauses = S.solver_clauses();

    double initial_time = cpuTime();

    S.verbosity = verb;

    solver = &S;
    // Use signal handlers that forcibly quit until the solver will be able to respond to
    // interrupts:
    signal(SIGINT, SIGINT_exit);
    signal(SIGXCPU,SIGINT_exit);

    // Set limit on CPU-time:
    if (cpu_lim != INT32_MAX){
      rlimit rl;
      getrlimit(RLIMIT_CPU, &rl);
      if (rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max){
        rl.rlim_cur = cpu_lim;
        if (setrlimit(RLIMIT_CPU, &rl) == -1)
          printf("WARNING! Could not set resource limit: CPU-time.\n");
      } 
    }

    // Set limit on virtual memory:
    if (mem_lim != INT32_MAX){
      rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
      rlimit rl;
      getrlimit(RLIMIT_AS, &rl);
      if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
        rl.rlim_cur = new_mem_lim;
        if (setrlimit(RLIMIT_AS, &rl) == -1)
          printf("WARNING! Could not set resource limit: Virtual memory.\n");
      } 
    }

    // usage: minisat [ io | itp | aig | cnf ] filename
    if ((argc != 3) ||
        (strcmp(argv[1], "io") && strcmp(argv[1], "itp") && strcmp(argv[1], "aig") && strcmp(argv[1], "cnf"))) {

      std::cout << "ir = " << sizeof(InferenceRule) << std::endl;
      std::cout << "hr = " << sizeof(ClauseHypRule) << std::endl;
      std::cout << "rr = " << sizeof(ResRule) << std::endl;

      std::cout << "usage: minisat [ io | itp | aig | cnf ] filename" << std::endl 
                << std::endl
                << "io  - IO self-check, writes a test AIG to filename"  << std::endl
                << "itp - Takes one AIG, splits it into A,B subformulas" << std::endl
                << "      and writes test problems !(A->I), (B^I), both UNSAT" << std::endl
                << "aig - Runs minisat on given aig" << std::endl
                << "cnf - Runs minisat on given cnf" << std::endl
                << std::endl;
      exit(1);
    }

    logger << loglevel(1) << "args: ";
    for (int qq = 0; qq < argc; ++ qq) { logger << loglevel(1) << argv[qq] << " "; }
    logger << loglevel(1) << endlog << endlog;

    if (!strcmp(argv[1], "io")) {
      std::cout << "Self checking I/O " << argv[2] << std::endl;
      aigio_test(argv[2]);

      exit(0);
    }

    if (!strcmp(argv[1], "aig")) {
      // open argv1 with an istream
      std::ifstream is(argv[2]); assert(is.is_open());

      AIGTermReader reader( tf, is );

      Term term; 
      reader >> term;
      // std::cout << "TERM = " << tf.repr(term) << std::endl;

      AIG2CNFAdapter cnf_adapter(tf);
      cnf_adapter.convert(term);
      
      std::ostringstream oss; oss << argv[2] << ".cnf";
      std::string a_name = oss.str();
      std::ofstream o(a_name.c_str());
          
      // std::cout << "-- Dumping CNF to file " << a_name << std::endl;
      // std::cout << tf.repr(term) << std::endl;
          
      // convert AIG to CNF and dump it to o stream
      cnf_adapter.convert(term); 
      dump_cnf(o, cnf_adapter.res()); 
      o.close(); // flush buffers

      gzFile in = gzopen(a_name.c_str(), "rb");
      if (in == NULL)
        printf("ERROR! Could not open file: %s\n", argv[2]), exit(1);
          
      parse_DIMACS(in, S);

      gzclose(in);
    }

    if (!strcmp(argv[1], "cnf")) {
      gzFile in = gzopen(argv[2], "rb");
      if (in == NULL)
        printf("ERROR! Could not open file: %s\n", argv[2]), exit(1);
          
      parse_DIMACS(in, S);

      gzclose(in);
    }

    if (!strcmp(argv[1], "itp")) {
      std::cout << "Input file: " << argv[2] << std::endl;
      std::ostringstream oss; oss << argv[2];

      // CNF-ize using aigtocnf (external)
      const std::string aigname = oss.str();
      oss << ".cnf"; const std::string cnfname = oss.str();

      // prepare to dump cnf
      std::ofstream os(oss.str().c_str());

      // open argv1 with an istream
      std::ifstream is(argv[2]); assert(is.is_open());

      AIGTermReader reader( tf, is );
      // AIGTermWriter console( tf, std::cout );

      simpaig* toplevel;

      try {
        Term term; reader >> term;
        toplevel = AIGTermFactory::TO_AIG(term);
      }

      catch (AIGException ae) {
        std::cerr << ae.msg() << std::endl;
        abort();
      }

      AIG2CNFAdapter cnf_adapter(tf); // stable tf

       { 
         // write A
         std::ostringstream oss; oss << argv[2] << ".A.cnf";
         std::string a_name = oss.str();
         std::ofstream o(a_name.c_str());
          
         std::cout << "-- Dumping CNF for A to file " << a_name << std::endl;
         A_aig = AIGTermFactory::TO_TERM(simpaig_child(toplevel, 0));
         // std::cout << tf.repr(AIGTermFactory::TO_TERM(simpaig_child(toplevel, 0))) << std::endl;
          
         // convert AIG to CNF and dump it to o stream
         cnf_adapter.convert(A_aig); 
         dump_cnf(o, cnf_adapter.res()); 
         o.close();

         gzFile in = gzopen(oss.str().c_str(), "rb");
         if (in == NULL)
           printf("ERROR! Could not open file: %s\n", oss.str().c_str()), exit(1);
          
         parse_DIMACS(in, S); // A
         gzclose(in);
          
         // -- build array with clauses of A
         ga_size = S.nClauses(); ga = (int*)(malloc(sizeof(int) * S.nClauses()));
         for (int i = 0; i < ga_size; ++i) { *(ga+i) = 1 + i; } // cfr Dimacs.h (colors start at 1)
       }

       { // write B
         std::ostringstream oss; oss << argv[2] << ".B.cnf";
         std::string b_name = oss.str();
         std::ofstream o(b_name.c_str());

         std::cout << "-- Dumping CNF for B to file " << b_name << std::endl;

         B_aig = AIGTermFactory::TO_TERM(simpaig_child(toplevel, 1));
         // std::cout << tf.repr(AIGTermFactory::TO_TERM(simpaig_child(toplevel, 1))) << std::endl;

         // convert AIG to CNF and dump it to o stream
         cnf_adapter.convert(B_aig); 
         dump_cnf(o, cnf_adapter.res()); 
         o.close(); // flush buffers

         gzFile in = gzopen(oss.str().c_str(), "rb");
         if (in == NULL)
           printf("ERROR! Could not open file: %s\n", oss.str().c_str()), exit(1);
          
         parse_DIMACS(in, S); // B
         gzclose(in);
       }
    }

    if (S.verbosity > 0){
      printf("============================[ Problem Statistics ]=============================\n");
      printf("|                                                                             |\n"); }

    // FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;
    FILE* res = NULL;

    if (S.verbosity > 0){
      printf("|  Number of variables:  %12d                                         |\n", S.nVars());
      printf("|  Number of clauses:    %12d                                         |\n", S.nClauses()); }

    double parsed_time = cpuTime();
    if (S.verbosity > 0){
      printf("|  Parse time:           %12.2f s                                       |\n", parsed_time - initial_time);
      printf("|                                                                             |\n"); }

    // Change to signal-handlers that will only notify the solver and allow it to terminate
    // voluntarily:
    signal(SIGINT, SIGINT_interrupt);
    signal(SIGXCPU,SIGINT_interrupt);

    if (!S.simplify()){
      if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
      if (S.verbosity > 0){
        printf("===============================================================================\n");
        printf("Solved by unit propagation\n");
        printStats(S);
        printf("\n"); }
      printf("UNSATISFIABLE\n");

      if (!strcmp(argv[1], "itp")) {
        dump_problems(*solver, tf, A_aig, B_aig, ga, ga_size);

        return 20;
      }
    }
    vec<Lit> dummy;
    lbool ret = S.solveLimited(dummy);
    if (S.verbosity > 0){
      printStats(S);
      printf("\n"); }
    printf(ret == l_True ? "SATISFIABLE\n" : ret == l_False ? "UNSATISFIABLE\n" : "INDETERMINATE\n");
    if (res != NULL){
      if (ret == l_True){
        fprintf(res, "SAT\n");
        for (int i = 0; i < S.nVars(); i++)
          if (S.model[i] != l_Undef)
            fprintf(res, "%s%s%d", (i==0)?"":" ", (S.model[i]==l_True)?"":"-", i+1);
        fprintf(res, " 0\n");
      }else if (ret == l_False) {
        fprintf(res, "UNSAT\n");

      }
      else
        fprintf(res, "INDET\n");
      fclose(res);
    }

    if (!strcmp(argv[1], "itp") && (ret == l_False)) {
      dump_problems(*solver, tf, A_aig, B_aig, ga, ga_size);
    }
           
#ifdef NDEBUG
    exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
    return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
  } catch (OutOfMemoryException&){
    printf("===============================================================================\n");
    printf("INDETERMINATE\n");
    exit(0);
  }
}
