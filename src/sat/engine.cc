#include <query/runtime.hh>
/**
 * @file sat/engine.cc
 * @brief SAT interface subsystem, Engine class implementation.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#include <cstdlib>
#include <set>
#include <sat.hh>
#include <opts/opts_mgr.hh>
#include <cadical.hpp>
#include <sat/proof_tracer.hh>
#include <atomic>
#include <climits>

namespace sat {

    // Only the owner thread accesses CaDiCaL. Other threads may set interrupted.
    class Engine::Backend : public CaDiCaL::Terminator {
    public:
        std::unique_ptr<proof::ProofTracer> tracer;
        CaDiCaL::Solver solver;
        std::vector<int> variables;
        std::atomic<bool> interrupted {false};
        uint64_t solves = 0, clauses = 0;
        int64_t configured_conflicts = -1, configured_propagations = -1;
        uint64_t configured_conflict_base = 0, configured_propagation_base = 0;
        uint64_t conflict_base = 0, propagation_base = 0;
        int64_t conflict_limit = -1, propagation_limit = -1;

        Backend(Mode mode, size_t proof_node_limit)
        {
            if (std::string(CaDiCaL::Solver::version()) != "3.0.1" ||
                std::string(CaDiCaL::Solver::signature()) != "cadical-3.0.1-c607304")
                throw std::runtime_error("Expected the pinned CaDiCaL 3.0.1 build");
            if (mode == Mode::proof) {
                if (!solver.configure("plain") || !solver.set("factor", 0) ||
                    !solver.set("lucky", 0) || !solver.set("walk", 0))
                    throw std::runtime_error("Invalid proof solver configuration");
                tracer = std::make_unique<proof::ProofTracer>(
                    [] { query::checkpoint(query::Phase::encoding); }, proof_node_limit);
                solver.connect_proof_tracer(tracer.get(), true);
            }
            if (!solver.set("quiet", 1) ||
                // Repeated incremental solves spend excessive time in the
                // inprobe simplification schedule on bounded LLVM models.
                !solver.set("inprobing", Engine::solver_inprobing()) ||
                !solver.set("seed", opts::OptsMgr::INSTANCE().sat_random_seed()))
                throw std::runtime_error("Invalid CaDiCaL configuration");
            solver.connect_terminator(this);
        }
        ~Backend() {
            solver.disconnect_terminator();
            if (tracer) solver.disconnect_proof_tracer(tracer.get());
        }

        uint64_t counter(const char* name) const
        {
            const auto count = solver.get_statistic_value(name);
            if (count < 0) throw std::logic_error("Unknown CaDiCaL statistic");
            return static_cast<uint64_t>(count);
        }
        int literal(Lit value) const
        {
            const int id = variables.at(var(value));
            return sign(value) ? -id : id;
        }
        query::StopReason budget_stop() const
        {
            if (conflict_limit >= 0 && counter("conflicts") - conflict_base >= uint64_t(conflict_limit))
                return query::StopReason::conflict_budget;
            if (propagation_limit >= 0 && counter("propagations") - propagation_base >= uint64_t(propagation_limit))
                return query::StopReason::propagation_budget;
            return query::StopReason::none;
        }
        bool terminate() override
        {
            return interrupted.load(std::memory_order_relaxed) ||
                   (tracer && tracer->failed()) ||
                   budget_stop() != query::StopReason::none;
        }
    };

    const char* Engine::solver_version() { return CaDiCaL::Solver::version(); }
    const char* Engine::solver_signature() { return CaDiCaL::Solver::signature(); }
    bool Engine::solver_inprobing() { return false; }

    std::ostream& operator<<(std::ostream& os, const Engine& engine)
    {
        const auto& backend = *engine.f_solver;
        return os << "Solver: `" << engine.f_instance_name
                  << "`, " << Engine::solver_signature()
                  << ", solves: " << backend.solves
                  << ", decs: " << backend.counter("decisions")
                  << ", search props: " << backend.counter("propagations")
                  << ", conflicts: " << backend.counter("conflicts")
                  << ", vars: " << backend.variables.size()
                  << ", submitted clauses: " << backend.clauses;
    }

    namespace {
        int64_t remaining(int64_t budget, uint64_t used)
        {
            if (budget < 0) return -1;
            return used >= uint64_t(budget) ? 0 : budget - static_cast<int64_t>(used);
        }
        int64_t tighter(int64_t first, int64_t second)
        {
            return first < 0 ? second : second < 0 ? first : std::min(first, second);
        }
    }

    Engine::Engine(const char* instance_name, Mode mode, size_t proof_node_limit)
        : f_instance_name(instance_name)
        , f_mode(mode)
        , f_enc_mgr(enc::EncodingMgr::INSTANCE())
        , f_solver(std::make_unique<Backend>(mode, proof_node_limit))
        , f_cnf_optimization_enabled(false)
        , f_optimization_in_progress(false)
    {
        opts::OptsMgr& opts_mgr { opts::OptsMgr::INSTANCE() };
        if (mode == Mode::normal && (opts_mgr.cnf_tautology_removal() ||
            opts_mgr.cnf_duplicate_removal() ||
            opts_mgr.cnf_subsumption() ||
            opts_mgr.cnf_variable_elimination() ||
            opts_mgr.cnf_self_subsumption() ||
            opts_mgr.cnf_blocked_clause()))
            enable_cnf_optimization(true);

        // Internal zero remains the main group/true microcode constant.
        f_groups.push_back(new_sat_var(true));
        if (mode == Mode::proof) add_proof_clause({mkLit(0)}, proof::Partition::a);
        if (auto context = query::current()) context->attach(this);
        EngineMgr::INSTANCE().register_instance(this);
    }

    Engine::~Engine()
    {
        if (auto context = query::current()) context->detach(this);
        EngineMgr::INSTANCE().unregister_instance(this);
    }

    void Engine::interrupt()
    {
        f_solver->interrupted.store(true, std::memory_order_relaxed);
    }

    void Engine::configure(int64_t conf_budget, int64_t prop_budget)
    {
        if (conf_budget < -1 || prop_budget < -1)
            throw std::invalid_argument("SAT budgets must be -1 or nonnegative");
        auto& b = *f_solver;
        b.configured_conflicts = conf_budget;
        b.configured_propagations = prop_budget;
        b.configured_conflict_base = b.counter("conflicts");
        b.configured_propagation_base = b.counter("propagations");
    }

    void Engine::invalidate_result()
    {
        f_status = STATUS_UNKNOWN;
        f_failed_groups.clear();
    }

    void Engine::set_groups(Groups groups)
    {
        if (f_mode == Mode::proof) throw std::logic_error("Proof engines do not support assumption groups");
        // Reject the entire update before touching either assumptions or results.
        for (const auto group : groups) {
            if (group == std::numeric_limits<group_t>::min() ||
                size_t(std::abs(group)) >= f_solver->variables.size())
                throw std::out_of_range("Invalid SAT group");
        }
        invalidate_result();
        f_groups = std::move(groups);
    }

    bool Engine::assigned(Var variable)
    {
        return f_status == STATUS_SAT && variable >= 0 &&
               size_t(variable) < f_solver->variables.size();
    }

    int Engine::value(Var variable)
    {
        if (!assigned(variable)) throw std::logic_error("No current SAT model for variable");
        return f_solver->solver.val(f_solver->variables[variable]) > 0;
    }

    Var Engine::existing_var(const enc::TCBI& tcbi) const
    {
        const auto found = f_tcbi2var_map.find(tcbi);
        if (found == f_tcbi2var_map.end())
            throw std::logic_error("Observable SAT variable was not allocated before solving");
        return found->second;
    }

    Var Engine::new_sat_var(bool frozen)
    {
        query::checkpoint(query::Phase::encoding);
        auto& b = *f_solver;
        if (b.tracer && b.solves) throw std::logic_error("Proof engines are single-query instances");
        if (b.variables.size() > size_t(MAX_VAR))
            throw std::out_of_range("SAT variable exceeds packed literal range");
        invalidate_result();
        const Var variable = b.variables.size();
        // CaDiCaL can allocate extension variables: never derive its ID from ours.
        const int native = b.solver.declare_one_more_variable();
        b.variables.push_back(native);
        if (frozen) b.solver.freeze(native);
        return variable;
    }

    void Engine::commit_clause(const Lits& literals)
    {
        auto& b = *f_solver;
        // Validate the whole clause before opening the native clause builder.
        for (auto literal : literals) (void)b.literal(literal);
        if (b.tracer && (!b.tracer->submitting || b.solves))
            throw std::logic_error("Proof clauses require a partition before the first solve");
        invalidate_result();
        for (auto literal : literals) b.solver.add(b.literal(literal));
        b.solver.add(0);
        ++b.clauses;
        if (f_mode == Mode::record) f_recorded_clauses.push_back(literals);
        if (b.tracer) b.tracer->check();
    }

    void Engine::add_proof_clause(const Lits& literals, proof::Partition partition)
    {
        query::checkpoint(query::Phase::encoding);
        auto& b = *f_solver;
        if (!b.tracer || b.solves) throw std::logic_error("Proof clauses require a fresh proof engine");
        b.tracer->check();
        std::set<int> native;
        for (auto lit : literals) native.insert(b.literal(lit));
        for (int lit : native) if (native.count(-lit)) return; // tautology has no constraint
        b.tracer->submitted.assign(native.begin(), native.end());
        b.tracer->submitting = partition;
        commit_clause(literals);
        if (b.tracer->submitting) throw std::logic_error("Missing original proof clause callback");
    }

    LitsVector Engine::recorded_clauses() const
    {
        if (f_mode != Mode::record) throw std::logic_error("Engine was not configured to record CNF");
        LitsVector result;
        for (const auto& clause : f_recorded_clauses) {
            query::checkpoint(query::Phase::encoding);
            result.push_back(clause);
        }
        for (auto group : f_groups) result.push_back({mkLit(std::abs(group), group < 0)});
        return result;
    }

    const proof::ResolutionProof& Engine::resolution_proof() const
    {
        if (!f_solver->tracer || f_status != STATUS_UNSAT || !f_solver->tracer->conclusion)
            throw std::logic_error("No current resolution proof");
        f_solver->tracer->check();
        return f_solver->tracer->proof;
    }
    proof::NodeId Engine::proof_root() const
    {
        (void)resolution_proof();
        return *f_solver->tracer->conclusion;
    }
    int Engine::proof_variable(Var variable) const
    {
        if (!f_solver->tracer) throw std::logic_error("Not a proof engine");
        return f_solver->variables.at(variable);
    }

    void Engine::add_clause(const Lits& literals)
    {
        query::checkpoint(query::Phase::encoding);
        invalidate_result();
        if (f_cnf_optimization_enabled && !f_optimization_in_progress)
            f_pending_clauses.push_back(literals);
        else
            commit_clause(literals);
    }

    std::vector<group_t> Engine::failed_groups() const
    {
        return f_status == STATUS_UNSAT ? f_failed_groups : std::vector<group_t>{};
    }

    status_t Engine::sat_solve_groups(const Groups& groups)
    {
        // Invalidate before the checkpoint, which can throw on cancellation.
        invalidate_result();
        query::PhaseTimer timer(query::Phase::solving);
        auto context = query::current();
        auto& b = *f_solver;
        if (b.tracer && b.solves) throw std::logic_error("Proof engines are single-query instances");
        b.conflict_base = b.counter("conflicts");
        b.propagation_base = b.counter("propagations");
        b.conflict_limit = remaining(b.configured_conflicts, b.conflict_base - b.configured_conflict_base);
        b.propagation_limit = remaining(b.configured_propagations, b.propagation_base - b.configured_propagation_base);
        if (context) {
            b.conflict_limit = tighter(b.conflict_limit, remaining(context->limits.conflicts, context->conflicts_used));
            b.propagation_limit = tighter(b.propagation_limit, remaining(context->limits.propagations, context->propagations_used));
        }
        if (const auto reason = b.budget_stop(); reason != query::StopReason::none) {
            if (context) context->cancel(reason);
            return STATUS_UNKNOWN;
        }
        // Even trivial formulas must respect requests made before solve().
        if (b.interrupted.load(std::memory_order_relaxed)) return STATUS_UNKNOWN;

        optimize_and_commit();
        if (!b.tracer) for (const auto group : groups) {
            if (group == std::numeric_limits<group_t>::min())
                throw std::out_of_range("Invalid SAT group");
            b.solver.assume(b.literal(mkLit(std::abs(group), group < 0)));
        }
        // Native limits reset after each solve. Large 64-bit budgets are checked
        // by the callback without narrowing to CaDiCaL's int limit argument.
        const int native_limit = b.conflict_limit >= 0 && b.conflict_limit <= INT_MAX
            ? static_cast<int>(b.conflict_limit) : -1;
        if (!b.solver.limit("conflicts", native_limit))
            throw std::logic_error("CaDiCaL conflict limit unavailable");
        ++b.solves;
        const int status = b.solver.solve();
        if (status == 10) f_status = STATUS_SAT;
        else if (status == 20) f_status = STATUS_UNSAT;
        else if (status != 0) throw std::logic_error("Invalid CaDiCaL solve status");

        const auto reason = b.budget_stop();
        if (context) {
            context->conflicts_used += b.counter("conflicts") - b.conflict_base;
            context->propagations_used += b.counter("propagations") - b.propagation_base;
            context->variables = std::max(context->variables, uint64_t(b.variables.size()));
            context->clauses = std::max(context->clauses, b.clauses);
            if (reason != query::StopReason::none) context->cancel(reason);
            else if (b.interrupted.load(std::memory_order_relaxed)) context->cancel();
            else if (f_status == STATUS_UNKNOWN) context->cancel(query::StopReason::solver_unknown);
        }
        if (reason != query::StopReason::none || b.interrupted.load(std::memory_order_relaxed) ||
            (context && context->stop != query::StopReason::none))
            invalidate_result();

        if (b.tracer) {
            try {
                b.tracer->check();
                if (f_status == STATUS_UNSAT) {
                    b.solver.conclude();
                    b.tracer->check();
                    if (!b.tracer->conclusion) throw std::logic_error("Missing proof conclusion");
                }
            } catch (...) { invalidate_result(); throw; }
        } else if (f_status == STATUS_UNSAT) {
            // Copy signed failed assumptions while the native result is valid.
            for (const auto group : groups)
                if (b.solver.failed(b.literal(mkLit(std::abs(group), group < 0))))
                    f_failed_groups.push_back(group);
        }
        return f_status;
    }

    void Engine::push(const compiler::Unit& cu, step_t time, group_t group)
    {
        query::PhaseTimer timer(query::Phase::encoding);
        /**
         * 1. Pushing DDs
         */
        {
            const dd::DDVector& dv { cu.dds() };
            dd::DDVector::const_iterator i;
            for (i = dv.begin(); dv.end() != i; ++i) {
                cnf_push(*i, time, group);
            }
        }

        /**
         * 2. Pushing CNF for inlined operators
         */
        {
            const compiler::InlinedOperatorDescriptors& inlined_operator_descriptors {
                cu.inlined_operator_descriptors()
            };

            compiler::InlinedOperatorDescriptors::const_iterator i;
            for (i = inlined_operator_descriptors.begin();
                 inlined_operator_descriptors.end() != i; ++i) {

                CNFOperatorInliner worker { *this, time, group };
                worker(*i);
            }
        }

        /**
         * 3. Pushing ITE MUXes
         */
        {
            const compiler::Expr2BinarySelectionDescriptorsMap& binary_selection_descriptors_map {
                cu.binary_selection_descriptors_map()
            };

            compiler::Expr2BinarySelectionDescriptorsMap::const_iterator mmi {
                binary_selection_descriptors_map.begin()
            };

            while (binary_selection_descriptors_map.end() != mmi) {
                expr::Expr_ptr toplevel { mmi->first };

                const compiler::BinarySelectionDescriptors& descriptors { mmi->second };

                compiler::BinarySelectionDescriptors::const_iterator i;
                for (i = descriptors.begin(); descriptors.end() != i; ++i) {
                    CNFBinarySelectionInliner worker { *this, time, group };
                    worker(*i);
                }

                ++mmi;
            }
        }

        /**
         * 4. Pushing ARRAY MUXes
         */
        {
            const compiler::MultiwaySelectionDescriptors& muxes {
                cu.array_mux_descriptors()
            };
            compiler::MultiwaySelectionDescriptors::const_iterator i;
            for (i = muxes.begin(); muxes.end() != i; ++i) {
                CNFMultiwaySelectionInliner worker { *this, time, group };
                worker(*i);
            }
        }
    }

    Var Engine::find_dd_var(const DdNode* node, step_t time)
    {
        assert(NULL != node && !Cudd_IsConstant(node));
        const enc::UCBI& ucbi { find_ucbi(node->index) };
        const enc::TCBI tcbi { ucbi, time };
        return tcbi_to_var(tcbi);
    }

    Var Engine::find_dd_var(int node_index, step_t time)
    {
        const enc::UCBI& ucbi { find_ucbi(node_index) };
        const enc::TCBI tcbi { ucbi, time };
        return tcbi_to_var(tcbi);
    }

    Var Engine::find_cnf_var(const DdNode* node, step_t time)
    {
        Var res;

        assert(NULL != node);
        TimedDD timed_node { const_cast<DdNode*>(node), time };

        TDD2VarMap::const_iterator eye { f_tdd2var_map.find(timed_node) };
        if (f_tdd2var_map.end() == eye) {
            res = new_sat_var();

            /* Insert into tdd2var map */
            f_tdd2var_map.insert(std::pair<TimedDD, Var>(timed_node, res));

#if 0
            DRIVEL
                << "Created cnf var "
                << res
                << " for DD node "
                << node
                << std::endl;
#endif
        } else {
            res = (*eye).second;
        }
        return res;
    }

    void Engine::clear_cnf_map()
    {
        f_rewrite_map.clear();
    }

    Var Engine::rewrite_cnf_var(Var v, step_t time)
    {
        Var res;

        TimedVar timed_var(v, time);
        RewriteMap::const_iterator eye {
            f_rewrite_map.find(timed_var)
        };

        if (f_rewrite_map.end() == eye) {
            res = new_sat_var();

            /* Insert into tvv2var map */
            f_rewrite_map.insert(std::pair<TimedVar, Var>(timed_var, res));

#if 0
            DRIVEL
                << "Rewrote microcode cnf var "
                << v << "@" << time
                << " as "
                << res
                << std::endl;
#endif
        } else {
            res = (*eye).second;
        }
        return res;
    }

    Var Engine::tcbi_to_var(const enc::TCBI& tcbi)
    {
        Var var;
        const TCBI2VarMap::iterator eye {
            f_tcbi2var_map.find(tcbi)
        };

        if (f_tcbi2var_map.end() != eye) {
            var = eye->second;
        } else {
            /* generate a new var and book it. Newly created var is not eliminable. */
            var = new_sat_var(true);

            f_tcbi2var_map.insert(std::pair<enc::TCBI, Var>(tcbi, var));
            f_var2tcbi_map.insert(std::pair<Var, enc::TCBI>(var, tcbi));
        }

        return var;
    }

    enc::TCBI& Engine::var_to_tcbi(Var var)
    {
        const Var2TCBIMap::iterator eye {
            f_var2tcbi_map.find(var)
        };

        /* TCBI *has* to be there already. */
        assert(f_var2tcbi_map.end() != eye);

        return eye->second;
    }
    
    // -- CNF Optimization Implementation -------------------------------------
    
    void Engine::enable_cnf_optimization(bool enable)
    {
        if (enable && f_mode != Mode::normal)
            throw std::logic_error("CNF optimization is unavailable for recording and proof engines");
        f_cnf_optimization_enabled = enable;
        
        const char* status_str = enable ? "enabled" : "disabled";
        DEBUG
            << "CNF optimization "
            << status_str
            << std::endl;
    }
    
    void Engine::optimize_and_commit()
    {
        if (f_pending_clauses.empty()) {
            return;
        }

        clock_t start_time = clock();
        f_opt_stats.reset();
        f_opt_stats.original_clauses = f_pending_clauses.size();

        if (f_cnf_optimization_enabled) {
            f_optimization_in_progress = true;

            TRACE
                << "Starting CNF optimization with "
                << f_opt_stats.original_clauses
                << " clauses"
                << std::endl;

            // Run optimization pipeline with timing
            optimize_cnf();

            f_opt_stats.final_clauses = f_pending_clauses.size();
            
            size_t removed = f_opt_stats.original_clauses - f_opt_stats.final_clauses;
            double reduction = (removed > 0) ? (100.0 * removed) / f_opt_stats.original_clauses : 0.0;
            
            clock_t opt_time = clock() - start_time;
            double opt_secs = (double)opt_time / CLOCKS_PER_SEC;
            f_opt_stats.total_time_ms = opt_secs * 1000;
            
            INFO
                << "CNF optimization complete: "
                << f_opt_stats.original_clauses << " -> "
                << f_opt_stats.final_clauses << " clauses "
                << "(" << removed
                << " removed, "
                << reduction
                << "% reduction) in "
                << opt_secs << " seconds"
                << std::endl;
            
            DEBUG
                << "  Tautologies: " << f_opt_stats.removed_tautologies
                << " (" << f_opt_stats.tautology_time_ms << "ms)"
                << ", Duplicates: " << f_opt_stats.removed_duplicates
                << " (" << f_opt_stats.duplicate_time_ms << "ms)"
                << ", Subsumed: " << f_opt_stats.removed_subsumed
                << " (" << f_opt_stats.subsumption_time_ms << "ms)"
                << std::endl;
            
            if (f_opt_stats.removed_by_var_elim || f_opt_stats.removed_by_self_subsumption || f_opt_stats.removed_blocked) {
                DEBUG
                    << "  Var elim: " << f_opt_stats.removed_by_var_elim
                    << " (" << f_opt_stats.var_elim_time_ms << "ms)"
                    << ", Self-subsume: " << f_opt_stats.removed_by_self_subsumption
                    << " (" << f_opt_stats.self_subsumption_time_ms << "ms)"
                    << ", Blocked: " << f_opt_stats.removed_blocked
                    << " (" << f_opt_stats.blocked_clause_time_ms << "ms)"
                    << std::endl;
            }
        } else {
            // No optimization, just record stats
            f_opt_stats.final_clauses = f_opt_stats.original_clauses;
        }
        
        // Always commit clauses to solver
        clock_t commit_start = clock();
        for (auto& clause : f_pending_clauses) {
            commit_clause(clause);
        }
        clock_t commit_time = clock() - commit_start;
        double commit_secs = (double)commit_time / CLOCKS_PER_SEC;

        auto pending_clauses {  f_pending_clauses.size() };
        TRACE
            << "Committed "
            << pending_clauses
            << " clauses to solver in " << commit_secs << " seconds"
            << std::endl;
        
        // Clear pending clauses
        f_pending_clauses.clear();
        f_optimization_in_progress = false;
    }
    
    void Engine::optimize_cnf()
    {
        // Run optimization passes in sequence with timing
        opts::OptsMgr& opts_mgr { opts::OptsMgr::INSTANCE() };
        if (opts_mgr.cnf_variable_elimination() || opts_mgr.cnf_blocked_clause() ||
            opts_mgr.cnf_self_subsumption()) {
            throw std::invalid_argument("Unsupported custom CNF transformation.");
        }
        clock_t start;
        
        if (opts_mgr.cnf_tautology_removal()) {
            start = clock();
            remove_tautologies();
            f_opt_stats.tautology_time_ms = ((double)(clock() - start) / CLOCKS_PER_SEC) * 1000;
        }
        
        if (opts_mgr.cnf_duplicate_removal()) {
            start = clock();
            remove_duplicates();
            f_opt_stats.duplicate_time_ms = ((double)(clock() - start) / CLOCKS_PER_SEC) * 1000;
        }
        
        if (opts_mgr.cnf_subsumption()) {
            start = clock();
            subsumption_elimination();
            f_opt_stats.subsumption_time_ms = ((double)(clock() - start) / CLOCKS_PER_SEC) * 1000;
        }
        
        if (opts_mgr.cnf_variable_elimination()) {
            start = clock();
            variable_elimination();
            f_opt_stats.var_elim_time_ms = ((double)(clock() - start) / CLOCKS_PER_SEC) * 1000;
        }
        
        if (opts_mgr.cnf_self_subsumption()) {
            start = clock();
            self_subsuming_resolution();
            f_opt_stats.self_subsumption_time_ms = ((double)(clock() - start) / CLOCKS_PER_SEC) * 1000;
        }
        
        if (opts_mgr.cnf_blocked_clause()) {
            start = clock();
            blocked_clause_elimination();
            f_opt_stats.blocked_clause_time_ms = ((double)(clock() - start) / CLOCKS_PER_SEC) * 1000;
        }
    }
    
    bool Engine::has_tautology(const std::vector<Lit>& clause)
    {
        // Use set instead of unordered_set to avoid hash issues with Lit
        std::set<int> seen;
        for (auto lit : clause) {
            int lit_int = toInt(lit);
            int neg_lit_int = toInt(~lit);
            if (seen.count(neg_lit_int) > 0) {
                return true;
            }
            seen.insert(lit_int);
        }
        return false;
    }
    
    void Engine::remove_tautologies()
    {
        std::vector<std::vector<Lit>> result;
        result.reserve(f_pending_clauses.size());
        
        for (auto& clause : f_pending_clauses) {
            if (!has_tautology(clause)) {
                result.push_back(std::move(clause));
            } else {
                f_opt_stats.removed_tautologies++;
            }
        }
        
        f_pending_clauses = std::move(result);
    }
    
    void Engine::remove_duplicates()
    {
        // First sort literals within each clause
        for (auto& clause : f_pending_clauses) {
            std::sort(clause.begin(), clause.end(),
                [](Lit a, Lit b) { return toInt(a) < toInt(b); });
        }
        
        // Sort clauses for efficient duplicate detection
        std::sort(f_pending_clauses.begin(), f_pending_clauses.end(),
            [](const std::vector<Lit>& a, const std::vector<Lit>& b) {
                if (a.size() != b.size()) return a.size() < b.size();
                for (size_t i = 0; i < a.size(); ++i) {
                    if (toInt(a[i]) != toInt(b[i])) {
                        return toInt(a[i]) < toInt(b[i]);
                    }
                }
                return false;
            });
        
        // Remove duplicates
        std::vector<std::vector<Lit>> result;
        result.reserve(f_pending_clauses.size());
        
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            bool is_duplicate = false;
            
            // Check if this clause is a duplicate of the previous one
            if (!result.empty()) {
                const auto& prev = result.back();
                const auto& curr = f_pending_clauses[i];
                
                if (prev.size() == curr.size()) {
                    is_duplicate = true;
                    for (size_t j = 0; j < prev.size(); ++j) {
                        if (toInt(prev[j]) != toInt(curr[j])) {
                            is_duplicate = false;
                            break;
                        }
                    }
                }
            }
            
            if (!is_duplicate) {
                result.push_back(std::move(f_pending_clauses[i]));
            } else {
                f_opt_stats.removed_duplicates++;
            }
        }
        
        f_pending_clauses = std::move(result);
    }
    
    bool Engine::is_subsumed(const std::vector<Lit>& smaller, const std::vector<Lit>& larger)
    {
        if (smaller.size() > larger.size()) return false;
        
        size_t j = 0;
        for (size_t i = 0; i < smaller.size(); ++i) {
            while (j < larger.size() && toInt(larger[j]) < toInt(smaller[i])) {
                j++;
            }
            if (j >= larger.size() || toInt(larger[j]) != toInt(smaller[i])) {
                return false;
            }
        }
        return true;
    }
    
    void Engine::subsumption_elimination()
    {
        // This pass also works when duplicate removal is disabled.
        for (auto& clause : f_pending_clauses) {
            std::sort(clause.begin(), clause.end(), [](Lit a, Lit b) {
                return toInt(a) < toInt(b);
            });
        }
        std::stable_sort(f_pending_clauses.begin(), f_pending_clauses.end(),
                         [](const auto& a, const auto& b) { return a.size() < b.size(); });
        std::vector<bool> subsumed(f_pending_clauses.size(), false);
        
        // For each clause, check if it's subsumed by any smaller clause
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            query::checkpoint(query::Phase::encoding);
            if (subsumed[i]) continue;
            
            for (size_t j = 0; j < i; ++j) {
                if (subsumed[j]) continue;
                if (f_pending_clauses[j].size() > f_pending_clauses[i].size()) break;
                
                if (is_subsumed(f_pending_clauses[j], f_pending_clauses[i])) {
                    subsumed[i] = true;
                    f_opt_stats.removed_subsumed++;
                    break;
                }
            }
        }
        
        // Collect non-subsumed clauses
        std::vector<std::vector<Lit>> result;
        result.reserve(f_pending_clauses.size());
        
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            if (!subsumed[i]) {
                result.push_back(std::move(f_pending_clauses[i]));
            }
        }
        
        f_pending_clauses = std::move(result);
    }
    
    void Engine::variable_elimination()
    {
        // Variable elimination by resolution
        // For each variable, if eliminating it reduces the clause count, do it
        
        // Count occurrences of each variable
        std::unordered_map<Var, std::vector<size_t>> positive_occurrences;
        std::unordered_map<Var, std::vector<size_t>> negative_occurrences;
        
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            for (auto lit : f_pending_clauses[i]) {
                Var var = sat::var(lit);
                if (sign(lit)) {
                    negative_occurrences[var].push_back(i);
                } else {
                    positive_occurrences[var].push_back(i);
                }
            }
        }
        
        std::vector<bool> clause_removed(f_pending_clauses.size(), false);
        
        // Try to eliminate variables
        for (auto& [var, pos_clauses] : positive_occurrences) {
            auto neg_it = negative_occurrences.find(var);
            if (neg_it == negative_occurrences.end()) continue;
            
            const auto& neg_clauses = neg_it->second;
            
            // Skip if too many resolvents would be created
            if (pos_clauses.size() * neg_clauses.size() > pos_clauses.size() + neg_clauses.size() + 10) {
                continue;
            }
            
            // Check if all resolvents are tautologies or already exist
            bool can_eliminate = true;
            std::vector<std::vector<Lit>> new_clauses;
            
            for (size_t pos_idx : pos_clauses) {
                if (clause_removed[pos_idx]) continue;
                
                for (size_t neg_idx : neg_clauses) {
                    if (clause_removed[neg_idx]) continue;
                    
                    // Create resolvent
                    std::vector<Lit> resolvent;
                    
                    // Add literals from positive clause (except var)
                    for (auto lit : f_pending_clauses[pos_idx]) {
                        if (sat::var(lit) != var) {
                            resolvent.push_back(lit);
                        }
                    }
                    
                    // Add literals from negative clause (except ~var)
                    for (auto lit : f_pending_clauses[neg_idx]) {
                        if (sat::var(lit) != var) {
                            // Check if literal already exists (would create tautology)
                            bool found = false;
                            for (auto existing : resolvent) {
                                if (existing == lit) {
                                    found = true;
                                    break;
                                } else if (existing == ~lit) {
                                    // Tautology - skip this resolvent
                                    goto next_resolvent;
                                }
                            }
                            if (!found) {
                                resolvent.push_back(lit);
                            }
                        }
                    }
                    
                    new_clauses.push_back(std::move(resolvent));
                    next_resolvent:;
                }
            }
            
            // If elimination is beneficial, mark clauses for removal and add resolvents
            if (can_eliminate && new_clauses.size() < pos_clauses.size() + neg_clauses.size()) {
                for (size_t idx : pos_clauses) {
                    if (!clause_removed[idx]) {
                        clause_removed[idx] = true;
                        f_opt_stats.removed_by_var_elim++;
                    }
                }
                for (size_t idx : neg_clauses) {
                    if (!clause_removed[idx]) {
                        clause_removed[idx] = true;
                        f_opt_stats.removed_by_var_elim++;
                    }
                }
                
                // Add resolvents
                for (auto& clause : new_clauses) {
                    f_pending_clauses.push_back(std::move(clause));
                }
            }
        }
        
        // Remove eliminated clauses
        std::vector<std::vector<Lit>> result;
        result.reserve(f_pending_clauses.size());
        
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            if (!clause_removed[i]) {
                result.push_back(std::move(f_pending_clauses[i]));
            }
        }
        
        f_pending_clauses = std::move(result);
    }
    
    void Engine::self_subsuming_resolution()
    {
        // Self-subsuming resolution: if C ∨ l and C ∨ ¬l exist,
        // we can replace C ∨ l with C
        
        std::vector<bool> modified(f_pending_clauses.size(), false);
        
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            if (modified[i]) continue;
            
            for (size_t j = i + 1; j < f_pending_clauses.size(); ++j) {
                if (modified[j]) continue;
                
                // Check if clauses differ by exactly one literal
                const auto& clause1 = f_pending_clauses[i];
                const auto& clause2 = f_pending_clauses[j];
                
                if (std::abs((int)clause1.size() - (int)clause2.size()) > 1) continue;
                
                // Find the differing literal
                Lit diff_lit1 = mkLit(0);
                Lit diff_lit2 = mkLit(0);
                bool found_diff = false;
                
                size_t p1 = 0, p2 = 0;
                while (p1 < clause1.size() && p2 < clause2.size()) {
                    if (toInt(clause1[p1]) == toInt(clause2[p2])) {
                        p1++;
                        p2++;
                    } else if (toInt(clause1[p1]) < toInt(clause2[p2])) {
                        if (found_diff) goto next_pair;
                        diff_lit1 = clause1[p1];
                        found_diff = true;
                        p1++;
                    } else {
                        if (found_diff) goto next_pair;
                        diff_lit2 = clause2[p2];
                        found_diff = true;
                        p2++;
                    }
                }
                
                // Handle remaining literals
                if (p1 < clause1.size()) {
                    if (found_diff) goto next_pair;
                    diff_lit1 = clause1[p1];
                    found_diff = true;
                }
                if (p2 < clause2.size()) {
                    if (found_diff) goto next_pair;
                    diff_lit2 = clause2[p2];
                    found_diff = true;
                }
                
                // Check if we have complementary literals
                if (found_diff && diff_lit1 == ~diff_lit2) {
                    // Perform self-subsuming resolution
                    if (clause1.size() > clause2.size()) {
                        // Remove diff_lit1 from clause1
                        auto& clause = f_pending_clauses[i];
                        clause.erase(std::remove(clause.begin(), clause.end(), diff_lit1), clause.end());
                        modified[i] = true;
                        f_opt_stats.removed_by_self_subsumption++;
                    } else {
                        // Remove diff_lit2 from clause2
                        auto& clause = f_pending_clauses[j];
                        clause.erase(std::remove(clause.begin(), clause.end(), diff_lit2), clause.end());
                        modified[j] = true;
                        f_opt_stats.removed_by_self_subsumption++;
                    }
                }
                
                next_pair:;
            }
        }
    }
    
    void Engine::blocked_clause_elimination()
    {
        // Blocked clause elimination: A clause C is blocked if 
        // for some literal l in C, all resolutions on l produce tautologies
        
        std::vector<bool> blocked(f_pending_clauses.size(), false);
        
        // Build occurrence lists
        std::unordered_map<int, std::vector<size_t>> lit_to_clauses;
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            for (auto lit : f_pending_clauses[i]) {
                lit_to_clauses[toInt(lit)].push_back(i);
            }
        }
        
        // Check each clause
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            if (blocked[i]) continue;
            
            // Try each literal in the clause
            bool is_blocked = false;
            for (auto lit : f_pending_clauses[i]) {
                bool all_resolvents_tautological = true;
                
                // Get clauses containing ~lit
                auto neg_it = lit_to_clauses.find(toInt(~lit));
                if (neg_it == lit_to_clauses.end()) {
                    // No clauses with ~lit, so this literal makes the clause blocked
                    is_blocked = true;
                    break;
                }
                
                // Check all possible resolvents
                for (size_t j : neg_it->second) {
                    if (i == j || blocked[j]) continue;
                    
                    // Check if resolvent would be tautological
                    bool tautological = false;
                    for (auto lit1 : f_pending_clauses[i]) {
                        if (lit1 == lit) continue; // Skip the resolved literal
                        
                        for (auto lit2 : f_pending_clauses[j]) {
                            if (lit2 == ~lit) continue; // Skip the resolved literal
                            
                            if (lit1 == ~lit2) {
                                tautological = true;
                                goto next_resolvent;
                            }
                        }
                    }
                    
                    if (!tautological) {
                        all_resolvents_tautological = false;
                        break;
                    }
                    
                    next_resolvent:;
                }
                
                if (all_resolvents_tautological) {
                    is_blocked = true;
                    break;
                }
            }
            
            if (is_blocked) {
                blocked[i] = true;
                f_opt_stats.removed_blocked++;
            }
        }
        
        // Remove blocked clauses
        std::vector<std::vector<Lit>> result;
        result.reserve(f_pending_clauses.size());
        
        for (size_t i = 0; i < f_pending_clauses.size(); ++i) {
            if (!blocked[i]) {
                result.push_back(std::move(f_pending_clauses[i]));
            }
        }
        
        f_pending_clauses = std::move(result);
    }

}; // namespace sat
