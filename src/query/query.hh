#ifndef YASMV_QUERY_HH
#define YASMV_QUERY_HH
#include <query/runtime.hh>
#include <query/source.hh>
#include <witness/witness.hh>
namespace query {
    enum class Operation { check_init,
                           check_trans,
                           pick_state,
                           reach,
                           simulate,
                           diameter,
                           validate_trace };
    enum class ExecutionStatus { completed,
                                 unknown,
                                 error };
    enum class Outcome { none,
                         satisfiable,
                         unsatisfiable,
                         reachable,
                         unreachable,
                         simulated,
                         deadlocked,
                         diameter,
                         valid,
                         invalid };
    struct QuerySpec {
        Operation operation = Operation::check_init;
        std::string request_id, strategy = "auto";
        expr::Expr_ptr target = nullptr, until = nullptr;
        expr::ExprVector assumptions;
        QueryLimits limits;
        bool enumerate = false, count = false;
        std::string trace_id;
        Json::Value trace, parent_trace;
    };
    struct QueryResult {
        std::string request_id;
        ExecutionStatus status = ExecutionStatus::unknown;
        Outcome outcome = Outcome::none;
        StopReason reason = StopReason::none;
        std::string scope = "exact_depth", strategy, proof_method;
        bool complete = false;
        int64_t value = 0;
        std::vector<unsigned> checked_depths;
        witness::Witness_ptr witness = nullptr;
        Json::Value identity, trace, statistics;
        std::vector<source::Diagnostic> diagnostics;
        int exit_code() const;
        Json::Value json() const;
    };
    QueryResult execute(const QuerySpec&, QueryContext&);
    QueryResult execute(const QuerySpec&);
    QueryResult checked(const QuerySpec&);
    Json::Value identity();
    Json::Value spec_json(const QuerySpec&);
    QuerySpec spec_from_json(const Json::Value&);
    int run_file(const std::string&);
} // namespace query
#endif
