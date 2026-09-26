#ifndef YASMV_QUERY_RUNTIME_HH
#define YASMV_QUERY_RUNTIME_HH
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <csignal>
#include <cstdint>
#include <functional>
#include <mutex>
#include <set>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>
namespace sat {
    class Engine;
}
namespace query {
    enum class StopReason { none,
                            depth_limit,
                            state_limit,
                            deadline,
                            conflict_budget,
                            propagation_budget,
                            cancelled,
                            validation_error,
                            internal_error,
                            solver_unknown };
    enum class Phase { loading,
                       compilation,
                       encoding,
                       solving,
                       decoding };
    const char* name(StopReason);
    struct QueryLimits {
        int64_t depth = -1, states = -1, wall_ms = -1, conflicts = -1, propagations = -1;
    };
    struct Cancelled: std::runtime_error {
        Cancelled()
            : std::runtime_error("Query interrupted")
        {}
    };
    extern volatile sig_atomic_t signal_pending;
    void signal_handler(int);
    class QueryContext {
    public:
        explicit QueryContext(QueryLimits limits = {});
        ~QueryContext();
        QueryContext(const QueryContext&) = delete;
        QueryContext& operator=(const QueryContext&) = delete;
        void cancel(StopReason reason = StopReason::cancelled);
        void check(Phase);
        void attach(sat::Engine*);
        void detach(sat::Engine*);
        QueryLimits limits;
        std::string requested_strategy = "auto", selected_strategy;
        std::vector<unsigned> checked_depths;
        std::atomic<StopReason> stop { StopReason::none };
        std::atomic<Phase> phase { Phase::loading };
        uint64_t conflicts_used = 0, propagations_used = 0;
        uint64_t variables = 0, clauses = 0;
        double compile_ms = 0, encode_ms = 0, solve_ms = 0, decode_ms = 0;
        // Deterministic cancellation at actual work boundaries, also useful to embedders.
        std::function<void(Phase)> checkpoint_hook;

    private:
        std::chrono::steady_clock::time_point started = std::chrono::steady_clock::now();
        std::mutex mutex;
        std::condition_variable cv;
        bool finished = false;
        std::set<sat::Engine*> engines;
        std::thread timer;
    };
    QueryContext* current();
    class ContextScope {
    public:
        explicit ContextScope(QueryContext&);
        ~ContextScope();

    private:
        std::unique_lock<std::recursive_mutex> lock;
        QueryContext* previous;
    };
    void checkpoint(Phase);
    class PhaseTimer {
    public:
        explicit PhaseTimer(Phase phase);
        ~PhaseTimer();

    private:
        Phase phase;
        QueryContext* context;
        std::chrono::steady_clock::time_point start;
    };
} // namespace query
#endif
