#include <query/runtime.hh>
#include <sat/engine.hh>
namespace query {
    volatile sig_atomic_t signal_pending = 0;
    void signal_handler(int)
    {
        signal_pending = 1;
    }
    static std::atomic<QueryContext*> active { nullptr };
    static std::recursive_mutex execution_mutex;
    QueryContext* current()
    {
        return active.load();
    }
    const char* name(StopReason value)
    {
        switch (value) {
#define CASE(x)         \
    case StopReason::x: \
        return #x
            CASE(none);
            CASE(depth_limit);
            CASE(state_limit);
            CASE(deadline);
            CASE(conflict_budget);
            CASE(propagation_budget);
            CASE(cancelled);
            CASE(validation_error);
            CASE(internal_error);
            CASE(solver_unknown);
#undef CASE
        }
        return "internal_error";
    }
    QueryContext::QueryContext(QueryLimits value)
        : limits(value)
    {
        timer = std::thread([this] {
            const auto start = std::chrono::steady_clock::now();
            std::unique_lock<std::mutex> lock(mutex);
            while (!finished) {
                cv.wait_for(lock, std::chrono::milliseconds(5));
                if (finished) break;
                StopReason reason = StopReason::none;
                if (signal_pending && current() == this) {
                    signal_pending = 0;
                    reason = StopReason::cancelled;
                }
                if (limits.wall_ms >= 0 && std::chrono::steady_clock::now() - start >= std::chrono::milliseconds(limits.wall_ms)) reason = StopReason::deadline;
                if (reason != StopReason::none) {
                    auto expected = StopReason::none;
                    stop.compare_exchange_strong(expected, reason);
                }
                if (stop != StopReason::none)
                    for (auto engine : engines)
                        engine->interrupt();
            }
        });
    }
    QueryContext::~QueryContext()
    {
        {
            std::lock_guard<std::mutex> lock(mutex);
            finished = true;
        }
        cv.notify_all();
        timer.join();
    }
    void QueryContext::cancel(StopReason reason)
    {
        auto expected = StopReason::none;
        stop.compare_exchange_strong(expected, reason);
        std::lock_guard<std::mutex> lock(mutex);
        for (auto engine : engines)
            engine->interrupt();
    }
    void QueryContext::check(Phase value)
    {
        phase = value;
        if (limits.wall_ms >= 0 && std::chrono::steady_clock::now() - started >= std::chrono::milliseconds(limits.wall_ms)) cancel(StopReason::deadline);
        if (checkpoint_hook) checkpoint_hook(value);
        if (signal_pending && current() == this) {
            signal_pending = 0;
            cancel();
        }
        if (stop != StopReason::none) throw Cancelled();
    }
    void QueryContext::attach(sat::Engine* e)
    {
        std::lock_guard<std::mutex> lock(mutex);
        engines.insert(e);
    }
    void QueryContext::detach(sat::Engine* e)
    {
        std::lock_guard<std::mutex> lock(mutex);
        engines.erase(e);
    }
    ContextScope::ContextScope(QueryContext& c)
        : lock(execution_mutex)
        , previous(active.exchange(&c))
    {}
    ContextScope::~ContextScope()
    {
        active = previous;
    }
    void checkpoint(Phase p)
    {
        if (auto c = current()) c->check(p);
    }
    PhaseTimer::PhaseTimer(Phase p)
        : phase(p)
        , context(current())
        , start(std::chrono::steady_clock::now())
    {
        checkpoint(p);
    }
    PhaseTimer::~PhaseTimer()
    {
        if (!context) return;
        double ms = std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - start).count();
        switch (phase) {
            case Phase::compilation:
                context->compile_ms += ms;
                break;
            case Phase::encoding:
                context->encode_ms += ms;
                break;
            case Phase::solving:
                context->solve_ms += ms;
                break;
            case Phase::decoding:
                context->decode_ms += ms;
                break;
            default:
                break;
        }
    }
} // namespace query
