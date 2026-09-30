#include <sat/interpolation_diagnostics.hh>
#include <cstdlib>
#include <iomanip>
#include <sstream>
#include <stdexcept>
#include <sys/resource.h>
#include <unistd.h>
#ifdef __GLIBC__
#include <malloc.h>
#endif

namespace sat::diagnostics {
namespace {
thread_local Run* active = nullptr;
thread_local uint64_t sequence = 0;
struct Config {
    std::filesystem::path directory;
    std::ofstream log;
    std::string selection;
    int64_t images = -1;
    std::chrono::steady_clock::time_point started = std::chrono::steady_clock::now();
    Config() {
        if (const char* p = std::getenv("YASMV_IMC_DIAGNOSTICS")) {
            if (!*p) throw std::invalid_argument("Empty interpolation diagnostics directory");
            directory = p;
            std::filesystem::create_directories(directory);
            if (std::filesystem::exists(directory / "telemetry.jsonl"))
                throw std::invalid_argument("Interpolation telemetry already exists");
            log.exceptions(std::ios::badbit | std::ios::failbit);
            log.open(directory / "telemetry.jsonl");
            if (const char* s = std::getenv("YASMV_IMC_CAPTURE")) selection = s;
            if (const char* s = std::getenv("YASMV_IMC_IMAGES")) {
                std::string value(s); size_t used = 0;
                images = std::stoll(value, &used);
                if (used != value.size() || images < 1) throw std::invalid_argument("Invalid diagnostic image limit");
            }
            if (!selection.empty() && selection != "all") {
                std::istringstream in(selection); std::string token;
                while (std::getline(in, token, ',')) {
                    size_t used = 0; std::stoull(token, &used);
                    if (used != token.size() || token.front() == '-') throw std::invalid_argument("Invalid capture selection");
                }
                if (selection.back() == ',') throw std::invalid_argument("Invalid capture selection");
            }
        } else if (std::getenv("YASMV_IMC_CAPTURE") || std::getenv("YASMV_IMC_IMAGES")) {
            throw std::invalid_argument("Capture and image limits require YASMV_IMC_DIAGNOSTICS");
        }
    }
    bool selected(uint64_t id) const {
        if (selection == "all") return true;
        std::istringstream in(selection); std::string token;
        while (std::getline(in, token, ',')) if (std::stoull(token) == id) return true;
        return false;
    }
};
Config& config() { static thread_local Config value; return value; }
void clause(std::ostream& out, const proof::Clause& c) {
    for (int lit : c) out << ' ' << lit;
    out << " 0";
}
}
Run* current() { return active; }
int64_t image_limit() { return config().images; }
bool enabled() { return !config().directory.empty(); }
void sample(const std::string& phase, Fields fields) {
    auto& cfg = config();
    if (cfg.directory.empty()) return;
    fields["elapsed_ms"] = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now()-cfg.started).count();
    long pages = 0, resident = 0;
    std::ifstream stat("/proc/self/statm");
    if (stat >> pages >> resident) fields["rss_bytes"] = uint64_t(resident) * sysconf(_SC_PAGESIZE);
    rusage usage{};
    if (!getrusage(RUSAGE_SELF, &usage)) fields["peak_rss_bytes"] = uint64_t(usage.ru_maxrss)*1024;
#ifdef __GLIBC__
    const auto heap = mallinfo2();
    fields["allocator_inuse_bytes"] = heap.uordblks;
    fields["allocator_free_arena_bytes"] = heap.fordblks;
    fields["allocator_mmap_bytes"] = heap.hblkhd;
#endif
    cfg.log << "{\"phase\":" << std::quoted(phase);
    for (const auto& [key, value] : fields) cfg.log << ',' << std::quoted(key) << ':' << value;
    cfg.log << "}\n";
    cfg.log.flush();
}
Fields proof_memory(const proof::ResolutionProof& p) {
    const auto m = p.memory();
    return {{"proof_nodes",m.nodes},{"proof_node_capacity",m.node_capacity},{"proof_literals",m.literals},
        {"proof_literal_capacity",m.literal_capacity},{"proof_active_ids",m.active_ids},{"proof_archived_ids",m.archived_ids},
        {"proof_node_bytes",m.node_bytes},{"proof_literal_bytes",m.literal_bytes},{"proof_id_payload_bytes",m.id_payload_bytes},
        {"proof_clause_slot_bytes",m.clause_slot_bytes},{"proof_expanded_literals",m.expanded_literals},
        {"proof_temporary_literal_bytes_peak",m.temporary_literal_bytes_peak},
        {"proof_original_clauses",m.original.clauses},{"proof_original_literals",m.original.literals},
        {"proof_original_literal_bytes",m.original.capacity*sizeof(int)},
        {"proof_derived_clauses",m.derived.clauses},{"proof_derived_literals",m.derived.literals},
        {"proof_derived_literal_bytes",m.derived.capacity*sizeof(int)}};
}
Fields circuit_memory(const Circuit& c, Circuit::Ref root) {
    return {{"circuit_allocated_nodes",c.size()},{"circuit_reachable_nodes",c.reachable_size(root)},
            {"circuit_payload_bytes",c.storage_payload_bytes()}};
}
Run::Run() : previous_(active), id_(sequence++), last_(std::chrono::steady_clock::now()) {
    auto& cfg = config();
    if (!cfg.directory.empty() && cfg.selected(id_)) {
        std::ostringstream name; name << "query-" << std::setw(6) << std::setfill('0') << id_;
        directory_ = cfg.directory / name.str();
        if (!std::filesystem::create_directory(directory_)) throw std::runtime_error("Capture directory already exists");
        events_.exceptions(std::ios::badbit | std::ios::failbit);
        input_.exceptions(std::ios::badbit | std::ios::failbit);
        events_.open(directory_ / "proof.events"); input_.open(directory_ / "input.cnf");
        events_ << "yasmv-proof-events 1\n";
        input_ << "yasmv-partitioned-cnf 1\n";
    }
    phase("query_begin");
    active = this;
}
Run::~Run() {
    // Logging errors during stack unwinding must not replace the original error.
    try { phase("query_temporaries_destroyed"); } catch (...) {}
    active = previous_;
}
void Run::original(proof::Id id, const proof::Clause& c, proof::Partition partition) {
    if (directory_.empty()) return;
    const char side = partition == proof::Partition::a ? 'a' : 'b';
    input_ << side << ' ' << id; clause(input_, c); input_ << '\n';
    events_ << "o " << side << ' ' << id; clause(events_, c); events_ << '\n';
}
void Run::event(char kind, proof::Id id, const proof::Clause& c, const std::vector<proof::Id>& hints, int witness) {
    if (directory_.empty()) return;
    events_ << kind << ' ' << id;
    if (kind == 'd') events_ << ' ' << witness;
    if (kind != 'u') clause(events_, c);
    if (kind == 'd') { for (auto hint : hints) events_ << ' ' << hint; events_ << " 0"; }
    events_ << '\n';
}
void Run::phase(const std::string& name, const proof::ResolutionProof* proof, const Circuit* circuit, Circuit::Ref root) {
    if (config().directory.empty()) return;
    auto fields = proof ? proof_memory(*proof) : Fields{};
    if (circuit) fields.merge(circuit_memory(*circuit,root));
    fields["query_index"] = id_;
    sample(name, std::move(fields));
    if (!directory_.empty()) { events_.flush(); input_.flush(); }
}
void Run::counters(const std::string& name, Fields fields) {
    fields["query_index"] = id_;
    sample(name, std::move(fields));
}
void Run::progress(const proof::ResolutionProof& p, const Circuit* c) {
    const auto now = std::chrono::steady_clock::now();
    if (now-last_ < std::chrono::seconds(1)) return;
    last_ = now;
    if (!c) phase("proof_progress", &p);
    else {
        auto fields = proof_memory(p);
        fields["query_index"] = id_;
        fields["circuit_allocated_nodes"] = c->size();
        fields["circuit_payload_bytes"] = c->storage_payload_bytes();
        sample("interpolant_progress", std::move(fields));
    }
}
void Run::complete(bool verified) {
    phase(verified ? "query_verified" : "query_not_verified");
    if (!directory_.empty()) {
        std::ofstream out(directory_ / "complete");
        out.exceptions(std::ios::badbit | std::ios::failbit);
        out << (verified ? "verified-unsat\n" : "not-verified\n");
    }
}
} // namespace sat::diagnostics
