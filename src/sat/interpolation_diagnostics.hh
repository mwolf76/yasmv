#ifndef YASMV_INTERPOLATION_DIAGNOSTICS_HH
#define YASMV_INTERPOLATION_DIAGNOSTICS_HH

#include <sat/proof.hh>
#include <sat/circuit.hh>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <map>
#include <string>

namespace sat::diagnostics {
using Fields = std::map<std::string, uint64_t>;
// Opt-in experiment instrumentation. Payload sizes exclude allocator/tree-node
// overhead; RSS and glibc allocator measurements are reported independently.
void sample(const std::string& phase, Fields fields = {});
Fields proof_memory(const proof::ResolutionProof&);
Fields circuit_memory(const Circuit&, Circuit::Ref);
int64_t image_limit();
bool enabled();
class Run {
public:
    Run();
    ~Run();
    Run(const Run&) = delete;
    Run& operator=(const Run&) = delete;
    const std::filesystem::path& directory() const { return directory_; }
    void original(proof::Id, const proof::Clause&, proof::Partition);
    void event(char, proof::Id, const proof::Clause& = {}, const std::vector<proof::Id>& = {}, int witness = 0);
    void progress(const proof::ResolutionProof&, const Circuit* = nullptr);
    void phase(const std::string&, const proof::ResolutionProof* = nullptr,
               const Circuit* = nullptr, Circuit::Ref = Circuit::False);
    void counters(const std::string&, Fields);
    void complete(bool verified);
private:
    Run* previous_;
    uint64_t id_;
    std::filesystem::path directory_;
    std::ofstream events_, input_;
    std::chrono::steady_clock::time_point last_;
};
Run* current();
} // namespace sat::diagnostics
#endif
