/**
 * @file ucodeopt.cc
 * @brief High-performance CNF optimizer for yasmv microcode files
 *
 * This tool optimizes CNF formulas in microcode JSON files using
 * yasmv's literal encoding (even=positive, odd=negative).
 *
 * Copyright (C) 2025 Marco Pensallorto
 */

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <memory>
#include <mutex>
#include <set>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <jsoncpp/json/json.h>

namespace fs = std::filesystem;

// Type aliases for clarity
using Literal = int32_t;
using Clause = std::vector<Literal>;
using CNF = std::vector<Clause>;

// Configuration
struct Config {
    fs::path input_path;
    fs::path output_path;
    std::string mode = "safe";  // "basic" or "safe"
    bool two_stage = false;
    bool dry_run = false;
    bool verbose = false;
    int num_workers = 0;  // 0 = auto-detect
};

// Statistics tracking
struct Stats {
    size_t original_clauses = 0;
    size_t removed_tautologies = 0;
    size_t removed_duplicates = 0;
    size_t removed_subsumed = 0;
    size_t strengthened = 0;
    size_t final_clauses = 0;
    
    double reduction_percent() const {
        if (original_clauses == 0) return 0.0;
        return 100.0 * (1.0 - static_cast<double>(final_clauses) / original_clauses);
    }
    
    void print() const {
        std::cout << "  Original clauses:    " << original_clauses << "\n";
        std::cout << "  Removed tautologies: " << removed_tautologies << "\n";
        std::cout << "  Removed duplicates:  " << removed_duplicates << "\n";
        std::cout << "  Removed subsumed:    " << removed_subsumed << "\n";
        std::cout << "  Strengthened:        " << strengthened << "\n";
        std::cout << "  Final clauses:       " << final_clauses << "\n";
        std::cout << "  Size reduction:      " << std::fixed << std::setprecision(1) 
                  << reduction_percent() << "%\n";
    }
};

// Fast clause comparison for sorting and uniqueness
struct ClauseCompare {
    bool operator()(const Clause& a, const Clause& b) const {
        if (a.size() != b.size()) return a.size() < b.size();
        return a < b;  // lexicographic comparison
    }
};

// Fast clause hashing for unordered containers
struct ClauseHash {
    size_t operator()(const Clause& clause) const {
        size_t hash = clause.size();
        for (auto lit : clause) {
            hash ^= std::hash<Literal>{}(lit) + 0x9e3779b9 + (hash << 6) + (hash >> 2);
        }
        return hash;
    }
};

class CNFMinimizer {
private:
    const std::string mode_;
    Stats stats_;
    
    // Yasmv literal encoding helpers
    static inline Literal negate_literal(Literal lit) {
        return (lit % 2 == 0) ? lit + 1 : lit - 1;
    }
    
    static inline bool are_complementary(Literal lit1, Literal lit2) {
        return std::abs(lit1 - lit2) == 1 && std::min(lit1, lit2) % 2 == 0;
    }
    
    static inline int get_variable(Literal lit) {
        return lit / 2;
    }
    
    // Check if clause contains complementary literals
    bool has_tautology(const Clause& clause) {
        std::unordered_set<Literal> seen;
        for (auto lit : clause) {
            if (seen.count(negate_literal(lit)) > 0) {
                return true;
            }
            seen.insert(lit);
        }
        return false;
    }
    
    // Remove tautological clauses
    CNF remove_tautologies(const CNF& cnf) {
        CNF result;
        result.reserve(cnf.size());
        
        for (const auto& clause : cnf) {
            if (!has_tautology(clause)) {
                result.push_back(clause);
            } else {
                stats_.removed_tautologies++;
            }
        }
        
        return result;
    }
    
    // Remove duplicate clauses
    CNF remove_duplicates(CNF cnf) {
        // Sort clauses for efficient duplicate detection
        for (auto& clause : cnf) {
            std::sort(clause.begin(), clause.end());
        }
        
        // Use set to track unique clauses
        std::set<Clause, ClauseCompare> unique_set;
        size_t original_size = cnf.size();
        
        CNF result;
        result.reserve(cnf.size());
        
        for (auto& clause : cnf) {
            if (unique_set.insert(clause).second) {
                result.push_back(std::move(clause));
            }
        }
        
        stats_.removed_duplicates = original_size - result.size();
        return result;
    }
    
    // Optimized subsumption using signature filtering
    using Signature = uint64_t;
    
    static Signature compute_signature(const Clause& clause) {
        Signature sig = 0;
        for (auto lit : clause) {
            // Use multiple hash positions to reduce false positives
            sig |= (1ULL << (std::hash<Literal>{}(lit) % 63));
            sig |= (1ULL << (std::hash<Literal>{}(lit * 31 + 17) % 63));
        }
        return sig;
    }
    
    static bool can_subsume_sig(Signature sig1, Signature sig2) {
        // If sig1 subsumes sig2, then (sig1 & sig2) == sig1
        return (sig1 & sig2) == sig1;
    }
    
    static bool fast_includes(const Clause& larger, const Clause& smaller) {
        if (smaller.size() > larger.size()) return false;
        
        auto it_large = larger.begin();
        auto it_small = smaller.begin();
        
        while (it_small != smaller.end() && it_large != larger.end()) {
            if (*it_small == *it_large) {
                ++it_small;
                ++it_large;
            } else if (*it_small < *it_large) {
                return false;
            } else {
                ++it_large;
            }
        }
        
        return it_small == smaller.end();
    }
    
    // Ultra-fast subsumption elimination with adaptive strategy
    CNF subsumption_elimination(CNF cnf) {
        if (cnf.size() <= 1) return cnf;
        
        size_t original_size = cnf.size();
        
        // Choose strategy based on CNF size
        if (cnf.size() < 100) {
            // Small CNFs: Use simple O(n²) with early termination
            cnf = simple_subsumption(std::move(cnf));
        } else if (cnf.size() < 1000) {
            // Medium CNFs: Use signature filtering
            cnf = signature_subsumption(std::move(cnf));
        } else {
            // Large CNFs: Use hash-indexed approach
            cnf = hash_indexed_subsumption(std::move(cnf));
        }
        
        stats_.removed_subsumed = original_size - cnf.size();
        return cnf;
    }

private:
    // Simple subsumption for small CNFs
    CNF simple_subsumption(CNF cnf) {
        // Sort clauses internally
        for (auto& clause : cnf) {
            std::sort(clause.begin(), clause.end());
        }
        
        // Sort by size
        std::sort(cnf.begin(), cnf.end(),
                  [](const Clause& a, const Clause& b) {
                      return a.size() < b.size();
                  });
        
        CNF result;
        result.reserve(cnf.size());
        
        for (size_t i = 0; i < cnf.size(); ++i) {
            bool is_subsumed = false;
            
            // Check against smaller clauses
            for (size_t j = 0; j < result.size(); ++j) {
                if (result[j].size() > cnf[i].size()) break;
                
                if (fast_includes(cnf[i], result[j])) {
                    is_subsumed = true;
                    break;
                }
            }
            
            if (!is_subsumed) {
                result.push_back(std::move(cnf[i]));
            }
        }
        
        return result;
    }
    
    // Signature-based subsumption for medium CNFs
    CNF signature_subsumption(CNF cnf) {
        // Sort clauses internally
        for (auto& clause : cnf) {
            std::sort(clause.begin(), clause.end());
        }
        
        // Create clause-signature pairs
        std::vector<std::pair<Clause, Signature>> clause_sigs;
        clause_sigs.reserve(cnf.size());
        
        for (auto& clause : cnf) {
            auto sig = compute_signature(clause);
            clause_sigs.emplace_back(std::move(clause), sig);
        }
        
        // Sort by size
        std::sort(clause_sigs.begin(), clause_sigs.end(),
                  [](const auto& a, const auto& b) {
                      return a.first.size() < b.first.size();
                  });
        
        std::vector<bool> subsumed(clause_sigs.size(), false);
        
        // Process in batches to improve cache locality
        const size_t batch_size = 64;
        for (size_t batch_start = 0; batch_start < clause_sigs.size(); batch_start += batch_size) {
            size_t batch_end = std::min(batch_start + batch_size, clause_sigs.size());
            
            for (size_t i = batch_start; i < batch_end; ++i) {
                if (subsumed[i]) continue;
                
                const auto& clause_i = clause_sigs[i].first;
                const auto& sig_i = clause_sigs[i].second;
                
                // Check against all later clauses
                for (size_t j = i + 1; j < clause_sigs.size(); ++j) {
                    if (subsumed[j]) continue;
                    
                    const auto& clause_j = clause_sigs[j].first;
                    const auto& sig_j = clause_sigs[j].second;
                    
                    if (clause_i.size() > clause_j.size()) break;
                    
                    if (can_subsume_sig(sig_i, sig_j) && fast_includes(clause_j, clause_i)) {
                        subsumed[j] = true;
                    }
                }
            }
        }
        
        // Collect result
        CNF result;
        result.reserve(clause_sigs.size());
        
        for (size_t i = 0; i < clause_sigs.size(); ++i) {
            if (!subsumed[i]) {
                result.push_back(std::move(clause_sigs[i].first));
            }
        }
        
        return result;
    }
    
    // Hash-indexed subsumption for large CNFs
    CNF hash_indexed_subsumption(CNF cnf) {
        // Sort clauses internally
        for (auto& clause : cnf) {
            std::sort(clause.begin(), clause.end());
        }
        
        // Group by first literal for faster lookups
        std::unordered_map<Literal, std::vector<size_t>> first_lit_groups;
        for (size_t i = 0; i < cnf.size(); ++i) {
            if (!cnf[i].empty()) {
                first_lit_groups[cnf[i][0]].push_back(i);
            }
        }
        
        // Sort each group by size
        for (auto& pair : first_lit_groups) {
            auto& indices = pair.second;
            std::sort(indices.begin(), indices.end(),
                      [&cnf](size_t a, size_t b) {
                          return cnf[a].size() < cnf[b].size();
                      });
        }
        
        std::vector<bool> subsumed(cnf.size(), false);
        
        // Process each group
        for (const auto& [lit, indices] : first_lit_groups) {
            for (size_t i = 0; i < indices.size(); ++i) {
                size_t idx_i = indices[i];
                if (subsumed[idx_i]) continue;
                
                // Check within same group
                for (size_t j = i + 1; j < indices.size(); ++j) {
                    size_t idx_j = indices[j];
                    if (subsumed[idx_j]) continue;
                    
                    if (cnf[idx_i].size() > cnf[idx_j].size()) break;
                    
                    if (fast_includes(cnf[idx_j], cnf[idx_i])) {
                        subsumed[idx_j] = true;
                    }
                }
            }
        }
        
        // Collect result
        CNF result;
        result.reserve(cnf.size());
        
        for (size_t i = 0; i < cnf.size(); ++i) {
            if (!subsumed[i]) {
                result.push_back(std::move(cnf[i]));
            }
        }
        
        return result;
    }
    
    // Forward subsumption (safe mode only)
    CNF forward_subsumption(const CNF& cnf) {
        std::vector<Clause> new_clauses;
        
        // Try to create strengthened clauses via resolution
        for (size_t i = 0; i < cnf.size(); ++i) {
            for (size_t j = i + 1; j < cnf.size(); ++j) {
                const auto& c1 = cnf[i];
                const auto& c2 = cnf[j];
                
                // Find complementary literals
                Literal comp_lit1 = 0, comp_lit2 = 0;
                int comp_count = 0;
                
                for (auto lit1 : c1) {
                    auto neg_lit1 = negate_literal(lit1);
                    if (std::binary_search(c2.begin(), c2.end(), neg_lit1)) {
                        comp_lit1 = lit1;
                        comp_lit2 = neg_lit1;
                        comp_count++;
                        if (comp_count > 1) break;
                    }
                }
                
                // Exactly one complementary pair found
                if (comp_count == 1) {
                    // Create resolvent
                    Clause resolvent;
                    resolvent.reserve(c1.size() + c2.size() - 2);
                    
                    // Add literals from c1 except comp_lit1
                    for (auto lit : c1) {
                        if (lit != comp_lit1) {
                            resolvent.push_back(lit);
                        }
                    }
                    
                    // Add literals from c2 except comp_lit2
                    for (auto lit : c2) {
                        if (lit != comp_lit2 && 
                            std::find(resolvent.begin(), resolvent.end(), lit) == resolvent.end()) {
                            resolvent.push_back(lit);
                        }
                    }
                    
                    // Sort for consistency
                    std::sort(resolvent.begin(), resolvent.end());
                    
                    // Check if not tautological
                    if (!has_tautology(resolvent)) {
                        new_clauses.push_back(std::move(resolvent));
                        stats_.strengthened++;
                    }
                }
            }
        }
        
        if (!new_clauses.empty()) {
            // Combine with original clauses
            CNF combined = cnf;
            combined.insert(combined.end(), new_clauses.begin(), new_clauses.end());
            
            // Re-apply subsumption elimination
            return subsumption_elimination(std::move(combined));
        }
        
        return cnf;
    }
    
public:
    explicit CNFMinimizer(const std::string& mode) : mode_(mode) {}
    
    CNF minimize(CNF cnf) {
        stats_.original_clauses = cnf.size();
        
        // Always apply these transformations
        cnf = remove_tautologies(cnf);
        cnf = remove_duplicates(std::move(cnf));
        cnf = subsumption_elimination(std::move(cnf));
        
        // Safe mode: apply forward subsumption
        if (mode_ == "safe") {
            cnf = forward_subsumption(cnf);
        }
        
        stats_.final_clauses = cnf.size();
        return cnf;
    }
    
    const Stats& get_stats() const { return stats_; }
};

// JSON I/O functions
bool read_json_cnf(const fs::path& path, Json::Value& root, CNF& cnf) {
    std::ifstream file(path);
    if (!file.is_open()) {
        std::cerr << "Error: Cannot open file " << path << "\n";
        return false;
    }
    
    Json::CharReaderBuilder builder;
    std::string errors;
    
    if (!Json::parseFromStream(builder, file, &root, &errors)) {
        std::cerr << "Error: JSON parsing failed: " << errors << "\n";
        return false;
    }
    
    if (!root.isMember("cnf") || !root["cnf"].isArray()) {
        std::cerr << "Error: No 'cnf' array in JSON\n";
        return false;
    }
    
    const auto& cnf_json = root["cnf"];
    cnf.clear();
    cnf.reserve(cnf_json.size());
    
    for (const auto& clause_json : cnf_json) {
        if (!clause_json.isArray()) continue;
        
        Clause clause;
        clause.reserve(clause_json.size());
        
        for (const auto& lit_json : clause_json) {
            if (lit_json.isInt()) {
                clause.push_back(lit_json.asInt());
            }
        }
        
        if (!clause.empty()) {
            cnf.push_back(std::move(clause));
        }
    }
    
    return true;
}

bool write_json_cnf(const fs::path& path, Json::Value& root, const CNF& cnf) {
    Json::Value cnf_json(Json::arrayValue);
    
    for (const auto& clause : cnf) {
        Json::Value clause_json(Json::arrayValue);
        for (auto lit : clause) {
            clause_json.append(lit);
        }
        cnf_json.append(clause_json);
    }
    
    root["cnf"] = cnf_json;
    
    std::ofstream file(path);
    if (!file.is_open()) {
        std::cerr << "Error: Cannot write to " << path << "\n";
        return false;
    }
    
    Json::StreamWriterBuilder builder;
    builder["indentation"] = "  ";
    std::unique_ptr<Json::StreamWriter> writer(builder.newStreamWriter());
    writer->write(root, &file);
    file << "\n";
    
    return true;
}

// Process a single file
bool process_file(const fs::path& input_path, const fs::path& output_path,
                  const Config& config) {
    auto start_time = std::chrono::high_resolution_clock::now();
    
    // Read input
    Json::Value root;
    CNF cnf;
    if (!read_json_cnf(input_path, root, cnf)) {
        return false;
    }
    
    size_t original_size = cnf.size();
    
    // Minimize
    if (config.two_stage) {
        // Stage 1: Basic
        CNFMinimizer basic_minimizer("basic");
        cnf = basic_minimizer.minimize(std::move(cnf));
        
        // Stage 2: Safe
        CNFMinimizer safe_minimizer("safe");
        cnf = safe_minimizer.minimize(std::move(cnf));
        
        if (config.verbose) {
            std::cout << input_path.filename().string() << ":\n";
            safe_minimizer.get_stats().print();
        }
    } else {
        // Single stage
        CNFMinimizer minimizer(config.mode);
        cnf = minimizer.minimize(std::move(cnf));
        
        if (config.verbose) {
            std::cout << input_path.filename().string() << ":\n";
            minimizer.get_stats().print();
        }
    }
    
    // Write output (unless dry run or no reduction)
    if (!config.dry_run && cnf.size() < original_size) {
        if (!write_json_cnf(output_path, root, cnf)) {
            return false;
        }
    } else if (!config.dry_run && output_path != input_path) {
        // Copy original if no reduction
        fs::copy_file(input_path, output_path, fs::copy_options::overwrite_existing);
    }
    
    auto end_time = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time);
    
    if (config.verbose) {
        std::cout << "  Processing time: " << duration.count() << "ms\n\n";
    }
    
    return true;
}

// Process directory in parallel
void process_directory(const Config& config) {
    std::vector<fs::path> json_files;
    
    // Collect JSON files
    for (const auto& entry : fs::directory_iterator(config.input_path)) {
        if (entry.is_regular_file() && entry.path().extension() == ".json") {
            json_files.push_back(entry.path());
        }
    }
    
    if (json_files.empty()) {
        std::cout << "No JSON files found in " << config.input_path << "\n";
        return;
    }
    
    std::cout << "Found " << json_files.size() << " JSON files to optimize\n";
    std::cout << "Input directory:  " << config.input_path << "\n";
    std::cout << "Output directory: " << config.output_path << "\n";
    std::cout << "Mode: " << (config.two_stage ? "Two-stage (basic + safe)" : config.mode) << "\n";
    
    // Create output directory
    fs::create_directories(config.output_path);
    
    // Determine thread count
    unsigned int num_threads = config.num_workers;
    if (num_threads == 0) {
        num_threads = std::thread::hardware_concurrency();
        if (num_threads == 0) num_threads = 1;
    }
    std::cout << "Using " << num_threads << " parallel workers\n\n";
    
    // Process files in parallel
    std::atomic<size_t> processed{0};
    std::atomic<size_t> successful{0};
    std::mutex output_mutex;
    
    auto worker = [&](size_t start, size_t end) {
        for (size_t i = start; i < end; ++i) {
            const auto& input_file = json_files[i];
            auto output_file = config.output_path / input_file.filename();
            
            bool success = process_file(input_file, output_file, config);
            
            if (success) successful.fetch_add(1);
            
            size_t count = processed.fetch_add(1) + 1;
            
            if (!config.verbose) {
                std::lock_guard<std::mutex> lock(output_mutex);
                std::cout << "\rProcessed: " << count << "/" << json_files.size() << std::flush;
            }
        }
    };
    
    // Launch threads
    std::vector<std::thread> threads;
    size_t files_per_thread = json_files.size() / num_threads;
    size_t remainder = json_files.size() % num_threads;
    
    size_t start = 0;
    for (unsigned int i = 0; i < num_threads; ++i) {
        size_t count = files_per_thread + (i < remainder ? 1 : 0);
        if (count > 0) {
            threads.emplace_back(worker, start, start + count);
            start += count;
        }
    }
    
    // Wait for completion
    for (auto& t : threads) {
        t.join();
    }
    
    if (!config.verbose) {
        std::cout << "\n";
    }
    
    // Summary
    std::cout << "\nOptimization complete:\n";
    std::cout << "  Files processed: " << processed.load() << "\n";
    std::cout << "  Successful: " << successful.load() << "\n";
    std::cout << "  Failed: " << (processed.load() - successful.load()) << "\n";
}

void print_usage(const char* program_name) {
    std::cout << "Usage: " << program_name << " [options]\n\n";
    std::cout << "Options:\n";
    std::cout << "  -f FILE          Process single file\n";
    std::cout << "  -d DIR           Process all JSON files in directory\n";
    std::cout << "  -o FILE          Output file (single file mode)\n";
    std::cout << "  -O DIR           Output directory (batch mode)\n";
    std::cout << "  --mode MODE      Minimization mode: basic or safe (default: safe)\n";
    std::cout << "  --two-stage      Apply both basic and safe minimization\n";
    std::cout << "  --workers N      Number of parallel workers (default: auto)\n";
    std::cout << "  --dry-run        Analyze but don't write files\n";
    std::cout << "  -v, --verbose    Verbose output\n";
    std::cout << "  -h, --help       Show this help\n";
}

int main(int argc, char* argv[]) {
    Config config;
    bool single_file_mode = false;
    
    // Parse command line arguments
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        
        if (arg == "-h" || arg == "--help") {
            print_usage(argv[0]);
            return 0;
        } else if (arg == "-f" && i + 1 < argc) {
            config.input_path = argv[++i];
            single_file_mode = true;
        } else if (arg == "-d" && i + 1 < argc) {
            config.input_path = argv[++i];
            single_file_mode = false;
        } else if (arg == "-o" && i + 1 < argc) {
            config.output_path = argv[++i];
        } else if (arg == "-O" && i + 1 < argc) {
            config.output_path = argv[++i];
        } else if (arg == "--mode" && i + 1 < argc) {
            config.mode = argv[++i];
            if (config.mode != "basic" && config.mode != "safe") {
                std::cerr << "Error: Invalid mode. Use 'basic' or 'safe'\n";
                return 1;
            }
        } else if (arg == "--two-stage") {
            config.two_stage = true;
        } else if (arg == "--workers" && i + 1 < argc) {
            config.num_workers = std::stoi(argv[++i]);
        } else if (arg == "--dry-run") {
            config.dry_run = true;
        } else if (arg == "-v" || arg == "--verbose") {
            config.verbose = true;
        } else {
            std::cerr << "Error: Unknown option " << arg << "\n";
            print_usage(argv[0]);
            return 1;
        }
    }
    
    // Validate arguments
    if (config.input_path.empty()) {
        std::cerr << "Error: No input specified. Use -f or -d\n";
        print_usage(argv[0]);
        return 1;
    }
    
    // Process
    if (single_file_mode) {
        if (!fs::exists(config.input_path)) {
            std::cerr << "Error: File not found: " << config.input_path << "\n";
            return 1;
        }
        
        if (config.output_path.empty()) {
            config.output_path = config.input_path;  // In-place
        }
        
        if (!process_file(config.input_path, config.output_path, config)) {
            return 1;
        }
    } else {
        if (!fs::is_directory(config.input_path)) {
            std::cerr << "Error: Not a directory: " << config.input_path << "\n";
            return 1;
        }
        
        if (config.output_path.empty()) {
            config.output_path = config.input_path.parent_path() / 
                                (config.input_path.filename().string() + "_optimized");
        }
        
        process_directory(config);
    }
    
    return 0;
}
