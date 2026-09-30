// Replay a captured, checked interpolation obligation without model compilation.
#include <sat/proof_tracer.hh>
#include <sat/interpolation_diagnostics.hh>
#include <cadical.hpp>
#include <jsoncpp/json/json.h>
#include <climits>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <set>
#include <sstream>
#include <stdexcept>

namespace {
using namespace sat;
using proof::Clause;
void require(bool ok, const char* message) { if (!ok) throw std::runtime_error(message); }
void end(std::istream& in) { std::string extra; require(!(in >> extra), "Trailing record data"); }
Clause clause(std::istream& in) {
    Clause result; long long lit;
    while (in >> lit) {
        if (!lit) return result;
        require(lit > INT_MIN && lit <= INT_MAX, "Invalid proof literal");
        result.push_back(static_cast<int>(lit));
    }
    throw std::runtime_error("Unterminated clause");
}
proof::Id id(std::istream& in) {
    proof::Id value = 0; require(bool(in >> value) && value > 0, "Invalid proof ID"); return value;
}
std::ifstream open(const std::filesystem::path& path, const std::string& header) {
    std::ifstream in(path); std::string line;
    require(bool(std::getline(in,line)) && line == header, "Missing or unsupported artifact header");
    return in;
}
struct Original { proof::Id id; proof::Partition side; Clause literals; };
struct Input {
    std::vector<Original> originals;
    std::map<int,Circuit::Atom> shared;
    int variables = 0;
    explicit Input(const std::filesystem::path& path) {
        std::ifstream complete(path/"complete"); std::string marker;
        require(bool(std::getline(complete,marker)) && marker == "verified-unsat", "Capture is not a verified completed UNSAT query");
        end(complete);
        auto in=open(path/"input.cnf","yasmv-partitioned-cnf 1"); std::string line;
        std::set<proof::Id> ids; std::map<int,unsigned> ownership;
        while (std::getline(in,line)) {
            std::istringstream row(line); char side;
            require(bool(row >> side) && (side=='a'||side=='b'), "Invalid partition");
            auto number=id(row); require(ids.insert(number).second, "Duplicate original ID");
            auto lits=clause(row); end(row);
            for (int lit:lits) { variables=std::max(variables,std::abs(lit)); ownership[std::abs(lit)] |= side=='a'?1:2; }
            originals.push_back({number,side=='a'?proof::Partition::a:proof::Partition::b,std::move(lits)});
        }
        require(in.eof() && !originals.empty(), "Invalid CNF stream");
        Json::Value metadata; std::ifstream meta(path/"interface.json");
        require(bool(meta), "Missing interface"); meta >> metadata;
        require(metadata["format"]=="yasmv-interpolation-capture" && metadata["version"]==1 && metadata["interface"].isArray(), "Invalid interface format");
        std::set<Circuit::Atom> atoms;
        for (const auto& entry:metadata["interface"]) {
            require(entry["variable"].isInt() && entry["atom"].isUInt64(), "Invalid interface entry");
            const auto var=entry["variable"].asInt(); const auto atom=entry["atom"].asUInt64();
            require(var>0 && atom>0 && ownership[var]==3, "Interface variable is not shared");
            require(shared.emplace(var,atom).second && atoms.insert(atom).second, "Aliased interface");
        }
        for (auto [var,sides]:ownership) if (sides==3) require(shared.count(var), "Missing shared variable");
    }
    bool verify(const Circuit& circuit,Circuit::Ref root) const {
        std::map<Circuit::Atom,int> atoms;
        for (auto [var,atom]:shared) atoms.emplace(atom,var);
        for (auto atom:circuit.support(root)) require(atoms.count(atom), "Foreign interpolant atom");
        for (auto side:{proof::Partition::a,proof::Partition::b}) {
            CaDiCaL::Solver solver; solver.set("quiet",1); solver.set("seed",0); solver.set("inprobing",0);
            for (int i=0;i<variables;++i) solver.declare_one_more_variable();
            for (const auto& c:originals) if (c.side==side) { for (int lit:c.literals) solver.add(lit); solver.add(0); }
            int last=variables;
            const auto desired=side==proof::Partition::a ? circuit.negate(root):root;
            const int top=circuit.encode(desired,[&] { require(last<INT_MAX,"Too many variables"); ++last; require(solver.declare_one_more_variable()==last,"Unexpected variable mapping"); return last; },
                [&](Circuit::Atom atom) { return atoms.at(atom); },
                [&](const Clause& c) { for (int lit:c) solver.add(lit); solver.add(0); });
            solver.add(top); solver.add(0);
            const int status=solver.solve();
            diagnostics::sample(side==proof::Partition::a?"craig_a_solved":"craig_b_solved");
            if (status!=20) return false;
        }
        return true;
    }
};
proof::NodeId replay(const std::filesystem::path& path,const Input& input,proof::ResolutionProof& proof) {
    auto in=open(path/"proof.events","yasmv-proof-events 1"); std::string line;
    size_t originals=0; bool concluded=false; proof::NodeId root=0;
    while (std::getline(in,line)) {
        std::istringstream row(line); char op; require(bool(row>>op),"Empty proof event");
        // CaDiCaL can delete clauses during destruction after conclude_unsat.
        require(!concluded || op=='e',"Proof event after conclusion");
        if (op=='o') {
            char side; require(bool(row>>side) && (side=='a'||side=='b'),"Invalid original partition");
            auto number=id(row); auto c=clause(row);
            require(originals<input.originals.size(),"Extra proof original");
            const auto& expected=input.originals[originals++];
            const auto partition=side=='a'?proof::Partition::a:proof::Partition::b;
            require(number==expected.id && partition==expected.side && c==expected.literals,"Proof originals do not match CNF");
            proof.original(number,c,partition);
        } else if (op=='d') {
            auto number=id(row); int witness; require(bool(row>>witness),"Missing witness");
            auto c=clause(row); std::vector<proof::Id> hints; proof::Id hint;
            while (true) { require(bool(row>>hint) && hint>=0,"Invalid hint list"); if (!hint) break; hints.push_back(hint); }
            proof.derive(number,c,hints,witness);
        } else if (op=='e'||op=='r') {
            auto number=id(row); auto c=clause(row);
            if (op=='e') proof.erase(number,c); else proof.restore(number,c);
        } else if (op=='u') {
            require(originals==input.originals.size(),"Missing proof originals");
            root=proof.conclude(id(row)); concluded=true;
        } else throw std::runtime_error("Unknown proof event");
        end(row);
    }
    require(in.eof() && concluded,"Incomplete proof event stream");
    return root;
}
}
int main(int argc,char** argv) {
    try {
        require(argc==3 && (std::string(argv[2])=="events" || std::string(argv[2])=="solve"),
                "usage: interpolation_replay CAPTURE_DIRECTORY events|solve");
        require(std::string(CaDiCaL::Solver::signature())=="cadical-3.0.1-c607304","Unexpected CaDiCaL build");
        const std::filesystem::path directory(argv[1]);
        diagnostics::sample("replay_load_begin");
        Input input(directory);
        diagnostics::sample("replay_load_end",{{"input_clauses",input.originals.size()}});
        Json::Value result; Circuit circuit; Circuit::Ref root;
        {
            diagnostics::Run diagnostic;
            {
                proof::ResolutionProof proof;
                std::unique_ptr<CaDiCaL::Solver> owned_solver;
                proof.observe([&](const proof::ResolutionProof& p) { diagnostic.progress(p); });
                proof::NodeId conclusion;
                if (std::string(argv[2])=="events") {
                    diagnostic.phase("replay_events_begin");
                    conclusion=replay(directory,input,proof);
                } else {
                    proof::ProofTracer tracer;
                    owned_solver=std::make_unique<CaDiCaL::Solver>();
                    auto& solver=*owned_solver;
                    require(solver.configure("plain") && solver.set("quiet",1) && solver.set("seed",0) &&
                            solver.set("factor",0) && solver.set("lucky",0) && solver.set("walk",0) && solver.set("inprobing",0),"Solver setup failed");
                    solver.connect_proof_tracer(&tracer,true);
                    // Detach before the tracer is destroyed, including on failure.
                    struct Disconnect {
                        CaDiCaL::Solver& solver;
                        proof::ProofTracer& tracer;
                        ~Disconnect() { solver.disconnect_proof_tracer(&tracer); }
                    } disconnect{solver,tracer};
                    for (int i=0;i<input.variables;++i) solver.declare_one_more_variable();
                    for (const auto& c:input.originals) {
                        tracer.submitted=c.literals; tracer.submitting=c.side;
                        for (int lit:c.literals) solver.add(lit);
                        solver.add(0); tracer.check();
                        require(!tracer.submitting,"Missing original callback");
                    }
                    diagnostic.phase("replay_solve_begin");
                    const int status=solver.solve(); tracer.check();
                    if (status==20) solver.conclude();
                    tracer.check();
                    require(status==20 && tracer.conclusion.has_value(),"Captured formula did not refute");
                    conclusion=*tracer.conclusion; proof=std::move(tracer.proof);
                }
                diagnostic.phase("replay_proof_complete",&proof);
                root=interpolate(proof,conclusion,input.shared,circuit);
                diagnostic.phase("interpolant_complete",&proof,&circuit,root);
                // Historical work counters survive; the large proof does not.
                for (const auto& [key,value]:diagnostics::proof_memory(proof)) result[key]=Json::UInt64(value);
            }
            diagnostic.phase("replay_proof_destroyed",nullptr,&circuit,root);
            diagnostic.phase("craig_verification_begin",nullptr,&circuit,root);
            require(input.verify(circuit,root),"Fresh Craig verification failed");
            diagnostic.phase("craig_verification_end",nullptr,&circuit,root);
            for (const auto& [key,value]:diagnostics::circuit_memory(circuit,root)) result[key]=Json::UInt64(value);
            diagnostic.complete(true);
        }
        result["status"]="completed"; result["verified"]=true;
        result["mode"]=argv[2]; result["scope"]="single-interpolation-obligation";
        result["obligations"]["A_implies_J"]="unsatisfiable";
        result["obligations"]["J_and_B"]="unsatisfiable";
        std::cout<<result<<'\n';
        return 0;
    } catch (const std::exception& e) { std::cerr<<e.what()<<'\n'; return 2; }
}
