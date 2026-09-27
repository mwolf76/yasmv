#include "llvm2smv/module_analysis.hh"
#include "llvm2smv/scalar_lowering.hh"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/SourceMgr.h"

using namespace llvm;

static cl::opt<std::string> InputFilename(cl::Positional, cl::desc("<LLVM IR or bitcode>"), cl::init(""));
static cl::opt<std::string> OutputFilename("o", cl::desc("SMV destination (not yet enabled)"));
static cl::opt<std::string> Entry("entry", cl::desc("Defined entry function"), cl::init("main"));
static cl::opt<bool> Analyze("analyze", cl::desc("Print feature inventory and rejection diagnostics as JSON"));
static cl::opt<bool> Capabilities("capabilities", cl::desc("Print supported operations as JSON"));
static cl::opt<bool> EmitScalar("emit-scalar-bundle", cl::desc("Emit an M2 scalar candidate bundle for native validation by the publisher"));
enum DiagnosticFormat { Text, JSON };
static cl::opt<DiagnosticFormat> Diagnostics("diagnostics", cl::desc("Diagnostic format"),
    cl::values(clEnumValN(Text, "text", "Human-readable diagnostics"),
               clEnumValN(JSON, "json", "Structured JSON diagnostics")), cl::init(Text));

int main(int argc, char** argv)
{
    InitLLVM init(argc, argv);
    cl::ParseCommandLineOptions(argc, argv, "LLVM to SMV: analysis and rejection gate\n");
    auto fail = [](StringRef code, StringRef message) {
        json::Array diagnostics;
        diagnostics.push_back(llvm2smv::diagnostic(code, message));
        json::Object report{{"version", 1}, {"status", "error"},
                            {"translation_available", false}, {"diagnostics", std::move(diagnostics)}};
        if (Analyze) outs() << formatv("{0:2}\n", json::Value(std::move(report)));
        else llvm2smv::printDiagnostics(report, Diagnostics == JSON);
        return 2;
    };
    if (Capabilities) {
        if (EmitScalar || Analyze || !InputFilename.empty() || OutputFilename.getNumOccurrences() || Entry.getNumOccurrences())
            return fail("invalid-options", "--capabilities cannot be combined with an input, --analyze, --entry, or -o.");
        outs() << formatv("{0:2}\n", json::Value(llvm2smv::capabilities()));
        return 0;
    }
    if (InputFilename.empty()) return fail("missing-input", "An LLVM IR or bitcode input is required.");
    if (Entry.empty()) return fail("invalid-entry", "The entry name must not be empty.");
    if (Analyze && OutputFilename.getNumOccurrences())
        return fail("invalid-options", "--analyze writes JSON to stdout and does not accept an SMV destination.");

    if (EmitScalar && (Analyze || OutputFilename.getNumOccurrences()))
        return fail("invalid-options", "Scalar candidates use stdout; use tools/llvm2smv_translate.py to validate and publish a bundle.");

    LLVMContext context;
    SMDiagnostic error;
    auto module = parseIRFile(InputFilename, error, context);
    if (!module) {
        std::string message;
        raw_string_ostream stream(message);
        error.print(argv[0], stream);
        return fail("invalid-ir", message);
    }
    std::string verification;
    raw_string_ostream verifier(verification);
    if (verifyModule(*module, &verifier)) return fail("invalid-ir", verification);

    if (EmitScalar) {
        try {
            auto candidate = llvm2smv::lowerScalar(*module, Entry);
            outs() << formatv("{0:2}\n", json::Value(std::move(candidate)));
            return 0;
        } catch (const llvm2smv::ScalarError& error) {
            json::Array diagnostics; diagnostics.push_back(json::Object(error.issue));
            json::Object report{{"version", 1}, {"status", "unsupported"},
                {"translation_available", false}, {"diagnostics", std::move(diagnostics)}};
            llvm2smv::printDiagnostics(report, Diagnostics == JSON);
            return 2;
        } catch (const std::exception& error) {
            return fail("scalar-lowering-error", error.what());
        }
    }
    auto report = llvm2smv::analyzeModule(*module, Entry);
    if (Analyze) outs() << formatv("{0:2}\n", json::Value(std::move(report)));
    else llvm2smv::printDiagnostics(report, Diagnostics == JSON);
    // Do not even open OutputFilename: preserve existing files and leave stdout
    // empty for failed translation. There is deliberately no legacy escape hatch.
    return 2;
}
