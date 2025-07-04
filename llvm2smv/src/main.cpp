#include <string>

#include "llvm2smv/LLVM2SMVPass.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

static cl::opt<std::string> InputFilename(cl::Positional,
                                          cl::desc("<input LLVM IR file>"), cl::Required);

static cl::opt<std::string> OutputFilename("o",
                                           cl::desc("Output SMV file"), cl::value_desc("filename"),
                                           cl::init("-"));

static cl::opt<unsigned> WordWidth("word-width",
                                   cl::desc("Default word width for integers"), cl::init(32));

static cl::opt<bool> Verbose("v", cl::desc("Enable verbose output"),
                             cl::init(false));

int main(int argc, char** argv)
{
    InitLLVM X(argc, argv);

    cl::ParseCommandLineOptions(argc, argv, "LLVM to SMV translator\n");

    // Set up the context and module
    LLVMContext Context;
    SMDiagnostic Err;

    // Parse the input LLVM IR file
    std::unique_ptr<Module> M = parseIRFile(InputFilename, Err, Context);
    if (!M) {
        Err.print(argv[0], errs());
        return 1;
    }

    if (Verbose) {
        errs() << "Loaded module: " << M->getName() << "\n";
        errs() << "Functions: " << M->size() << "\n";
        errs() << "Global variables: " << M->global_size() << "\n";
    }

    // Set up output file
    std::error_code EC;
    std::unique_ptr<ToolOutputFile> Out;
    if (OutputFilename == "-") {
        Out = std::make_unique<ToolOutputFile>("-", EC, sys::fs::OF_Text);
    } else {
        Out = std::make_unique<ToolOutputFile>(OutputFilename, EC,
                                               sys::fs::OF_Text);
    }

    if (EC) {
        errs() << "Error opening output file: " << EC.message() << "\n";
        return 1;
    }

    // Write word width directive
    Out->os() << "#word-width " << WordWidth << "\n\n";

    // Run the translation pass
    llvm2smv::LLVM2SMVPass Translator(Out->os());
    Translator.runOnModule(*M);

    // Keep the output file
    Out->keep();

    if (Verbose) {
        errs() << "Translation complete. Output written to "
               << (OutputFilename.getValue() == "-" ? "stdout" : OutputFilename.getValue()) << "\n";
    }

    return 0;
}
