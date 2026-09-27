#ifndef LLVM2SMV_MODULE_ANALYSIS_HH
#define LLVM2SMV_MODULE_ANALYSIS_HH

#include "llvm/IR/Module.h"
#include "llvm/Support/JSON.h"

namespace llvm2smv {
// M0 inventories verified IR. A report never authorizes SMV generation.
llvm::json::Object capabilities();
llvm::json::Object analyzeModule(const llvm::Module& module, llvm::StringRef entry);
llvm::json::Object diagnostic(llvm::StringRef code, llvm::StringRef message);
void printDiagnostics(const llvm::json::Object& report, bool json);
}
#endif
