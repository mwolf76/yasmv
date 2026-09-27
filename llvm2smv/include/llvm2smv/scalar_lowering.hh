#ifndef LLVM2SMV_SCALAR_LOWERING_HH
#define LLVM2SMV_SCALAR_LOWERING_HH
#include "llvm/IR/Module.h"
#include "llvm/Support/JSON.h"
#include <stdexcept>
namespace llvm2smv {
class ScalarError : public std::runtime_error {
public:
    ScalarError(std::string message, const llvm::Instruction* instruction = nullptr);
    llvm::json::Object issue;
};
// Verified, closed, zero-argument entry; mutates only its owned input module.
// Returns a candidate bundle. Native validation/publication remains mandatory.
llvm::json::Object lowerScalar(llvm::Module& module, llvm::StringRef entry);
}
#endif
