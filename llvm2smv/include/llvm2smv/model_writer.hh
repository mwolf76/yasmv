#ifndef LLVM2SMV_MODEL_WRITER_HH
#define LLVM2SMV_MODEL_WRITER_HH
#include "llvm2smv/transition_system.hh"
#include "llvm/Support/JSON.h"

namespace llvm2smv::ts {
// A deterministic container of UTF-8 files. Publication additionally requires
// successful yasmv model validation; see tools/llvm2smv_artifact.py.
llvm::json::Object artifact(const Model& model, const std::map<std::string, std::string>& provenance);
std::string render(const Model& model);
std::string renderExpr(const Expr& expression);
std::string sha256(const std::string& bytes);
}
#endif
