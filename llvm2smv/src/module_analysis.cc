#include "llvm2smv/module_analysis.hh"
#include "llvm/Config/llvm-config.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/Path.h"
#include <map>
#include <set>
#include <vector>

static_assert(LLVM_VERSION_MAJOR == 18, "llvm2smv M0 requires LLVM 18");
using namespace llvm;

namespace llvm2smv {

json::Object diagnostic(StringRef code, StringRef message)
{
    return json::Object{{"severity", "error"}, {"code", code.str()},
                        {"message", message.str()}, {"source", nullptr}};
}

json::Object capabilities()
{
    return json::Object{
        {"version", 1}, {"milestone", "M0"}, {"llvm_version", LLVM_VERSION_STRING},
        {"required_llvm_major", 18}, {"translation_available", false},
        {"supported_features", json::Array{}},
        {"operations", json::Array{"analyze", "capabilities"}},
        {"input_formats", json::Array{"llvm-ir", "llvm-bitcode"}},
        {"message", "M0 provides verified feature inventory and diagnostics. "
                    "SMV generation is disabled until validated lowering is implemented."}};
}

namespace {
std::string typeName(const Type* type)
{
    std::string text;
    raw_string_ostream stream(text);
    type->print(stream);
    return text;
}

std::string valueText(const Value& value)
{
    std::string text;
    raw_string_ostream stream(text);
    value.print(stream);
    return text;
}

json::Array attributes(const AttributeList& list)
{
    json::Array result;
    for (unsigned index : list.indexes())
        for (Attribute attribute : list.getAttributes(index))
            result.push_back(json::Object{{"index", static_cast<int64_t>(index)},
                                          {"attribute", attribute.getAsString()}});
    return result;
}

json::Value location(const Instruction& instruction)
{
    const DebugLoc& loc = instruction.getDebugLoc();
    if (!loc) return nullptr;
    SmallString<256> path(loc->getFilename());
    if (sys::path::is_relative(path) && !loc->getDirectory().empty()) {
        path = loc->getDirectory();
        sys::path::append(path, loc->getFilename());
    }
    return json::Object{{"file", path.str().str()}, {"line", loc.getLine()}, {"column", loc.getCol()}};
}

void collectType(const Type* type, std::set<const Type*>& seen, std::set<std::string>& names)
{
    if (!seen.insert(type).second) return;
    names.insert(typeName(type));
    for (Type* child : type->subtypes()) collectType(child, seen, names);
}
} // namespace

json::Object analyzeModule(const Module& module, StringRef entryName)
{
    json::Array diagnostics, functions, globals, aliases, ifuncs, metadata;
    std::map<std::string, int64_t> opcodes;
    std::set<const Type*> seenTypes;
    std::set<std::string> types;
    auto reject = [&](StringRef code, StringRef message) {
        diagnostics.push_back(diagnostic(code, message));
    };
    if (module.getTargetTriple().empty())
        reject("missing-target", "Specify the compilation target triple; host layout is never inferred.");
    if (module.getDataLayoutStr().empty())
        reject("missing-data-layout", "Specify the target DataLayout; host layout is never inferred.");
    if (!module.getModuleInlineAsm().empty())
        reject("unsupported-module-asm", "Module inline assembly has no execution model.");

    for (const GlobalVariable& global : module.globals()) {
        collectType(global.getValueType(), seenTypes, types);
        globals.push_back(json::Object{
            {"name", global.getName().str()}, {"type", typeName(global.getValueType())},
            {"address_space", global.getAddressSpace()},
            {"declaration", global.isDeclaration()}, {"constant", global.isConstant()},
            {"thread_local", global.isThreadLocal()}, {"ir", valueText(global)}});
        auto issue = diagnostic("unsupported-global", "Global storage and initialization require memory lowering.");
        issue["global"] = global.getName().str();
        diagnostics.push_back(std::move(issue));
    }
    for (const GlobalAlias& alias : module.aliases()) {
        aliases.push_back(valueText(alias));
        reject("unsupported-alias", "Global aliases require address and linkage semantics.");
    }
    for (const GlobalIFunc& ifunc : module.ifuncs()) {
        ifuncs.push_back(valueText(ifunc));
        reject("unsupported-ifunc", "Indirect function resolvers have no execution model.");
    }
    for (const NamedMDNode& node : module.named_metadata()) {
        std::string text;
        raw_string_ostream stream(text);
        node.print(stream);
        metadata.push_back(json::Object{{"name", node.getName().str()}, {"ir", text}});
    }

    const Function* entry = module.getFunction(entryName);
    std::vector<const Function*> pending;
    std::set<const Function*> seenFunctions;
    if (!entry || entry->isDeclaration()) {
        reject("invalid-entry", "The selected entry must name a defined function; no fallback is selected.");
    } else {
        pending.push_back(entry);
        seenFunctions.insert(entry);
    }
    // Inspect all blocks in the direct call closure, including infeasible paths.
    for (size_t index = 0; index < pending.size(); ++index) {
        const Function& function = *pending[index];
        collectType(function.getFunctionType(), seenTypes, types);
        json::Array instructions;
        auto attrs = attributes(function.getAttributes());
        if (!attrs.empty()) {
            auto issue = diagnostic("unsupported-attributes", "Function/parameter attributes require a validated semantic policy.");
            issue["function"] = function.getName().str();
            issue["attributes"] = attributes(function.getAttributes());
            diagnostics.push_back(std::move(issue));
        }
        if (function.isDeclaration()) {
            auto issue = diagnostic("unsupported-external-call", "External functions require explicit runtime models.");
            issue["function"] = function.getName().str();
            diagnostics.push_back(std::move(issue));
        }
        unsigned blockIndex = 0;
        for (const BasicBlock& block : function) {
            unsigned instructionIndex = 0;
            for (const Instruction& instruction : block) {
                collectType(instruction.getType(), seenTypes, types);
                for (const Use& operand : instruction.operands()) collectType(operand->getType(), seenTypes, types);
                ++opcodes[instruction.getOpcodeName()];
                json::Object record{
                    {"block", blockIndex}, {"block_name", block.getName().str()},
                    {"index", instructionIndex++}, {"opcode", instruction.getOpcodeName()},
                    {"type", typeName(instruction.getType())}, {"ir", valueText(instruction)},
                    {"source", location(instruction)}, {"supported", false}};
                if (const auto* call = dyn_cast<CallBase>(&instruction)) {
                    const auto* callee = dyn_cast<Function>(call->getCalledOperand()->stripPointerCasts());
                    record["callee"] = callee ? json::Value(callee->getName().str()) : json::Value(nullptr);
                    record["attributes"] = attributes(call->getAttributes());
                    record["operand_bundle_count"] = call->getNumOperandBundles();
                    record["inline_asm"] = call->isInlineAsm();
                    if (callee && seenFunctions.insert(callee).second) pending.push_back(callee);
                }
                auto issue = diagnostic("unsupported-instruction",
                    "No validated instruction lowering is available in M0. See the implementation plan for staged support.");
                issue["function"] = function.getName().str();
                issue["instruction"] = json::Object(record);
                issue["source"] = location(instruction);
                diagnostics.push_back(std::move(issue));
                instructions.push_back(std::move(record));
            }
            ++blockIndex;
        }
        functions.push_back(json::Object{
            {"name", function.getName().str()}, {"declaration", function.isDeclaration()},
            {"type", typeName(function.getFunctionType())}, {"calling_convention", function.getCallingConv()},
            {"attributes", std::move(attrs)}, {"instructions", std::move(instructions)}});
    }
    // Inventory-only changes must never accidentally enable the legacy writer.
    reject("translation-unavailable", "M0 does not generate SMV. Validated execution lowering is required before translation can be enabled.");
    json::Object counts;
    for (const auto& [opcode, count] : opcodes) counts[opcode] = count;
    json::Array typeList;
    for (const auto& type : types) {
        typeList.push_back(type);
        auto issue = diagnostic("unsupported-type", "No validated type lowering is available in M0.");
        issue["type"] = type;
        diagnostics.push_back(std::move(issue));
    }
    return json::Object{
        {"version", 1}, {"status", "unsupported"}, {"translation_available", false},
        {"llvm_version", LLVM_VERSION_STRING}, {"entry", entryName.str()},
        {"target_triple", module.getTargetTriple()}, {"data_layout", module.getDataLayoutStr()},
        {"inventory", json::Object{{"functions", std::move(functions)}, {"globals", std::move(globals)},
                                   {"aliases", std::move(aliases)}, {"ifuncs", std::move(ifuncs)},
                                   {"metadata", std::move(metadata)}, {"types", std::move(typeList)},
                                   {"opcodes", std::move(counts)}}},
        {"diagnostics", std::move(diagnostics)}};
}

void printDiagnostics(const json::Object& report, bool jsonFormat)
{
    if (jsonFormat) {
        errs() << formatv("{0:2}\n", json::Value(json::Object(report)));
        return;
    }
    if (const auto* items = report.getArray("diagnostics")) {
        for (const auto& item : *items) {
            const auto& issue = *item.getAsObject();
            errs() << "llvm2smv: error [" << *issue.getString("code") << "]: " << *issue.getString("message");
            if (auto function = issue.getString("function")) errs() << " (function " << *function << ")";
            if (auto global = issue.getString("global")) errs() << " (global " << *global << ")";
            if (auto type = issue.getString("type")) errs() << " (type " << *type << ")";
            if (const auto* attrs = issue.getArray("attributes"))
                for (const auto& attr : *attrs)
                    errs() << "\n  attribute: " << *attr.getAsObject()->getString("attribute");
            if (const auto* instruction = issue.getObject("instruction")) errs() << "\n" << *instruction->getString("ir");
            if (const auto* source = issue.getObject("source"))
                errs() << "\n" << *source->getString("file") << ":" << *source->getInteger("line")
                       << ":" << *source->getInteger("column");
            errs() << "\n";
        }
    }
}
} // namespace llvm2smv
