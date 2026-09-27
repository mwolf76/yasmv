#include "llvm2smv/model_writer.hh"
#include "llvm/ADT/SmallString.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/SHA256.h"
#include <set>
#include <sstream>

namespace llvm2smv::ts {
namespace {
std::string typeText(const Type& type)
{
    switch (type.kind()) {
    case Type::Kind::Boolean: return "boolean";
    case Type::Kind::Word: return (type.isSigned() ? "int" : "uint") + std::to_string(type.width());
    case Type::Kind::Array: return typeText(type.element()) + "[" + std::to_string(type.count()) + "]";
    case Type::Kind::Enum: {
        std::string result = "{ ";
        for (const auto& literal : type.literals()) {
            if (result != "{ ") result += ", ";
            result += literalName(type, literal);
        }
        return result + " }";
    }
    }
    throw ModelError("Unknown type");
}
const char* operatorText(Op op)
{
    switch (op) {
    case Op::Not: return "!"; case Op::BitNot: return "~"; case Op::Negate: return "-";
    case Op::And: return "&&"; case Op::Or: return "||"; case Op::Xor: return "!=";
    case Op::Equal: return "="; case Op::NotEqual: return "!=";
    case Op::Less: return "<"; case Op::LessEqual: return "<=";
    case Op::Greater: return ">"; case Op::GreaterEqual: return ">=";
    case Op::Add: return "+"; case Op::Sub: return "-"; case Op::Mul: return "*";
    case Op::Div: return "/"; case Op::Rem: return "%";
    case Op::BitAnd: return "&"; case Op::BitOr: return "|"; case Op::BitXor: return "^";
    case Op::ShiftLeft: return "<<"; case Op::ShiftRight: return ">>";
    }
    throw ModelError("Unknown operator");
}
std::string jsonText(llvm::json::Object object)
{
    return llvm::formatv("{0:2}\n", llvm::json::Value(std::move(object))).str();
}
}

std::string renderExpr(const Expr& expr)
{
    const auto& operands = expr.operands();
    switch (expr.kind()) {
    case Expr::Kind::Boolean: return expr.booleanValue() ? "TRUE" : "FALSE";
    case Expr::Kind::Integer: {
        llvm::SmallString<32> digits;
        expr.bits().toString(digits, 16, false);
        return "((" + typeText(expr.type()) + ") 0x" + digits.str().str() + ")";
    }
    case Expr::Kind::Literal: return literalName(expr.type(), expr.literalValue());
    case Expr::Kind::Variable: return symbolName(expr.symbol()->key);
    case Expr::Kind::Unary: return "(" + std::string(operatorText(expr.op())) + "(" + renderExpr(operands[0]) + "))";
    case Expr::Kind::Binary: return "(" + renderExpr(operands[0]) + " " + operatorText(expr.op()) + " " + renderExpr(operands[1]) + ")";
    case Expr::Kind::Cast: return "((" + typeText(expr.type()) + ") (" + renderExpr(operands[0]) + "))";
    case Expr::Kind::Select: return "(" + renderExpr(operands[0]) + " ? " + renderExpr(operands[1]) + " : " + renderExpr(operands[2]) + ")";
    case Expr::Kind::Array: {
        std::string result = "[";
        for (const auto& operand : operands) {
            if (result != "[") result += ", ";
            result += renderExpr(operand);
        }
        return result + "]";
    }
    case Expr::Kind::Index: return "(" + renderExpr(operands[0]) + ")[" + std::to_string(expr.indexValue()) + "]";
    }
    throw ModelError("Unknown expression");
}

std::string render(const Model& model)
{
    model.validate();
    std::set<std::string> writers;
    for (const auto& [key, step] : model.steps())
        for (const auto& write : step.writes) writers.insert(write.target->key);
    std::ostringstream output;
    output << "-- llvm2smv typed model v1; no C/LLVM equivalence claim\n#word-width 64\nMODULE main\n";
    for (const auto& [key, variable] : model.variables()) {
        if (variable.symbol->mode != Mode::Choice)
            output << (writers.count(key) ? "#inertial\n" : "#frozen\n");
        output << "VAR " << symbolName(key) << " : " << typeText(variable.symbol->type) << ";\n";
    }
    for (const auto& [key, variable] : model.variables())
        if (variable.initial) output << "INIT (" << symbolName(key) << " = " << renderExpr(*variable.initial) << ");\n";
    for (const auto& [key, expression] : model.invariants()) output << "INVAR " << renderExpr(expression) << ";\n";
    for (const auto& [key, step] : model.steps()) {
        output << "TRANS " << renderExpr(step.guard) << " ?: ";
        bool first = true;
        for (const auto& write : step.writes) {
            if (!first) output << ", ";
            output << symbolName(write.target->key) << " := " << renderExpr(write.value);
            first = false;
        }
        output << ";\n";
    }
    for (const auto& [key, expression] : model.properties())
        output << "DEFINE " << propertyName(key) << " := " << renderExpr(expression) << ";\n";
    return output.str();
}

std::string sha256(const std::string& bytes)
{
    llvm::SHA256 hash;
    hash.update(bytes);
    auto digest = hash.final();
    return hexKey(std::string(reinterpret_cast<const char*>(digest.data()), digest.size()));
}

llvm::json::Object artifact(const Model& model, const std::map<std::string, std::string>& provenance, const std::string& scope)
{
    using namespace llvm;
    if (scope.empty() || !json::isUTF8(scope)) throw ModelError("Artifact scope must be nonempty UTF-8");
    std::map<std::string, std::string> files;
    files["model.smv"] = render(model);
    json::Object symbols, steps, properties, origin;
    for (const auto& [key, variable] : model.variables())
        symbols[symbolName(key)] = json::Object{{"key_hex", hexKey(key)}, {"type", typeText(variable.symbol->type)}};
    for (const auto& [key, step] : model.steps())
        steps[hexKey(key)] = json::Object{{"key_hex", hexKey(key)}, {"guard", renderExpr(step.guard)}};
    for (const auto& [key, expr] : model.properties())
        properties[propertyName(key)] = json::Object{{"key_hex", hexKey(key)}, {"expression", renderExpr(expr)}};
    for (const auto& [key, value] : provenance) {
        if (!json::isUTF8(key) || !json::isUTF8(value)) throw ModelError("Provenance must be UTF-8");
        origin[key] = value;
    }
    files["source-map.json"] = jsonText(json::Object{{"version", 1}, {"symbols", std::move(symbols)}, {"steps", std::move(steps)}});
    files["properties.json"] = jsonText(json::Object{{"version", 1}, {"properties", std::move(properties)}});
    files["provenance.json"] = jsonText(json::Object{{"version", 1}, {"llvm_version", LLVM_VERSION_STRING},
        {"scope", scope}, {"origin", std::move(origin)}});
    std::string identity = "llvm2smv-model-v1\n";
    json::Object hashes;
    for (const auto& [name, content] : files) {
        auto digest = sha256(content);
        hashes[name] = digest;
        identity += name + "\n" + digest + "\n";
    }
    files["manifest.json"] = jsonText(json::Object{{"version", 1}, {"artifact_id", sha256(identity)}, {"files", std::move(hashes)}});
    json::Object result;
    for (const auto& [name, content] : files) result[name] = content;
    return json::Object{{"version", 1}, {"files", std::move(result)}};
}
} // namespace llvm2smv::ts
