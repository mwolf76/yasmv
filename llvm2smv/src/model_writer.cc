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
bool sameConstant(const Expr& a, const Expr& b)
{
    if (a.kind() != b.kind() || a.type() != b.type()) return false;
    if (a.kind() == Expr::Kind::Boolean) return a.booleanValue() == b.booleanValue();
    if (a.kind() == Expr::Kind::Integer) return a.bits() == b.bits();
    if (a.kind() == Expr::Kind::Literal) return a.literalValue() == b.literalValue();
    return false;
}
std::optional<Expr> constantValue(const Expr& e, const std::map<std::string, Expr>& constants)
{
    using K = Expr::Kind;
    if (e.kind() == K::Boolean || e.kind() == K::Integer || e.kind() == K::Literal) return e;
    if (e.kind() == K::Variable) {
        auto found = constants.find(e.symbol()->key);
        return found == constants.end() ? std::nullopt : std::optional<Expr>(found->second);
    }
    auto a = constantValue(e.operands()[0], constants);
    if (e.kind() == K::Cast && a) {
        auto bits = a->type().isSigned() ? a->bits().sextOrTrunc(e.type().width()) : a->bits().zextOrTrunc(e.type().width());
        return Expr::integer(e.type(), bits);
    }
    if (e.kind() == K::Unary && a) {
        if (e.op() == Op::Not) return Expr::boolean(!a->booleanValue());
        return Expr::integer(e.type(), e.op() == Op::Negate ? -a->bits() : ~a->bits());
    }
    if (e.kind() == K::Select) {
        if (a) return constantValue(e.operands()[a->booleanValue() ? 1 : 2], constants);
        auto yes = constantValue(e.operands()[1], constants), no = constantValue(e.operands()[2], constants);
        return yes && no && sameConstant(*yes, *no) ? yes : std::nullopt;
    }
    if (e.kind() != K::Binary) return std::nullopt;
    auto b = constantValue(e.operands()[1], constants);
    if (e.op() == Op::And || e.op() == Op::Or) {
        bool absorbing = e.op() == Op::Or;
        if ((a && a->booleanValue() == absorbing) || (b && b->booleanValue() == absorbing)) return Expr::boolean(absorbing);
    }
    if (!a || !b) return std::nullopt;
    if (e.op() == Op::Equal || e.op() == Op::NotEqual)
        return Expr::boolean(sameConstant(*a, *b) == (e.op() == Op::Equal));
    if (a->kind() == K::Boolean) {
        bool x = a->booleanValue(), y = b->booleanValue();
        return Expr::boolean(e.op() == Op::And ? x && y : e.op() == Op::Or ? x || y : x != y);
    }
    auto x = a->bits(), y = b->bits(); bool sign = a->type().isSigned();
    switch (e.op()) {
    case Op::Less: return Expr::boolean(sign ? x.slt(y) : x.ult(y));
    case Op::LessEqual: return Expr::boolean(sign ? x.sle(y) : x.ule(y));
    case Op::Greater: return Expr::boolean(sign ? x.sgt(y) : x.ugt(y));
    case Op::GreaterEqual: return Expr::boolean(sign ? x.sge(y) : x.uge(y));
    case Op::Add: return Expr::integer(e.type(), x + y);
    case Op::Sub: return Expr::integer(e.type(), x - y);
    case Op::Mul: return Expr::integer(e.type(), x * y);
    case Op::BitAnd: return Expr::integer(e.type(), x & y);
    case Op::BitOr: return Expr::integer(e.type(), x | y);
    case Op::BitXor: return Expr::integer(e.type(), x ^ y);
    // Leave division and shifts to the backend, including exceptional operands.
    default: return std::nullopt;
    }
}

std::string jsonText(llvm::json::Object object)
{
    return llvm::formatv("{0:2}\n", llvm::json::Value(std::move(object))).str();
}
}

static std::string renderExpr(const Expr& expr, const std::map<std::string, Expr>& constants)
{
    if (!constants.empty())
        if (auto folded = constantValue(expr, constants)) return renderExpr(*folded, {});
    const auto& operands = expr.operands();
    switch (expr.kind()) {
    case Expr::Kind::Boolean: return expr.booleanValue() ? "TRUE" : "FALSE";
    case Expr::Kind::Integer: {
        llvm::SmallString<32> digits;
        expr.bits().toString(digits, 16, false);
        return "((" + typeText(expr.type()) + ") 0x" + digits.str().str() + ")";
    }
    case Expr::Kind::Literal: return literalName(expr.type(), expr.literalValue());
    case Expr::Kind::Variable: {
        auto found = constants.find(expr.symbol()->key);
        return found == constants.end() ? symbolName(expr.symbol()->key) : renderExpr(found->second, constants);
    }
    case Expr::Kind::Unary: return "(" + std::string(operatorText(expr.op())) + "(" + renderExpr(operands[0], constants) + "))";
    case Expr::Kind::Binary: return "(" + renderExpr(operands[0], constants) + " " + operatorText(expr.op()) + " " + renderExpr(operands[1], constants) + ")";
    case Expr::Kind::Cast: return "((" + typeText(expr.type()) + ") (" + renderExpr(operands[0], constants) + "))";
    case Expr::Kind::Select: return "(" + renderExpr(operands[0], constants) + " ? " + renderExpr(operands[1], constants) + " : " + renderExpr(operands[2], constants) + ")";
    case Expr::Kind::Array: {
        std::string result = "[";
        for (const auto& operand : operands) {
            if (result != "[") result += ", ";
            result += renderExpr(operand, constants);
        }
        return result + "]";
    }
    case Expr::Kind::Index: return "(" + renderExpr(operands[0], constants) + ")[" + std::to_string(expr.indexValue()) + "]";
    }
    throw ModelError("Unknown expression");
}

std::string renderExpr(const Expr& expr) { return renderExpr(expr, {}); }

std::string render(const Model& model)
{
    model.validate();
    std::set<std::string> writers;
    for (const auto& [key, step] : model.steps())
        for (const auto& write : step.writes) writers.insert(write.target->key);
    // Find inductively constant slots: initialized literals whose every write
    // preserves that value. Removing candidates to a fixed point is necessary
    // when one slot depends on another. No guard assumptions or path pruning.
    // Keep declarations/initializers so trace identities remain unchanged.
    std::map<std::string, Expr> constants;
    for (const auto& [key, variable] : model.variables()) {
        if (variable.symbol->mode == Mode::Choice || !variable.initial) continue;
        auto kind = variable.initial->kind();
        if (kind == Expr::Kind::Boolean || kind == Expr::Kind::Integer || kind == Expr::Kind::Literal)
            constants.emplace(key, *variable.initial);
    }
    bool changed;
    do {
        changed = false;
        for (const auto& [key, step] : model.steps()) for (const auto& write : step.writes) {
            auto found = constants.find(write.target->key);
            if (found == constants.end()) continue;
            auto value = constantValue(write.value, constants);
            if (!value || !sameConstant(*value, found->second)) {
                constants.erase(found);
                changed = true;
            }
        }
    } while (changed);
    std::ostringstream output;
    output << "-- llvm2smv typed model v1; no C/LLVM equivalence claim\n#word-width 64\nMODULE main\n";
    for (const auto& [key, variable] : model.variables()) {
        if (variable.symbol->mode != Mode::Choice)
            output << (writers.count(key) ? "#inertial\n" : "#frozen\n");
        output << "VAR " << symbolName(key) << " : " << typeText(variable.symbol->type) << ";\n";
    }
    for (const auto& [key, variable] : model.variables())
        if (variable.initial) output << "INIT (" << symbolName(key) << " = " << renderExpr(*variable.initial, constants) << ");\n";
    for (const auto& [key, expression] : model.invariants()) output << "INVAR " << renderExpr(expression, constants) << ";\n";
    for (const auto& [key, step] : model.steps()) {
        output << "TRANS " << renderExpr(step.guard, constants) << " ?: ";
        bool first = true;
        for (const auto& write : step.writes) {
            if (!first) output << ", ";
            output << symbolName(write.target->key) << " := " << renderExpr(write.value, constants);
            first = false;
        }
        output << ";\n";
    }
    for (const auto& [key, expression] : model.properties())
        output << "DEFINE " << propertyName(key) << " := " << renderExpr(expression, constants) << ";\n";
    return output.str();
}

std::string sha256(const std::string& bytes)
{
    llvm::SHA256 hash;
    hash.update(bytes);
    auto digest = hash.final();
    return hexKey(std::string(reinterpret_cast<const char*>(digest.data()), digest.size()));
}

llvm::json::Object artifact(const Model& model, const std::map<std::string, std::string>& provenance, const std::string& scope, llvm::json::Object locations, llvm::json::Object memory)
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
    files["source-map.json"] = jsonText(json::Object{{"version", 1}, {"symbols", std::move(symbols)}, {"steps", std::move(steps)}, {"locations", std::move(locations)}, {"memory", std::move(memory)}});
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
