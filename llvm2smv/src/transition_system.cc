#include "llvm2smv/transition_system.hh"
#include <algorithm>
#include <climits>
#include <set>

namespace llvm2smv::ts {
namespace {
void require(bool condition, const char* message)
{
    if (!condition) throw ModelError(message);
}
}

Type Type::boolean() { return Type(Kind::Boolean); }
Type Type::word(unsigned width, bool isSigned)
{
    require(width >= 1 && width <= 64, "Word width must be in 1..64");
    Type result(Kind::Word);
    result.width_ = width;
    result.signed_ = isSigned;
    return result;
}
Type Type::enumeration(std::string key, std::vector<std::string> literals)
{
    require(!key.empty() && !literals.empty(), "Enum key and domain must not be empty");
    std::sort(literals.begin(), literals.end());
    require(std::adjacent_find(literals.begin(), literals.end()) == literals.end(), "Duplicate enum literal");
    require(!literals.front().empty(), "Empty enum literal");
    Type result(Kind::Enum);
    result.key_ = std::move(key);
    result.literals_ = std::move(literals);
    return result;
}
Type Type::array(Type element, unsigned count)
{
    require(element.kind() == Kind::Boolean || element.kind() == Kind::Word,
            "M1 arrays require Boolean or word elements");
    require(count > 0 && count <= INT_MAX, "Invalid array size");
    Type result(Kind::Array);
    result.element_ = std::make_shared<const Type>(std::move(element));
    result.count_ = count;
    return result;
}
const Type& Type::element() const
{
    require(kind_ == Kind::Array, "Element type requested on non-array");
    return *element_;
}
bool Type::operator==(const Type& other) const
{
    return kind_ == other.kind_ && width_ == other.width_ && signed_ == other.signed_
        && key_ == other.key_ && literals_ == other.literals_ && count_ == other.count_
        && (kind_ != Kind::Array || *element_ == *other.element_);
}

struct Expr::Node {
    Kind kind;
    Type type;
    Op op = Op::Equal;
    bool boolean = false;
    llvm::APInt bits = llvm::APInt(1, 0);
    std::string literal;
    SymbolRef symbol;
    std::vector<Expr> operands;
    unsigned index = 0;
    Node(Kind kind, Type type) : kind(kind), type(std::move(type)) {}
};
Expr::Expr(Node node) : node_(std::make_shared<const Node>(std::move(node))) {}
Expr::Kind Expr::kind() const { return node_->kind; }
const Type& Expr::type() const { return node_->type; }
Op Expr::op() const { return node_->op; }
bool Expr::booleanValue() const { return node_->boolean; }
const llvm::APInt& Expr::bits() const { return node_->bits; }
const std::string& Expr::literalValue() const { return node_->literal; }
const SymbolRef& Expr::symbol() const { return node_->symbol; }
const std::vector<Expr>& Expr::operands() const { return node_->operands; }
unsigned Expr::indexValue() const { return node_->index; }
Expr Expr::boolean(bool value)
{
    Node result(Kind::Boolean, Type::boolean()); result.boolean = value; return Expr(std::move(result));
}
Expr Expr::integer(Type type, llvm::APInt bits)
{
    require(type.kind() == Type::Kind::Word && type.width() == bits.getBitWidth(), "Integer constant width/type mismatch");
    Node result(Kind::Integer, std::move(type)); result.bits = std::move(bits); return Expr(std::move(result));
}
Expr Expr::literal(Type type, std::string literal)
{
    require(type.kind() == Type::Kind::Enum, "Enum literal requires enum type");
    require(std::find(type.literals().begin(), type.literals().end(), literal) != type.literals().end(), "Unknown enum literal");
    Node result(Kind::Literal, std::move(type)); result.literal = std::move(literal); return Expr(std::move(result));
}
Expr Expr::variable(SymbolRef symbol)
{
    require(bool(symbol), "Null symbol");
    Node result(Kind::Variable, symbol->type); result.symbol = std::move(symbol); return Expr(std::move(result));
}
Expr Expr::unary(Op op, Expr operand)
{
    require((op == Op::Not && operand.type().kind() == Type::Kind::Boolean)
        || ((op == Op::BitNot || op == Op::Negate) && operand.type().kind() == Type::Kind::Word), "Invalid unary operator/type");
    Node result(Kind::Unary, operand.type()); result.op = op;
    result.operands.push_back(std::move(operand)); return Expr(std::move(result));
}
Expr Expr::binary(Op op, Expr lhs, Expr rhs)
{
    require(lhs.type() == rhs.type(), "Binary operands require identical types; cast explicitly");
    bool equality = op == Op::Equal || op == Op::NotEqual;
    bool logical = op == Op::And || op == Op::Or || op == Op::Xor;
    bool relation = op == Op::Less || op == Op::LessEqual || op == Op::Greater || op == Op::GreaterEqual;
    bool arithmetic = op >= Op::Add && op <= Op::ShiftRight;
    require(equality || (logical && lhs.type().kind() == Type::Kind::Boolean)
        || ((relation || arithmetic) && lhs.type().kind() == Type::Kind::Word), "Invalid binary operator/type");
    Node result(Kind::Binary, (equality || logical || relation) ? Type::boolean() : lhs.type());
    result.op = op; result.operands = {std::move(lhs), std::move(rhs)}; return Expr(std::move(result));
}
Expr Expr::cast(Type destination, Expr operand)
{
    require(destination.kind() == Type::Kind::Word && operand.type().kind() == Type::Kind::Word,
            "Cast requires word types; Boolean conversions must be explicit expressions");
    Node result(Kind::Cast, std::move(destination)); result.operands.push_back(std::move(operand)); return Expr(std::move(result));
}
Expr Expr::select(Expr condition, Expr yes, Expr no)
{
    require(condition.type().kind() == Type::Kind::Boolean && yes.type() == no.type(), "Invalid conditional types");
    Node result(Kind::Select, yes.type()); result.operands = {std::move(condition), std::move(yes), std::move(no)};
    return Expr(std::move(result));
}
Expr Expr::array(std::vector<Expr> elements)
{
    require(!elements.empty() && elements.size() <= INT_MAX, "Invalid array literal size");
    Type element = elements.front().type();
    for (const auto& expr : elements) require(expr.type() == element, "Array literal element type mismatch");
    Node result(Kind::Array, Type::array(element, elements.size()));
    result.operands = std::move(elements); return Expr(std::move(result));
}
Expr Expr::index(Expr array, unsigned index)
{
    require(array.type().kind() == Type::Kind::Array && index < array.type().count(), "Invalid constant array index");
    Node result(Kind::Index, array.type().element()); result.index = index;
    result.operands.push_back(std::move(array)); return Expr(std::move(result));
}

SymbolRef Model::variable(std::string key, Type type, Mode mode, std::optional<Expr> initial)
{
    require(!key.empty() && !variables_.count(key), "Empty or duplicate variable key");
    require(!initial || initial->type() == type, "Initial value type mismatch");
    require(mode != Mode::Choice || !initial, "Choice variables cannot have a one-time initializer");
    auto symbol = std::make_shared<const Symbol>(Symbol{key, std::move(type), mode});
    variables_.emplace(key, Variable{symbol, std::move(initial)});
    return symbol;
}
void Model::step(std::string key, Expr guard, std::vector<Write> writes)
{
    require(!key.empty() && !steps_.count(key), "Empty or duplicate step key");
    require(guard.type().kind() == Type::Kind::Boolean && !writes.empty(), "Step requires Boolean guard and writes");
    std::set<std::string> targets;
    for (const auto& write : writes) {
        require(bool(write.target), "Null assignment target");
        require(write.target->mode == Mode::State, "Only state variables may be assigned");
        require(write.value.type() == write.target->type, "Assignment type mismatch");
        require(targets.insert(write.target->key).second, "Duplicate simultaneous assignment target");
    }
    std::sort(writes.begin(), writes.end(), [](const Write& a, const Write& b) { return a.target->key < b.target->key; });
    steps_.emplace(key, Step{key, std::move(guard), std::move(writes)});
}
void Model::invariant(std::string key, Expr expression)
{
    require(!key.empty() && !invariants_.count(key), "Empty or duplicate invariant key");
    require(expression.type().kind() == Type::Kind::Boolean, "Invariant must be Boolean");
    invariants_.emplace(std::move(key), std::move(expression));
}
void Model::property(std::string key, Expr expression)
{
    require(!key.empty() && !properties_.count(key), "Empty or duplicate property key");
    require(expression.type().kind() == Type::Kind::Boolean, "Property must be Boolean");
    properties_.emplace(std::move(key), std::move(expression));
}
void Model::validateExpr(const Expr& expr) const
{
    if (expr.type().kind() == Type::Kind::Enum) {
        bool declared = false;
        for (const auto& [key, variable] : variables_)
            declared |= variable.symbol->type == expr.type();
        require(declared, "Expression uses an undeclared enum type");
    }
    if (expr.kind() == Expr::Kind::Variable) {
        auto found = variables_.find(expr.symbol()->key);
        require(found != variables_.end() && found->second.symbol == expr.symbol(), "Expression references a foreign/undeclared symbol");
    }
    for (const auto& operand : expr.operands()) validateExpr(operand);
}
void Model::validate() const
{
    require(!variables_.empty(), "Model must declare state");
    std::map<std::string, Type> enums;
    for (const auto& [key, variable] : variables_) {
        const auto& type = variable.symbol->type;
        if (type.kind() == Type::Kind::Enum) {
            auto found = enums.find(type.key());
            require(found == enums.end() || found->second == type, "Enum key has incompatible domains");
            enums.emplace(type.key(), type);
        }
        if (variable.initial) validateExpr(*variable.initial);
    }
    for (const auto& [key, step] : steps_) {
        validateExpr(step.guard);
        for (const auto& write : step.writes) {
            auto found = variables_.find(write.target->key);
            require(found != variables_.end() && found->second.symbol == write.target, "Assignment targets a foreign/undeclared symbol");
            validateExpr(write.value);
        }
    }
    for (const auto& [key, expr] : invariants_) validateExpr(expr);
    for (const auto& [key, expr] : properties_) validateExpr(expr);
}

std::string hexKey(const std::string& key)
{
    static const char* digits = "0123456789abcdef";
    std::string result;
    for (unsigned char c : key) { result += digits[c >> 4]; result += digits[c & 15]; }
    return result;
}
std::string symbolName(const std::string& key) { return "v_" + hexKey(key); }
std::string literalName(const Type& type, const std::string& literal)
{
    return "e_" + hexKey(type.key()) + "_" + hexKey(literal);
}
std::string propertyName(const std::string& key) { return "p_" + hexKey(key); }
} // namespace llvm2smv::ts
