#ifndef LLVM2SMV_TRANSITION_SYSTEM_HH
#define LLVM2SMV_TRANSITION_SYSTEM_HH

#include "llvm/ADT/APInt.h"
#include <map>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <vector>

namespace llvm2smv::ts {

class ModelError : public std::runtime_error {
public:
    using std::runtime_error::runtime_error;
};

class Type {
public:
    enum class Kind { Boolean, Word, Enum, Array };
    static Type boolean();
    static Type word(unsigned width, bool isSigned = false);
    static Type enumeration(std::string key, std::vector<std::string> literals);
    static Type array(Type element, unsigned count);
    Kind kind() const { return kind_; }
    unsigned width() const { return width_; }
    bool isSigned() const { return signed_; }
    const std::string& key() const { return key_; }
    const std::vector<std::string>& literals() const { return literals_; }
    const Type& element() const;
    unsigned count() const { return count_; }
    bool operator==(const Type& other) const;
    bool operator!=(const Type& other) const { return !(*this == other); }
private:
    explicit Type(Kind kind) : kind_(kind) {}
    Kind kind_;
    unsigned width_ = 0, count_ = 0;
    bool signed_ = false;
    std::string key_;
    std::vector<std::string> literals_;
    std::shared_ptr<const Type> element_;
};

enum class Mode { State, Frozen, Choice };
struct Symbol {
    const std::string key;
    const Type type;
    const Mode mode;
};
using SymbolRef = std::shared_ptr<const Symbol>;

enum class Op {
    Not, BitNot, Negate, And, Or, Xor, Equal, NotEqual,
    Less, LessEqual, Greater, GreaterEqual, Add, Sub, Mul, Div, Rem,
    BitAnd, BitOr, BitXor, ShiftLeft, ShiftRight
};

class Expr {
public:
    enum class Kind { Boolean, Integer, Literal, Variable, Unary, Binary, Cast, Select, Array, Index };
    static Expr boolean(bool value);
    static Expr integer(Type type, llvm::APInt bits);
    static Expr literal(Type type, std::string literal);
    static Expr variable(SymbolRef symbol);
    static Expr unary(Op op, Expr operand);
    static Expr binary(Op op, Expr lhs, Expr rhs);
    static Expr cast(Type destination, Expr operand);
    static Expr select(Expr condition, Expr yes, Expr no);
    static Expr array(std::vector<Expr> elements);
    // M1 exposes constant indices only. Dynamic memory accesses belong to M4.
    static Expr index(Expr array, unsigned index);
    Kind kind() const;
    const Type& type() const;
    Op op() const;
    bool booleanValue() const;
    const llvm::APInt& bits() const;
    const std::string& literalValue() const;
    const SymbolRef& symbol() const;
    const std::vector<Expr>& operands() const;
    unsigned indexValue() const;
private:
    struct Node;
    explicit Expr(Node node);
    std::shared_ptr<const Node> node_;
};

struct Variable { SymbolRef symbol; std::optional<Expr> initial; };
struct Write { SymbolRef target; Expr value; };
struct Step { std::string key; Expr guard; std::vector<Write> writes; };

class Model {
public:
    // nullopt is an explicit choice of unconstrained initialization.
    SymbolRef variable(std::string key, Type type, Mode mode, std::optional<Expr> initial);
    void step(std::string key, Expr guard, std::vector<Write> writes);
    void invariant(std::string key, Expr expression);
    void property(std::string key, Expr expression);
    void validate() const;
    const std::map<std::string, Variable>& variables() const { return variables_; }
    const std::map<std::string, Step>& steps() const { return steps_; }
    const std::map<std::string, Expr>& invariants() const { return invariants_; }
    const std::map<std::string, Expr>& properties() const { return properties_; }
private:
    void validateExpr(const Expr& expr) const;
    std::map<std::string, Variable> variables_;
    std::map<std::string, Step> steps_;
    std::map<std::string, Expr> invariants_, properties_;
};

// Injective byte encoding: independent of allocation/insertion order and locale.
std::string symbolName(const std::string& key);
std::string literalName(const Type& type, const std::string& literal);
std::string propertyName(const std::string& key);
std::string hexKey(const std::string& key);

} // namespace llvm2smv::ts
#endif
