#include "llvm2smv/model_writer.hh"
#include "llvm/Support/FormatVariadic.h"
#include <functional>
#include <iostream>

using namespace llvm2smv::ts;
namespace {
Expr word(unsigned width, uint64_t bits, bool sign = false)
{ return Expr::integer(Type::word(width, sign), llvm::APInt(width, bits)); }
Expr value(SymbolRef s) { return Expr::variable(s); }
Expr eq(Expr a, Expr b) { return Expr::binary(Op::Equal, a, b); }
void check(bool ok) { if (!ok) throw std::runtime_error("Self-test assertion failed"); }
void rejects(std::function<void()> f)
{
    try { f(); } catch (const ModelError&) { return; }
    throw std::runtime_error("Invalid model/expression was accepted");
}
Model fixture(const std::string& name)
{
    Model m;
    if (name == "sequence" || name == "sequence-reverse") {
        auto pcType = Type::enumeration("pc", {"start", "second", "done"});
        auto literal = [&](const char* s) { return Expr::literal(pcType, s); };
        SymbolRef pc, x, y;
        if (name == "sequence") {
            pc = m.variable("pc", pcType, Mode::State, literal("start"));
            x = m.variable("x", Type::word(8), Mode::State, word(8, 0));
            y = m.variable("y", Type::word(8), Mode::State, word(8, 0));
        } else {
            y = m.variable("y", Type::word(8), Mode::State, word(8, 0));
            x = m.variable("x", Type::word(8), Mode::State, word(8, 0));
            pc = m.variable("pc", pcType, Mode::State, literal("start"));
        }
        m.variable("unchanged", Type::word(8), Mode::State, word(8, 7));
        m.variable("immutable", Type::word(8), Mode::Frozen, word(8, 9));
        auto first = [&] { m.step("first", eq(value(pc), literal("start")),
            {{x, Expr::binary(Op::Add, value(x), word(8, 1))}, {pc, literal("second")}}); };
        auto second = [&] { m.step("second", eq(value(pc), literal("second")),
            {{y, Expr::binary(Op::Mul, value(x), word(8, 2))}, {pc, literal("done")}}); };
        if (name == "sequence") { first(); second(); } else { second(); first(); }
        m.property("done", eq(value(pc), literal("done")));
        m.property("false", Expr::boolean(false));
    } else if (name == "swap") {
        auto x = m.variable("x", Type::word(8), Mode::State, word(8, 1));
        auto y = m.variable("y", Type::word(8), Mode::State, word(8, 2));
        m.step("swap", Expr::boolean(true), {{y, value(x)}, {x, value(y)}});
    } else if (name == "constants") {
        for (unsigned width : {1, 8, 16, 32, 64}) {
            auto u = Type::word(width), s = Type::word(width, true);
            m.variable("u" + std::to_string(width), u, Mode::Frozen,
                Expr::integer(u, llvm::APInt::getAllOnes(width)));
            m.variable("s" + std::to_string(width), s, Mode::Frozen,
                Expr::integer(s, llvm::APInt::getSignedMinValue(width)));
        }
        m.variable("boolean", Type::boolean(), Mode::Frozen, Expr::boolean(true));
        m.variable("truncated", Type::word(1), Mode::Frozen, Expr::cast(Type::word(1), word(8, 254)));
        m.variable("signed_extension", Type::word(16), Mode::Frozen, Expr::cast(Type::word(16), word(8, 255, true)));
        m.variable("zero_extension", Type::word(16), Mode::Frozen, Expr::cast(Type::word(16), word(8, 255)));
    } else if (name == "operators") {
        auto a = m.variable("a", Type::word(8), Mode::Frozen, word(8, 5));
        auto b = m.variable("b", Type::word(8), Mode::Frozen, word(8, 2));
        auto add = [&](std::string key, Expr expression) {
            m.variable(std::move(key), expression.type(), Mode::Frozen, expression);
        };
        for (auto [key, op] : std::vector<std::pair<std::string, Op>>{
                {"add", Op::Add}, {"sub", Op::Sub}, {"mul", Op::Mul}, {"div", Op::Div},
                {"rem", Op::Rem}, {"and", Op::BitAnd}, {"or", Op::BitOr}, {"xor", Op::BitXor},
                {"shl", Op::ShiftLeft}, {"shr", Op::ShiftRight}, {"eq", Op::Equal},
                {"ne", Op::NotEqual}, {"lt", Op::Less}, {"le", Op::LessEqual},
                {"gt", Op::Greater}, {"ge", Op::GreaterEqual}})
            add(key, Expr::binary(op, value(a), value(b)));
        add("not", Expr::unary(Op::BitNot, value(a)));
        add("neg", Expr::unary(Op::Negate, value(a)));
        add("select", Expr::select(Expr::binary(Op::Greater, value(a), value(b)), value(a), value(b)));
        add("signed_less", Expr::binary(Op::Less, word(8, 255, true), word(8, 0, true)));
        add("unsigned_less", Expr::binary(Op::Less, word(8, 255), word(8, 0)));
        for (auto [key, op] : std::vector<std::pair<std::string, Op>>{
                {"bool_and", Op::And}, {"bool_or", Op::Or}, {"bool_xor", Op::Xor}})
            add(key, Expr::binary(op, Expr::boolean(true), Expr::boolean(false)));
        add("bool_not", Expr::unary(Op::Not, Expr::boolean(true)));
    } else if (name == "arrays") {
        auto a = m.variable("a", Type::array(Type::word(8), 2), Mode::State,
            Expr::array({word(8, 1), word(8, 2)}));
        m.variable("b", Type::array(Type::boolean(), 2), Mode::Frozen,
            Expr::array({Expr::boolean(true), Expr::boolean(false)}));
        m.step("swap", Expr::boolean(true), {{a, Expr::array({Expr::index(value(a), 1), Expr::index(value(a), 0)})}});
    } else if (name == "choice") {
        auto x = m.variable("a_state", Type::boolean(), Mode::State, Expr::boolean(false));
        auto choice = m.variable("z_choice", Type::boolean(), Mode::Choice, std::nullopt);
        m.step("sample", Expr::boolean(true), {{x, value(choice)}});
    } else if (name == "overlap") {
        auto x = m.variable("x", Type::boolean(), Mode::State, Expr::boolean(false));
        m.step("a", Expr::boolean(true), {{x, Expr::boolean(true)}});
        m.step("b", Expr::boolean(true), {{x, Expr::boolean(false)}});
    } else if (name == "names") {
        for (const auto& key : {std::string("a-b"), std::string("a_b"), std::string("MODULE"),
                std::string("x;\nINIT FALSE;"), std::string("\xff\0", 2)})
            m.variable(key, Type::boolean(), Mode::Frozen, Expr::boolean(true));
    } else throw std::runtime_error("Unknown fixture: " + name);
    return m;
}
void selfTests()
{
    for (auto width : {0U, 65U}) rejects([&] { Type::word(width); });
    rejects([] { Type::enumeration("e", {"a", "a"}); });
    rejects([] { Type::array(Type::boolean(), 0); });
    rejects([] { Expr::integer(Type::word(8), llvm::APInt(16, 0)); });
    rejects([] { Expr::binary(Op::Add, word(8, 0), word(16, 0)); });
    rejects([] { Expr::binary(Op::Add, word(8, 0), word(8, 0, true)); });
    rejects([] { eq(Expr::boolean(true), word(1, 1)); });
    rejects([] { Expr::cast(Type::word(1), Expr::boolean(true)); });
    rejects([] { Expr::index(Expr::array({word(8, 0)}), 1); });
    rejects([] { Expr::array({word(8, 0), word(16, 0)}); });
    rejects([] { Expr::select(word(1, 1), word(8, 0), word(8, 0)); });
    rejects([] { Expr::unary(Op::Add, word(8, 0)); });
    rejects([] { Expr::binary(Op::Not, word(8, 0), word(8, 0)); });
    Model m;
    auto x = m.variable("x", Type::boolean(), Mode::State, Expr::boolean(false));
    rejects([&] { m.variable("x", Type::boolean(), Mode::State, std::nullopt); });
    rejects([&] { m.variable("bad", Type::boolean(), Mode::Choice, Expr::boolean(false)); });
    rejects([&] { m.step("bad", Expr::boolean(true), {{x, value(x)}, {x, value(x)}}); });
    for (auto mode : {Mode::Frozen, Mode::Choice}) {
        Model other;
        auto v = other.variable("x", Type::boolean(), mode, std::nullopt);
        rejects([&] { other.step("bad", Expr::boolean(true), {{v, value(v)}}); });
    }
    Model other;
    auto foreign = other.variable("x", Type::boolean(), Mode::State, std::nullopt);
    m.property("foreign", value(foreign));
    rejects([&] { m.validate(); });
    Model missing;
    missing.variable("x", Type::boolean(), Mode::State, std::nullopt);
    auto undeclared = Type::enumeration("missing", {"a", "b"});
    missing.property("bad", eq(Expr::literal(undeclared, "a"), Expr::literal(undeclared, "b")));
    rejects([&] { missing.validate(); });
    Model targetModel;
    targetModel.variable("x", Type::boolean(), Mode::State, std::nullopt);
    targetModel.step("foreign", Expr::boolean(true), {{foreign, Expr::boolean(true)}});
    rejects([&] { targetModel.validate(); });
    Model enums;
    enums.variable("a", Type::enumeration("e", {"a"}), Mode::Frozen, std::nullopt);
    enums.variable("b", Type::enumeration("e", {"b"}), Mode::Frozen, std::nullopt);
    rejects([&] { enums.validate(); });
    check(symbolName("a-b") != symbolName("a_b"));
    check(symbolName("x") != propertyName("x"));
    check(render(fixture("sequence")) == render(fixture("sequence-reverse")));
    check(llvm::formatv("{0:2}", llvm::json::Value(artifact(fixture("sequence"), {}))).str()
        == llvm::formatv("{0:2}", llvm::json::Value(artifact(fixture("sequence-reverse"), {}))).str());
}
}
int main(int argc, char** argv)
{
    try {
        if (argc == 1) { selfTests(); std::cout << "Typed model self-tests passed\n"; }
        else if (argc == 3 && std::string(argv[1]) == "--fixture")
            std::cout << llvm::formatv("{0:2}\n", llvm::json::Value(artifact(fixture(argv[2]), {{"producer", "M1 fixtures"}}))).str();
        else throw std::runtime_error("Usage: llvm2smv_model_tests [--fixture NAME]");
        return 0;
    } catch (const std::exception& e) { std::cerr << e.what() << '\n'; return 1; }
}
