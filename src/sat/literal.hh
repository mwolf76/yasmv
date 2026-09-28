// Solver-independent literals. The packed representation is also the arithmetic
// microcode format: 2 * zero-based variable + sign (1 means negated).
#ifndef SAT_LITERAL_H
#define SAT_LITERAL_H

#include <limits>
#include <stdexcept>
#include <vector>

namespace sat {

using Var = int;
inline constexpr Var MAX_VAR = std::numeric_limits<int>::max() / 2;

class Lit {
    int packed_;
    explicit constexpr Lit(int packed) : packed_(packed) {}
    friend constexpr Lit toLit(int);
    friend constexpr int toInt(Lit);

public:
    constexpr bool operator==(const Lit&) const = default;
    constexpr bool operator<(Lit other) const { return packed_ < other.packed_; }
};

constexpr Lit toLit(int packed)
{
    if (packed < 0) throw std::out_of_range("Negative packed SAT literal");
    return Lit(packed);
}

constexpr int toInt(Lit literal) { return literal.packed_; }
constexpr Var var(Lit literal) { return toInt(literal) / 2; }
constexpr bool sign(Lit literal) { return (toInt(literal) & 1) != 0; }

constexpr Lit mkLit(Var variable, bool negative = false)
{
    if (variable < 0 || variable > MAX_VAR)
        throw std::out_of_range("SAT variable exceeds packed literal range");
    return toLit(2 * variable + static_cast<int>(negative));
}

constexpr Lit operator~(Lit literal) { return toLit(toInt(literal) ^ 1); }
constexpr Lit operator^(Lit literal, bool invert) { return toLit(toInt(literal) ^ int(invert)); }

using Lits = std::vector<Lit>;
using LitsVector = std::vector<Lits>;

} // namespace sat
#endif
