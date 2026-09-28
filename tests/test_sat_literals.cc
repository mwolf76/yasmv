// This executable deliberately links no SAT solver or yasmv library.
#include <sat/literal.hh>

#include <algorithm>
#include <iostream>
#include <type_traits>

#ifdef Minisat_SolverTypes_h
#error "The public literal header must not depend on MiniSat"
#endif

static_assert(sizeof(sat::Lit) == sizeof(int));
static_assert(std::is_trivially_copyable_v<sat::Lit>);
static_assert(!std::is_convertible_v<int, sat::Lit>);
static_assert(sat::toInt(sat::mkLit(0)) == 0);
static_assert(sat::toInt(~sat::mkLit(0)) == 1);
static_assert(sat::toInt(sat::mkLit(sat::MAX_VAR, true)) == std::numeric_limits<int>::max());

namespace {
void check(bool condition)
{
    if (!condition) throw std::runtime_error("SAT literal contract failed");
}

void round_trip(int packed)
{
    const auto literal = sat::toLit(packed);
    check(sat::toInt(literal) == packed);
    check(sat::var(literal) == packed / 2);
    check(sat::sign(literal) == bool(packed % 2));
    check(sat::mkLit(packed / 2, packed % 2) == literal);
    check(sat::toInt(~literal) == (packed ^ 1));
    check(~~literal == literal);
    check((literal ^ true) == ~literal);
    check((literal ^ false) == literal);
}

template<class F> void rejects(F operation)
{
    bool rejected = false;
    try { operation(); }
    catch (const std::out_of_range&) { rejected = true; }
    check(rejected);
}
}

int main()
{
    try {
        for (int packed = 0; packed < 65536; ++packed) round_trip(packed);
        round_trip(std::numeric_limits<int>::max());
        round_trip(std::numeric_limits<int>::max() - 1);
        rejects([] { sat::toLit(-1); });
        rejects([] { sat::toLit(std::numeric_limits<int>::min()); });
        rejects([] { sat::mkLit(-1); });
        rejects([] { sat::mkLit(sat::MAX_VAR + 1); });
        rejects([] { sat::mkLit(std::numeric_limits<int>::max(), true); });

        sat::Lits literals {sat::toLit(3), sat::toLit(0), sat::toLit(2), sat::toLit(1)};
        const auto original = literals;
        std::sort(literals.begin(), literals.end());
        for (int packed = 0; packed < 4; ++packed)
            check(sat::toInt(literals[packed]) == packed);
        check(sat::toInt(original.front()) == 3);
        sat::LitsVector clauses {literals, {}};
        literals.clear();
        check(clauses.front().size() == 4 && clauses.back().empty());
        std::cout << "SAT literal contracts passed (65,538 round trips, bounds, containers)\n";
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
