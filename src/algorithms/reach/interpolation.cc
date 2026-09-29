#include <algorithms/reach/interpolation.hh>

#include <algorithm>
#include <stdexcept>

namespace reach::interpolation {
namespace {
using namespace sat;
void tick() { query::checkpoint(query::Phase::encoding); }
void notify(const Observer& observer, Event event)
{
    tick();
    if (observer) observer(event);
    tick();
}
enc::TCBI at(const enc::TCBI& bit, step_t frame)
{
    if (frame > LAST_POSITIVE_TIME) throw std::invalid_argument("Interpolation frame exceeds the forward time range");
    return enc::TCBI(enc::UCBI(bit.expr(), bit.time(), bit.bitno()), frame);
}
void validate_bits(const Bits& bits)
{
    TCBI2VarMap seen;
    for (const auto& bit : bits) {
        tick();
        if (!bit.expr() || bit.base() != 0 || (bit.time() != 0 && bit.time() != FROZEN) ||
            !seen.emplace(bit, 0).second)
            throw std::invalid_argument("Interpolation requires distinct canonical state bits");
    }
}
void validate_formula(const System& system, const StateFormula& formula)
{
    validate_bits(system.bits());
    if (system.bits().size() != formula.bits.size()) throw std::invalid_argument("Invariant state dictionary mismatch");
    for (size_t i = 0; i < formula.bits.size(); ++i) {
        tick();
        if (!enc::TCBIEq()(formula.bits[i], system.bits()[i]) ||
            formula.bits[i].time() != system.bits()[i].time() || formula.bits[i].base() != 0)
            throw std::invalid_argument("Invariant state dictionary mismatch");
    }
    for (auto atom : formula.circuit.support(formula.root))
        if (!atom || atom > formula.bits.size()) throw std::invalid_argument("Invariant has foreign state support");
}
void allocate_state(Engine& engine, const Bits& bits, step_t frame)
{
    for (const auto& bit : bits) { tick(); engine.tcbi_to_var(at(bit, frame)); }
}
void emit(Engine& engine, const StateFormula& formula, Circuit::Ref root, step_t frame)
{
    const int top = formula.circuit.encode(root, [&] { return engine.new_sat_var() + 1; },
        [&](Circuit::Atom atom) {
            if (!atom || atom > formula.bits.size()) throw std::invalid_argument("Invariant has foreign state support");
            return engine.tcbi_to_var(at(formula.bits.at(atom - 1), frame)) + 1;
        }, [&](const proof::Clause& clause) {
            Lits literals;
            for (int lit : clause) { tick(); literals.push_back(mkLit(std::abs(lit) - 1, lit < 0)); }
            engine.add_clause(literals);
        });
    engine.add_clause({mkLit(std::abs(top) - 1, top < 0)});
}
Circuit::Ref import(StateFormula& into, const InterpolationResult& from)
{
    if (from.status != STATUS_UNSAT || !from.verified) throw std::logic_error("Cannot import an unverified interpolant");
    TCBI2VarMap indices;
    for (size_t i = 0; i < into.bits.size(); ++i) {
        tick();
        if (i > size_t(MAX_VAR)) throw std::length_error("State dictionary is too large");
        indices.emplace(into.bits[i], static_cast<Var>(i));
    }
    return into.circuit.import(from.circuit, from.root, [&](Circuit::Atom atom) {
        tick();
        const auto& bit = from.state_bits.at(atom);
        const auto found = indices.find(bit);
        if (found == indices.end() || bit.time() != into.bits[found->second].time())
            throw std::invalid_argument("Interpolant refers to a bit outside the system state");
        return static_cast<Circuit::Atom>(found->second) + 1;
    });
}
struct Stopped { Stop reason; };
status_t completed(status_t status)
{
    if (status == STATUS_UNKNOWN) {
        if (auto context = query::current(); context && context->stop != query::StopReason::none)
            throw Stopped{Stop::interrupted};
        throw Stopped{Stop::solver_unknown};
    }
    tick();
    return status;
}
Path decode(Engine& engine, const Bits& bits, unsigned depth)
{
    Path path;
    for (unsigned frame = 0; frame <= depth; ++frame) {
        query::checkpoint(query::Phase::decoding);
        State state;
        for (const auto& bit : bits) {
            query::checkpoint(query::Phase::decoding);
            const auto var = engine.existing_var(at(bit, frame));
            if (!engine.assigned(var)) throw std::logic_error("Concrete path has an unassigned state bit");
            state.push_back(engine.value(var) != 0);
        }
        path.push_back(std::move(state));
    }
    return path;
}
} // namespace

StateFormula::StateFormula(Bits dictionary, size_t node_limit)
    : circuit(tick, node_limit), bits(std::move(dictionary)) {}
void StateFormula::emit(sat::Engine& engine, step_t frame, bool positive) const
{
    interpolation::emit(engine, *this, positive ? root : circuit.negate(root), frame);
}
bool StateFormula::evaluate(const State& state) const
{
    if (state.size() != bits.size()) throw std::invalid_argument("State width mismatch");
    return circuit.evaluate(root, [&](sat::Circuit::Atom atom) {
        if (!atom || atom > state.size()) throw std::invalid_argument("Invariant has foreign state support");
        return state.at(atom - 1);
    });
}

void emit_suffix(const System& system, sat::Engine& engine, step_t first, unsigned horizon)
{
    if (first > LAST_POSITIVE_TIME || horizon > LAST_POSITIVE_TIME - first)
        throw std::invalid_argument("Interpolation suffix exceeds the forward time range");
    auto active = sat::MAINGROUP;
    for (unsigned offset = 0; offset <= horizon; ++offset) {
        tick();
        const auto frame = first + offset;
        if (offset == horizon) { system.target(engine, frame, active); break; }
        const auto stop = engine.new_sat_var(), go = engine.new_sat_var();
        // Raw variables, not Engine groups: only the enclosing branch activates
        // a continuation. No native assumptions force the suffix to its end.
        engine.add_clause({sat::mkLit(active, true), sat::mkLit(stop), sat::mkLit(go)});
        engine.add_clause({sat::mkLit(stop, true), sat::mkLit(active)});
        engine.add_clause({sat::mkLit(go, true), sat::mkLit(active)});
        system.target(engine, frame, stop);
        system.transition(engine, frame, go);
        active = go;
    }
}

sat::status_t verify_invariant(const System& system, const StateFormula& candidate, const Observer& observer)
{
    validate_formula(system, candidate);
    for (auto event : {Event::verify_initial, Event::verify_transition, Event::verify_target}) {
        notify(observer, event);
        sat::Engine engine("interpolation-verify-invariant");
        if (event == Event::verify_initial) {
            system.initial(engine, 0);
            candidate.emit(engine, 0, false);
        } else if (event == Event::verify_transition) {
            candidate.emit(engine, 0);
            system.transition(engine, 0);
            candidate.emit(engine, 1, false);
        } else {
            candidate.emit(engine, 0);
            system.target(engine, 0);
        }
        const auto status = engine.solve();
        if (status != sat::STATUS_UNSAT) return status;
    }
    tick();
    return sat::STATUS_UNSAT;
}

sat::status_t verify_path(const System& system, const Path& path, const Observer& observer)
{
    validate_bits(system.bits());
    if (path.empty() || path.size() - 1 > LAST_POSITIVE_TIME) throw std::invalid_argument("Invalid concrete path length");
    notify(observer, Event::verify_path);
    sat::Engine engine("interpolation-verify-path");
    system.initial(engine, 0);
    for (size_t frame = 0; frame < path.size(); ++frame) {
        tick();
        if (path[frame].size() != system.bits().size()) throw std::invalid_argument("Concrete path state width mismatch");
        if (frame) system.transition(engine, frame - 1);
        for (size_t i = 0; i < system.bits().size(); ++i) {
            tick();
            const auto var = engine.tcbi_to_var(at(system.bits()[i], frame));
            engine.add_clause({sat::mkLit(var, !path[frame][i])});
        }
    }
    system.target(engine, path.size() - 1);
    const auto status = engine.solve();
    tick();
    return status;
}

Result search(const System& system, Limits limits, const Observer& observer)
{
    if (limits.horizon < -1 || limits.images < -1 || limits.horizon >= LAST_POSITIVE_TIME)
        throw std::invalid_argument("Invalid interpolation search limits");
    Result result;
    auto& stats = result.statistics;
    try {
        validate_bits(system.bits());
        sat::Engine concrete("interpolation-concrete-search");
        system.initial(concrete, 0);
        allocate_state(concrete, system.bits(), 0);
        unsigned depth = 0;
        const auto check_depth = [&] {
            notify(observer, Event::concrete);
            system.target(concrete, depth, concrete.new_group());
            const auto status = completed(concrete.solve());
            stats.checked_depths.push_back(depth);
            if (status == sat::STATUS_SAT) return true;
            concrete.invert_last_group();
            return false;
        };
        const auto reachable = [&] {
            auto path = decode(concrete, system.bits(), depth);
            if (completed(verify_path(system, path, observer)) != sat::STATUS_SAT)
                throw std::logic_error("Concrete interpolation path failed fresh validation");
            tick();
            result.path = std::move(path);
            result.outcome = Outcome::reachable;
            result.verified = true;
        };
        const auto unreachable = [&](StateFormula candidate, bool vacuous) {
            if (completed(verify_invariant(system, candidate, observer)) != sat::STATUS_UNSAT)
                throw std::logic_error("Interpolation invariant failed fresh validation");
            tick();
            result.invariant.emplace(std::move(candidate));
            result.outcome = Outcome::unreachable;
            result.verified = true;
            result.vacuous = vacuous;
        };
        if (check_depth()) { reachable(); return result; }
        if (completed(concrete.solve()) == sat::STATUS_UNSAT) {
            unreachable(StateFormula(system.bits(), limits.invariant_nodes), true);
            return result;
        }

        // Project the native initial predicate into an exact state circuit.
        // A=I*, B=NOT I* use independently compiled semantic polarities. Craig
        // validation therefore establishes equivalence, not just containment.
        notify(observer, Event::initial_projection);
        sat::InterpolationResult initial;
        {
            sat::Engine a("interpolation-initial-a", sat::Engine::Mode::record);
            sat::Engine b("interpolation-initial-b", sat::Engine::Mode::record);
            system.initial(a, 0);
            system.initial(b, 0, false);
            initial = sat::compute_interpolant(sat::PartitionedCnf(a, b, 0), limits.interpolation);
        }
        if (completed(initial.status) != sat::STATUS_UNSAT)
            throw std::logic_error("Initial predicate and its semantic complement overlap");
        StateFormula seed(system.bits(), limits.invariant_nodes);
        seed.root = import(seed, initial);
        stats.proof_nodes += initial.proof_nodes;
        stats.circuit_nodes = seed.circuit.size();
        initial = sat::InterpolationResult();

        for (unsigned horizon = 0;; ++horizon) {
            tick();
            if (horizon >= LAST_POSITIVE_TIME ||
                (limits.horizon >= 0 && horizon > static_cast<uint64_t>(limits.horizon)))
                throw Stopped{Stop::horizon_limit};
            stats.horizon = horizon;
            StateFormula reached = seed;
            bool first = true;
            for (;;) {
                tick();
                if (limits.images >= 0 && stats.images >= static_cast<uint64_t>(limits.images))
                    throw Stopped{Stop::image_limit};
                notify(observer, Event::image);
                ++stats.images;
                sat::InterpolationResult image;
                {
                    sat::Engine a("interpolation-image-a", sat::Engine::Mode::record);
                    sat::Engine b("interpolation-image-b", sat::Engine::Mode::record);
                    // Use the original INIT on the first iteration explicitly.
                    if (first) system.initial(a, 0);
                    else reached.emit(a, 0);
                    system.transition(a, 0);
                    emit_suffix(system, b, 1, horizon);
                    image = sat::compute_interpolant(sat::PartitionedCnf(a, b, 1), limits.interpolation);
                }
                completed(image.status);
                stats.proof_nodes += image.proof_nodes;
                if (first) {
                    // Complete all newly exposed concrete depths in order. An
                    // abstract image iteration is never a concrete depth check.
                    bool found = false;
                    while (depth < horizon + 1 && !found) {
                        system.transition(concrete, depth);
                        ++depth;
                        allocate_state(concrete, system.bits(), depth);
                        found = check_depth();
                    }
                    if ((image.status == sat::STATUS_SAT) != found)
                        throw std::logic_error("Initial image and concrete bounded search disagree");
                    if (found) { ++stats.concrete_sat; reachable(); return result; }
                }
                if (image.status == sat::STATUS_SAT) {
                    // SAT from an enlarged R is only an approximation witness.
                    // Discard it and restart with a longer suffix and exact INIT.
                    ++stats.spurious_sat;
                    ++stats.restarts;
                    notify(observer, Event::restart);
                    break;
                }
                const auto next = import(reached, image);
                stats.circuit_nodes = std::max(stats.circuit_nodes, reached.circuit.size());
                notify(observer, Event::inclusion);
                sat::Engine inclusion("interpolation-image-inclusion");
                emit(inclusion, reached, next, 0);
                reached.emit(inclusion, 0, false);
                if (completed(inclusion.solve()) == sat::STATUS_UNSAT) {
                    unreachable(std::move(reached), false);
                    return result;
                }
                notify(observer, Event::growth);
                reached.root = reached.circuit.disjunction(reached.root, next);
                stats.circuit_nodes = std::max(stats.circuit_nodes, reached.circuit.size());
                ++stats.enlargements;
                first = false;
            }
        }
    } catch (const Stopped& stopped) {
        result.stop = stopped.reason;
    } catch (const query::Cancelled&) {
        result.stop = Stop::interrupted;
    } catch (const std::length_error&) {
        result.stop = Stop::node_limit;
    }
    if (auto context = query::current()) result.query_stop = context->stop.load();
    return result;
}
} // namespace reach::interpolation
