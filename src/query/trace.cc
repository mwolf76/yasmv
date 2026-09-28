#include <algorithms/base.hh>
#include <charconv>
#include <env/environment.hh>
#include <expr/time/analyzer/analyzer.hh>
#include <expr/time/expander/expander.hh>
#include <filesystem>
#include <fstream>
#include <limits>
#include <optional>
#include <parse.hh>
#include <query/expressions.hh>
#include <query/trace.hh>
#include <unistd.h>
#include <witness/witness_mgr.hh>
namespace query::trace {
    struct Symbol {
        std::string name;
        expr::Expr_ptr key;
        type::Type_ptr type;
        bool frozen, input;
    };
    static std::vector<Symbol> symbols()
    {
        std::vector<Symbol> v;
        auto& mm = model::ModelMgr::INSTANCE();
        auto& em = expr::ExprMgr::INSTANCE();
        symb::SymbIter it(mm.model());
        while (it.has_next()) {
            auto [scope, s] = it.next();
            if (!s->is_variable()) continue;
            auto& x = s->as_variable();
            if (x.type()->is_instance()) continue;
            auto key = em.make_dot(scope, s->name());
            v.push_back({ source::print(key), key, x.type(), x.is_frozen(), x.is_input() });
        }
        std::sort(v.begin(), v.end(), [](const auto& a, const auto& b) { return a.name < b.name; });
        return v;
    }
    void allocate_state(sat::Engine& engine, unsigned step)
    {
        auto& bm = enc::EncodingMgr::INSTANCE();
        for (const auto& s : symbols()) {
            checkpoint(Phase::encoding);
            if (s.input) continue;
            expr::TimedExpr key(s.key, s.frozen ? FROZEN : 0);
            auto encoding = bm.find_encoding(key);
            if (!encoding) {
                encoding = bm.make_encoding(s.type);
                bm.register_encoding(key, encoding);
            }
            for (const auto& bit : encoding->bits())
                engine.tcbi_to_var(enc::TCBI(bm.find_ucbi(bit.getNode()->index), step));
        }
    }
    witness::Witness_ptr decode(sat::Engine& engine, unsigned depth)
    {
        PhaseTimer timer(Phase::decoding);
        auto& bm = enc::EncodingMgr::INSTANCE();
        auto w = new witness::Witness();
        w->set_id("query_" + std::to_string(witness::WitnessMgr::INSTANCE().autoincrement()));
        for (const auto& s : symbols())
            w->lang().push_back(s.key);
        for (unsigned k = 0; k <= depth; ++k) {
            auto& tf = w->extend();
            for (const auto& s : symbols()) {
                checkpoint(Phase::decoding);
                if (s.input) {
                    tf.set_value(s.key, env::Environment::INSTANCE().get(s.key->rhs()));
                    continue;
                }
                auto encoding = bm.find_encoding(expr::TimedExpr(s.key, s.frozen ? FROZEN : 0));
                std::vector<int> values(bm.nbits(), 0);
                for (const auto& bit : encoding->bits()) {
                    auto index = bit.getNode()->index;
                    values[index] = engine.value(engine.existing_var(enc::TCBI(bm.find_ucbi(index), k)));
                }
                auto value = encoding->expr(values.data());
                if (value) tf.set_value(s.key, value);
            }
        }
        return w;
    }
    Json::Value evaluate_watches(witness::Witness& w, const std::map<std::string, expr::Expr_ptr>& watches)
    {
        Json::Value result(Json::objectValue);
        algorithms::Algorithm a(model::ModelMgr::INSTANCE().model());
        auto empty = expr::ExprMgr::INSTANCE().make_empty();
        for (const auto& [name, expression] : watches) {
            auto unit = a.compiler().process(empty, expression);
            result[name] = Json::arrayValue;
            for (unsigned k = 0; k < w.size(); ++k) {
                checkpoint(Phase::encoding);
                sat::Engine engine("watch");
                a.assert_time_frame(engine, 0, w[w.first_time() + k]);
                a.assert_fsm_invar(engine, 0);
                auto state_status = engine.solve();
                if (state_status == sat::STATUS_UNKNOWN) throw Cancelled();
                if (state_status != sat::STATUS_SAT) throw std::invalid_argument("Cannot evaluate watch on an invalid state");
                a.assert_formula(engine, 0, unit);
                auto status = engine.solve();
                if (status == sat::STATUS_UNKNOWN) throw Cancelled();
                result[name].append(status == sat::STATUS_SAT);
            }
        }
        return result;
    }
    static void require(bool condition, const std::string& message)
    {
        if (!condition) throw std::invalid_argument(message);
    }
    static bool equal_json(const Json::Value& a, const Json::Value& b)
    {
        Json::StreamWriterBuilder builder;
        builder["indentation"] = "";
        return Json::writeString(builder, a) == Json::writeString(builder, b);
    }
    static void keys(const Json::Value& v, std::initializer_list<const char*> names)
    {
        require(v.isObject(), "Expected an object");
        std::set<std::string> expected;
        for (auto n : names)
            expected.insert(n);
        for (const auto& n : v.getMemberNames())
            require(expected.count(n), "Unknown field: " + n);
        for (const auto& n : expected)
            require(v.isMember(n), "Missing field: " + n);
    }
    static Json::Value type_json(type::Type_ptr t)
    {
        Json::Value v;
        if (t->is_boolean())
            v["kind"] = "boolean";
        else if (t->is_enum()) {
            v["kind"] = "enum";
            v["literals"] = Json::arrayValue;
            std::vector<std::string> lits;
            for (auto e : t->as_enum()->literals())
                lits.push_back(source::print(e));
            std::sort(lits.begin(), lits.end());
            for (auto& s : lits)
                v["literals"].append(s);
        } else if (t->is_array()) {
            v["kind"] = "array";
            v["length"] = t->as_array()->nelems();
            v["element"] = type_json(t->as_array()->of());
        } else if (t->is_algebraic()) {
            v["kind"] = "integer";
            v["width"] = t->width();
            v["signed"] = t->is_signed_algebraic();
        } else
            throw std::invalid_argument("Unsupported trace type");
        return v;
    }
    static uint64_t literal_bits(expr::Expr_ptr e)
    {
        auto& em = expr::ExprMgr::INSTANCE();
        if (e == em.make_true()) return 1;
        if (e == em.make_false()) return 0;
        if (em.is_constant(e)) return static_cast<uint64_t>(e->value());
        if (em.is_neg(e)) return uint64_t(0) - literal_bits(e->lhs());
        if (e->symb() == expr::NOT) return !literal_bits(e->lhs());
        throw std::invalid_argument("Trace input value must be a literal (optionally negated)");
    }
    static Json::Value value_json(type::Type_ptr t, expr::Expr_ptr e)
    {
        if (!e) return Json::Value();
        auto& em = expr::ExprMgr::INSTANCE();
        if (t->is_array()) {
            Json::Value v(Json::arrayValue);
            for (auto x : em.array_literals(e))
                v.append(value_json(t->as_array()->of(), x));
            return v;
        }
        if (t->is_boolean()) return Json::Value(bool(literal_bits(e)));
        if (t->is_enum()) return Json::Value(source::print(e));
        uint64_t bits = literal_bits(e);
        unsigned width = t->width();
        require(width > 0 && width <= 64, "Unsupported integer width");
        if (width < 64) bits &= (uint64_t(1) << width) - 1;
        if (t->is_signed_algebraic()) {
            if (width < 64 && (bits & (uint64_t(1) << (width - 1)))) bits |= ~((uint64_t(1) << width) - 1);
            return Json::Value(std::to_string(static_cast<int64_t>(bits)));
        }
        return Json::Value(std::to_string(bits));
    }
    static expr::Expr_ptr value_expr(type::Type_ptr t, const Json::Value& v)
    {
        auto& em = expr::ExprMgr::INSTANCE();
        if (v.isNull()) return nullptr;
        if (t->is_boolean()) {
            require(v.isBool(), "Expected Boolean value");
            return v.asBool() ? em.make_true() : em.make_false();
        }
        if (t->is_enum()) {
            require(v.isString(), "Expected enum literal");
            for (auto e : t->as_enum()->literals())
                if (source::print(e) == v.asString()) return e;
            throw std::invalid_argument("Unknown enum literal");
        }
        if (t->is_array()) {
            require(v.isArray() && v.size() == t->as_array()->nelems(), "Array length mismatch");
            expr::Expr_ptr acc = nullptr;
            for (size_t i = v.size(); i > 0; --i) {
                auto e = value_expr(t->as_array()->of(), v[static_cast<Json::ArrayIndex>(i - 1)]);
                require(e != nullptr, "Array elements must be assigned");
                acc = acc ? em.make_array_comma(e, acc) : e;
            }
            return em.make_array(acc);
        }
        require(v.isString(), "Integer values must be decimal strings");
        auto text = v.asString();
        unsigned width = t->width();
        require(width > 0 && width <= 64, "Unsupported integer width");
        if (t->is_signed_algebraic()) {
            int64_t x = 0;
            auto p = std::from_chars(text.data(), text.data() + text.size(), x);
            require(p.ec == std::errc() && p.ptr == text.data() + text.size() && text == std::to_string(x), "Invalid canonical signed integer");
            if (width < 64) require(x >= -(int64_t(1) << (width - 1)) && x < (int64_t(1) << (width - 1)), "Signed integer out of range");
            return em.make_const(x);
        }
        uint64_t x = 0;
        auto p = std::from_chars(text.data(), text.data() + text.size(), x);
        require(p.ec == std::errc() && p.ptr == text.data() + text.size() && text == std::to_string(x), "Invalid canonical unsigned integer");
        if (width < 64) require(x < (uint64_t(1) << width), "Unsigned integer out of range");
        return em.make_const(static_cast<int64_t>(x));
    }
    // Exact semantic valuations shared by graph exploration and its verifier.
    Json::Value state_values(sat::Engine& engine, unsigned step)
    {
        auto& bm = enc::EncodingMgr::INSTANCE();
        Json::Value result(Json::objectValue);
        for (const auto& s : symbols()) {
            checkpoint(Phase::decoding);
            expr::Expr_ptr value;
            if (s.input) value = env::Environment::INSTANCE().get(s.key->rhs());
            else {
                auto encoding = bm.find_encoding(expr::TimedExpr(s.key, s.frozen ? FROZEN : 0));
                require(encoding != nullptr, "State encoding is missing");
                std::vector<int> bits(bm.nbits(), 0);
                for (const auto& bit : encoding->bits()) {
                    auto index = bit.getNode()->index;
                    auto var = engine.existing_var(enc::TCBI(bm.find_ucbi(index), step));
                    require(engine.assigned(var), "Unassigned semantic state bit");
                    bits[index] = engine.value(var);
                }
                value = encoding->expr(bits.data());
            }
            require(value != nullptr, "Incomplete semantic state");
            result[s.name] = value_json(s.type, value);
        }
        return result;
    }
    expr::Expr_ptr typed_value(type::Type_ptr type, expr::Expr_ptr value)
    {
        auto& em = expr::ExprMgr::INSTANCE();
        if (type->is_algebraic()) return em.make_cast(type->repr(), value);
        if (type->is_array()) {
            auto elements = em.array_literals(value);
            expr::Expr_ptr acc = nullptr;
            for (auto it = elements.rbegin(); it != elements.rend(); ++it) {
                auto element = typed_value(type->as_array()->of(), *it);
                acc = acc ? em.make_array_comma(element, acc) : element;
            }
            return em.make_array(acc);
        }
        return value;
    }
    expr::Expr_ptr valuation(const Json::Value& values)
    {
        auto syms = symbols();
        require(values.isObject() && values.size() == syms.size(), "Expected a complete semantic state");
        auto& em = expr::ExprMgr::INSTANCE();
        auto result = em.make_true();
        for (const auto& s : syms) {
            checkpoint(Phase::compilation);
            require(values.isMember(s.name) && !values[s.name].isNull(), "Missing state value: " + s.name);
            auto value = value_expr(s.type, values[s.name]);
            if (s.input) {
                require(values[s.name] == value_json(s.type, env::Environment::INSTANCE().get(s.key->rhs())), "Input value differs from model binding");
            } else result = em.make_and(result, em.make_eq(parse::parseExpression(s.name.c_str()), typed_value(s.type, value)));
        }
        return result;
    }
    Json::Value symbol_catalog()
    {
        Json::Value catalog(Json::objectValue);
        for (const auto& s : symbols()) {
            auto& d = catalog[s.name];
            d["type"] = type_json(s.type);
            d["frozen"] = s.frozen;
            d["input"] = s.input;
        }
        return catalog;
    }
    Json::Value export_trace(witness::Witness& w, const QuerySpec& spec, const Json::Value& id)
    {
        PhaseTimer timer(Phase::decoding);
        Json::Value v;
        v["version"] = 1;
        v["id"] = w.id();
        v["identity"] = id;
        v["initial_time"] = 0;
        v["origin"]["initial_time"] = spec.strategy == "backward" ? UINT_MAX - (w.size() - 1) : w.first_time();
        v["origin"]["direction"] = spec.strategy == "backward" ? "backward" : "forward";
        v["symbols"] = symbol_catalog();
        v["steps"] = Json::arrayValue;
        unsigned k = 0;
        for (auto tf : w.frames()) {
            Json::Value frame;
            frame["step"] = k++;
            frame["values"] = Json::objectValue;
            for (const auto& s : symbols())
                frame["values"][s.name] = value_json(s.type, tf->has_value(s.key) ? tf->value(s.key) : nullptr);
            v["steps"].append(frame);
        }
        v["query"] = spec_json(spec);
        v["branch"] = Json::Value();
        return v;
    }
    witness::Witness_ptr import_trace(const Json::Value& v)
    {
        keys(v, { "version", "id", "identity", "initial_time", "origin", "symbols", "steps", "query", "branch" });
        require(v["version"].isInt() && v["version"].asInt() == 1, "Unsupported trace version");
        require(equal_json(v["identity"], identity()), "Trace model/configuration identity mismatch");
        require(v["id"].isString() && !v["id"].asString().empty(), "Invalid trace id");
        require(v["initial_time"].isUInt() && v["initial_time"].asUInt() == 0, "Trace display coordinates must start at zero");
        keys(v["origin"], { "initial_time", "direction" });
        require(v["origin"]["initial_time"].isUInt(), "Invalid origin time");
        require(v["origin"]["direction"] == "forward" || v["origin"]["direction"] == "backward", "Invalid trace direction");
        auto syms = symbols();
        require(v["symbols"].isObject() && v["symbols"].size() == syms.size(), "Trace symbol set mismatch");
        for (const auto& s : syms) {
            const auto& d = v["symbols"][s.name];
            keys(d, { "type", "frozen", "input" });
            require(equal_json(d["type"], type_json(s.type)) && d["frozen"] == Json::Value(s.frozen) && d["input"] == Json::Value(s.input), "Trace symbol type mismatch: " + s.name);
        }
        require(v["steps"].isArray() && !v["steps"].empty(), "Trace must contain states");
        auto w = new witness::Witness(nullptr, v["id"].asString(), "Imported trace v1");
        for (const auto& s : syms)
            w->lang().push_back(s.key);
        for (Json::ArrayIndex k = 0; k < v["steps"].size(); ++k) {
            checkpoint(Phase::decoding);
            const auto& f = v["steps"][k];
            keys(f, { "step", "values" });
            require(f["step"].isUInt() && f["step"].asUInt() == k, "Nonconsecutive trace step");
            require(f["values"].isObject(), "Expected state values");
            for (const auto& n : f["values"].getMemberNames())
                require(v["symbols"].isMember(n), "Unknown state symbol: " + n);
            auto& tf = w->extend();
            for (const auto& s : syms) {
                auto e = value_expr(s.type, f["values"][s.name]);
                if (e) tf.set_value(s.key, e);
            }
        }
        return w;
    }
    // Independent direct evaluator for the Boolean/integer expression subset.
    // Unsupported operators report no result; SAT replay still checks the full dialect.
    static std::optional<uint64_t> eval(expr::Expr_ptr e, witness::Witness& w, unsigned step)
    {
        auto& em = expr::ExprMgr::INSTANCE();
        if (!e) return std::nullopt;
        if (e == em.make_true()) return 1;
        if (e == em.make_false()) return 0;
        if (em.is_constant(e)) return static_cast<uint64_t>(e->value());
        auto key = em.is_identifier(e) ? em.make_dot(em.make_empty(), e) : e;
        if (step < w.size() && std::find(w.lang().begin(), w.lang().end(), key) != w.lang().end() && w[step].has_value(key)) {
            auto value = w[step].value(key);
            if (value == em.make_true()) return 1;
            if (value == em.make_false()) return 0;
            if (em.is_constant(value)) return static_cast<uint64_t>(value->value());
            return std::nullopt;
        }
        if (em.is_identifier(e) || e->symb() == expr::QSTRING || e->symb() == expr::INSTANT) return std::nullopt;
        if (e->symb() == expr::NEXT) return eval(e->lhs(), w, step + 1);
        if (e->symb() == expr::ASSIGNMENT) {
            auto lhs = eval(e->lhs(), w, step + 1), rhs = eval(e->rhs(), w, step);
            if (lhs && rhs) return *lhs == *rhs;
            return std::nullopt;
        }
        auto lhs = eval(e->lhs(), w, step);
        if (!lhs) return std::nullopt;
        if (e->symb() == expr::NOT) return !*lhs;
        auto rhs = eval(e->rhs(), w, step);
        if (!rhs) return std::nullopt;
        switch (e->symb()) {
            case expr::AND:
                return bool(*lhs) && bool(*rhs);
            case expr::OR:
                return bool(*lhs) || bool(*rhs);
            case expr::GUARD:
            case expr::IMPLIES:
                return !*lhs || *rhs;
            case expr::EQ:
                return *lhs == *rhs;
            case expr::NE:
                return *lhs != *rhs;
            default:
                return std::nullopt;
        }
    }
    static expr::Expr_ptr chronological(expr::Expr_ptr e, unsigned depth)
    {
        auto& em = expr::ExprMgr::INSTANCE();
        if (em.is_and(e)) return em.make_and(chronological(e->lhs(), depth), chronological(e->rhs(), depth));
        require(em.is_at(e) && em.is_instant(e->lhs()), "Unsupported timed trace assumption");
        uint64_t raw = e->lhs()->value();
        int64_t point = raw > INT_MAX ? int64_t(depth) - int64_t(UINT_MAX - raw) : raw;
        require(point >= 0 && point <= depth, "Query assumption falls outside recorded trace");
        return em.make_at(em.make_instant(point), e->rhs());
    }
    QueryResult validate(const Json::Value& v, const Json::Value& parent, QueryContext& context, const std::string& request_id)
    {
        ContextScope scope(context);
        QueryResult r;
        r.request_id = request_id;
        r.scope = "whole_trace";
        try {
            auto w = import_trace(v);
            r.identity = identity();
            QuerySpec spec = spec_from_json(v["query"]);
            require(!spec.target || state_expression(spec.target), "Trace goal must be a state expression");
            for (auto e : spec.assumptions)
                require(state_expression(e, spec.operation == Operation::reach && spec.limits.depth < 0), "Incompatible timed trace assumption");
            const Json::Value& resolved_parent = parent.isNull() ? spec.parent_trace : parent;
            const auto& parent = resolved_parent;
            if (!v["branch"].isNull()) {
                keys(v["branch"], { "parent_id", "prefix_length", "parent_digest" });
                const auto& b = v["branch"];
                require(!parent.isNull(), "Branch validation requires the parent trace");
                require(b["parent_id"] == parent["id"], "Branch parent id mismatch");
                Json::StreamWriterBuilder builder;
                builder["indentation"] = "";
                require(b["parent_digest"] == source::digest(Json::writeString(builder, parent)), "Branch parent digest mismatch");
                require(b["prefix_length"].isUInt() && b["prefix_length"].asUInt() > 0, "Invalid branch prefix");
                auto n = b["prefix_length"].asUInt();
                require(n <= w->size() && n <= parent["steps"].size(), "Branch prefix exceeds trace");
                for (unsigned k = 0; k < n; ++k)
                    require(equal_json(v["steps"][k], parent["steps"][k]), "Branch changed its declared prefix at step " + std::to_string(k));
                auto pr = validate(parent, parent["query"]["parent_trace"], context);
                require(pr.outcome == Outcome::valid, "Parent trace has not passed replay");
            }
            bool missing = false;
            for (auto tf : w->frames())
                for (const auto& s : symbols())
                    if (!tf->has_value(s.key)) missing = true;
            if (missing) {
                r.reason = StopReason::solver_unknown;
                source::Diagnostic d;
                d.code = "unassigned-values";
                d.message = "Trace contains unassigned values; complete replay cannot be certified";
                r.diagnostics.push_back(d);
                return r;
            }
            algorithms::Algorithm a(model::ModelMgr::INSTANCE().model());
            sat::Engine engine("trace-replay");
            a.assert_fsm_init(engine, 0);
            auto empty = expr::ExprMgr::INSTANCE().make_empty();
            for (unsigned k = 0; k < w->size(); ++k) {
                checkpoint(Phase::encoding);
                a.assert_fsm_invar(engine, k);
                a.assert_time_frame(engine, k, (*w)[k]);
                const unsigned start = spec.operation == Operation::simulate && !v["branch"].isNull() ? v["branch"]["prefix_length"].asUInt() - 1 : 0;
                for (auto e : spec.assumptions) {
                    if (spec.operation == Operation::simulate && (k < start || k + 1 == w->size())) continue;
                    expr::time::Analyzer times(expr::ExprMgr::INSTANCE());
                    times.process(e);
                    bool timed = times.has_forward_time() || times.has_backward_time();
                    if (timed && k != 0) continue;
                    if (timed) {
                        expr::time::Expander expand(expr::ExprMgr::INSTANCE());
                        e = chronological(expand.process(e), w->size() - 1);
                    }
                    auto cu = a.compiler().process(empty, e);
                    a.assert_formula(engine, k, cu);
                }
                if (k > 0) a.assert_fsm_trans(engine, k - 1);
                auto status = engine.solve();
                if (status == sat::STATUS_UNKNOWN) throw Cancelled();
                if (status == sat::STATUS_UNSAT) {
                    r.status = ExecutionStatus::completed;
                    r.outcome = Outcome::invalid;
                    r.complete = true;
                    source::Diagnostic d;
                    d.code = "replay-mismatch";
                    d.message = "Trace violates initialization, invariants, assumptions or transition at step " + std::to_string(k);
                    r.diagnostics.push_back(d);
                    return r;
                }
                r.checked_depths.push_back(k);
            }
            if (spec.operation == Operation::reach || spec.operation == Operation::shortest_reach || spec.operation == Operation::check_property || spec.operation == Operation::prove_property) {
                if (spec.operation == Operation::check_property || spec.operation == Operation::prove_property) {
                    require(!spec.property.isNull(), "Missing safety property");
                    spec.target = expr::ExprMgr::INSTANCE().make_not(parse::parseExpression(spec.property["expression"].asCString()));
                }
                require(spec.target != nullptr, "Reachability trace has no target");
                auto goal = a.compiler().process(empty, spec.target);
                a.assert_formula(engine, w->size() - 1, goal);
                if (spec.limits.depth >= 0) require(w->size() - 1 <= static_cast<unsigned>(spec.limits.depth), "Trace exceeds query depth");
                auto status = engine.solve();
                if (status == sat::STATUS_UNKNOWN) throw Cancelled();
                require(status == sat::STATUS_SAT, "Final state does not satisfy query target");
            }
            unsigned evaluated = 0;
            auto& main = model::ModelMgr::INSTANCE().model().main_module();
            auto test = [&](expr::Expr_ptr e, unsigned k) {auto value=eval(e,*w,k);if(value){++evaluated;require(*value!=0,"Independent evaluator found a mismatch at step "+std::to_string(k));} };
            for (auto e : main.init())
                test(e, 0);
            for (unsigned k = 0; k < w->size(); ++k) {
                for (auto e : main.invar())
                    test(e, k);
                if (k + 1 < w->size())
                    for (auto e : main.trans())
                        test(e, k);
            }
            r.statistics["independent_constraints_checked"] = evaluated;
            if (context.stop != StopReason::none) throw Cancelled();
            r.status = ExecutionStatus::completed;
            r.outcome = Outcome::valid;
            r.complete = true;
            r.witness = w;
            r.trace = v;
        } catch (const Cancelled&) {
            r.reason = context.stop == StopReason::none ? StopReason::solver_unknown : context.stop.load();
        } catch (const std::exception& e) {
            r.status = ExecutionStatus::error;
            r.reason = StopReason::validation_error;
            source::Diagnostic d;
            d.code = "invalid-trace";
            d.message = e.what();
            r.diagnostics.push_back(d);
        }
        return r;
    }
    Json::Value read_file(const std::string& path)
    {
        std::ifstream in(path);
        require(bool(in), "Cannot open JSON file: " + path);
        Json::CharReaderBuilder b;
        b["rejectDupKeys"] = true;
        b["allowComments"] = false;
        b["allowTrailingCommas"] = false;
        b["strictRoot"] = true;
        b["failIfExtra"] = true;
        Json::Value v;
        std::string errors;
        require(Json::parseFromStream(b, in, &v, &errors), "Invalid JSON: " + errors);
        return v;
    }
    void write_file(const std::string& path, const Json::Value& value)
    {
        auto tmp = path + ".tmp." + std::to_string(getpid());
        try {
            std::ofstream out(tmp, std::ios::trunc);
            require(bool(out), "Cannot write artifact: " + tmp);
            out << value << '\n';
            out.close();
            require(bool(out), "Artifact write failed");
            std::filesystem::rename(tmp, path);
        } catch (...) {
            std::filesystem::remove(tmp);
            throw;
        }
    }
} // namespace query::trace
