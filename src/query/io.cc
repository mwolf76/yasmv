#include <env/environment.hh>
#include <fstream>
#include <map>
#include <parse.hh>
#include <query/query.hh>
#include <query/trace.hh>
namespace query {
    static const std::map<std::string, Operation> operations = {
        {"validate-progress", Operation::validate_progress}, {"explain-init", Operation::explain_init},
        {"explain-step", Operation::explain_step}, {"explain-reach", Operation::explain_reach},
        {"validate-model", Operation::validate_model}, {"pick-state", Operation::pick_state},
        {"simulate", Operation::simulate}, {"diameter", Operation::diameter}, {"validate-trace", Operation::validate_trace}};

    static void require(bool c, const std::string& message)
    {
        if (!c) throw std::invalid_argument(message);
    }
    static void allowed(const Json::Value& v, std::initializer_list<const char*> names)
    {
        require(v.isObject(), "Expected query object");
        std::set<std::string> keys;
        for (auto n : names)
            keys.insert(n);
        for (const auto& n : v.getMemberNames())
            require(keys.count(n), "Unknown request field: " + n);
    }
    static expr::Expr_ptr expression(const Json::Value& v)
    {
        require(v.isString() && !v.asString().empty(), "Expected nonempty expression string");
        auto e = parse::parseExpression(v.asCString());
        require(e != nullptr, "Invalid expression: " + v.asString());
        return e;
    }
    Json::Value spec_json(const QuerySpec& s)
    {
        Json::Value v;
        for (const auto& [n, o] : operations)
            if (o == s.operation) v["operation"] = n;
        v["request_id"] = s.request_id;
        std::string variant = s.check_variant, method = s.method;
        if (variant.empty()) {
            if (s.operation == Operation::check_init) variant = "init";
            if (s.operation == Operation::check_trans) variant = "trans";
            if (s.operation == Operation::check_progress) variant = "progress";
            if (s.operation == Operation::reach || s.operation == Operation::shortest_reach) variant = "reachable";
            if (s.operation == Operation::check_property || s.operation == Operation::prove_property) variant = "invariant";
        }
        if (!variant.empty()) {
            v["operation"] = "check";
            v["variant"] = variant;
            if (variant == "reachable" || variant == "invariant") {
                if (method.empty()) method = s.strategy == "interpolation" || s.limits.depth < 0 ? "interpolation" :
                    s.operation == Operation::prove_property ? "induction" : "bmc";
                v["method"] = method;
                if (s.shortest || s.operation == Operation::shortest_reach) v["shortest"] = true;
            }
        }
        v["assumptions"] = Json::arrayValue;
        for (auto e : s.assumptions)
            v["assumptions"].append(source::print(e));
        if (s.target) v["target"] = source::print(s.target);
        if (s.until) v["until"] = source::print(s.until);
        if (s.enumerate) v["enumerate"] = true;
        if (s.count) v["count"] = true;
        if (!s.trace_id.empty()) v["trace_id"] = s.trace_id;
        if (!s.progress.isNull()) v["progress"] = s.progress;
        if (s.check_target) v["target"] = source::print(s.check_target);
        else if (!s.property.isNull()) v["target"] = s.property["expression"];
        if (!s.explanation.isNull()) v["explanation"] = s.explanation;
        if (s.prefix_length >= 0) v["prefix_length"] = Json::Int64(s.prefix_length);
        if (!s.watches.empty()) {
            v["watches"] = Json::objectValue;
            for (const auto& [name, e] : s.watches)
                v["watches"][name] = source::print(e);
        }
        if (s.limits.depth >= 0) v["limits"]["depth"] = Json::Int64(s.limits.depth);
        if (s.limits.states >= 0) v["limits"]["states"] = Json::Int64(s.limits.states);
        if (s.limits.wall_ms >= 0 || !variant.empty()) v["limits"]["wall_ms"] = Json::Int64(s.limits.wall_ms);
        if (s.limits.conflicts >= 0) v["limits"]["conflicts"] = Json::Int64(s.limits.conflicts);
        if (s.limits.propagations >= 0) v["limits"]["propagations"] = Json::Int64(s.limits.propagations);
        if (!s.parent_trace.isNull()) v["parent_trace"] = s.parent_trace;
        return v;
    }
    QuerySpec spec_from_json(const Json::Value& v)
    {
        allowed(v, { "operation", "variant", "method", "shortest", "request_id", "target", "until", "assumptions", "limits", "enumerate", "count", "trace_id", "trace", "parent_trace", "prefix_length", "watches", "explanation", "progress" });
        require(v["operation"].isString(), "Expected query operation");
        QuerySpec s;
        const bool checking = v["operation"] == "check";
        if (checking) {
            require(v["variant"].isString(), "Check requires a variant");
            s.check_variant = v["variant"].asString();
            const auto& variant = s.check_variant;
            require(variant == "init" || variant == "trans" || variant == "reachable" || variant == "invariant" || variant == "progress", "Unknown check variant");
            const bool search = variant == "reachable" || variant == "invariant";
            require(v.isMember("target") == (search || variant == "progress"), "This check requires exactly its target expression");
            require(!v.isMember("method") || (search && v["method"].isString()), "Method applies only to reachable and invariant checks");
            require(!v.isMember("shortest") || (search && v["shortest"].isBool()), "Invalid shortest option");
            s.method = search ? v.get("method", "interpolation").asString() : "";
            s.shortest = v.get("shortest", false).asBool();
            require(!search || s.method == "bmc" || s.method == "induction" || s.method == "interpolation", "Unknown check method");
            require(!v.isMember("shortest") || s.method == "bmc", "Shortest requires BMC");
            s.operation = variant == "init" ? Operation::check_init : variant == "trans" ? Operation::check_trans :
                variant == "progress" ? Operation::check_progress : variant == "reachable" && s.method != "induction" ? Operation::reach :
                s.method == "bmc" ? Operation::check_property : Operation::prove_property;
            if (s.method == "interpolation") s.strategy = "interpolation";
            if (variant == "trans") s.limits.depth = 1;
            if (variant == "progress") s.limits.states = 10000;
            s.limits.wall_ms = 30000;
            for (auto key : {"until", "trace", "trace_id", "parent_trace", "prefix_length", "explanation", "progress", "enumerate", "count"})
                require(!v.isMember(key), std::string("Check does not accept ") + key);
        } else {
            require(operations.count(v["operation"].asString()), "Unsupported query operation");
            s.operation = operations.at(v["operation"].asString());
            require(!v.isMember("variant") && !v.isMember("method") && !v.isMember("shortest"), "Check options require operation check");
        }
        for (auto n : {"request_id", "trace_id"})
            if (v.isMember(n)) require(v[n].isString(), std::string("Expected string: ") + n);
        s.request_id = v.get("request_id", "").asString();
        s.trace_id = v.get("trace_id", "").asString();
        if (v.isMember("target")) s.target = expression(v["target"]);
        if (v.isMember("until")) s.until = expression(v["until"]);
        if (v.isMember("assumptions")) {
            require(v["assumptions"].isArray(), "Assumptions must be an array");
            for (const auto& a : v["assumptions"])
                s.assumptions.push_back(expression(a));
        }
        if (v.isMember("limits")) {
            allowed(v["limits"], { "depth", "states", "wall_ms", "conflicts", "propagations" });
            for (const auto& [name, dest] : std::vector<std::pair<std::string, int64_t*>> { { "depth", &s.limits.depth }, { "states", &s.limits.states }, { "wall_ms", &s.limits.wall_ms }, { "conflicts", &s.limits.conflicts }, { "propagations", &s.limits.propagations } }) {
                if (v["limits"].isMember(name)) {
                    require(v["limits"][name].isInt64(), "Limit must be an integer: " + name);
                    *dest = v["limits"][name].asInt64();
                }
            }
        }
        for (auto n : { "count", "enumerate" })
            if (v.isMember(n)) require(v[n].isBool(), std::string("Expected Boolean: ") + n);
        s.count = v.get("count", false).asBool();
        s.enumerate = v.get("enumerate", false).asBool();
        if (v.isMember("prefix_length")) {
            require(v["prefix_length"].isInt64() && v["prefix_length"].asInt64() > 0, "Prefix length must be positive");
            s.prefix_length = v["prefix_length"].asInt64();
        }
        if (v.isMember("watches")) {
            require(v["watches"].isObject(), "Watches must be an object of Boolean expressions");
            for (const auto& name : v["watches"].getMemberNames())
                s.watches[name] = expression(v["watches"][name]);
        }
        if (v.isMember("explanation")) {
            const auto& options = v["explanation"];
            allowed(options, { "minimize", "checks", "wall_ms", "active_ids", "exact_depth" });
            for (auto key : { "minimize", "exact_depth" })
                if (options.isMember(key)) require(options[key].isBool(), "Explanation flag must be Boolean");
            for (auto key : { "checks", "wall_ms" })
                if (options.isMember(key)) require(options[key].isInt64() && options[key].asInt64() >= 0 && options[key].asInt64() <= 1000000, "Invalid explanation budget");
            if (options.isMember("active_ids")) {
                require(options["active_ids"].isArray(), "active_ids must be an array");
                for (const auto& id : options["active_ids"])
                    require(id.isString(), "Constraint IDs must be strings");
            }
            s.explanation = options;
        }
        if (checking) {
            const bool bounded = s.method == "bmc" || s.method == "induction";
            require(!bounded || (v["limits"].isMember("depth") && s.limits.depth >= (s.method == "induction" ? 1 : 0)), "BMC and induction require an explicit depth");
            require(s.limits.depth <= 10000, "Depth exceeds 10000");
            require(bounded || s.check_variant == "trans" || !v["limits"].isMember("depth"), "Depth is unsupported for this check method");
            require(s.check_variant != "trans" || s.limits.depth > 0, "Transition depth must be positive");
            require(!v["limits"].isMember("states") || s.check_variant == "progress", "States applies only to progress");
            if (s.check_variant == "progress") require(s.limits.states > 0 && s.limits.states <= 1000000, "Invalid progress state limit");
            s.check_target = s.target;
            if (s.check_variant == "invariant" || (s.check_variant == "reachable" && s.method == "induction")) {
                auto property = s.check_variant == "invariant" ? s.target : expr::ExprMgr::INSTANCE().make_not(s.target);
                s.property["name"] = "checked property";
                s.property["expression"] = source::print(property);
                s.target = nullptr;
            }
        }
        s.progress = v["progress"];
        s.trace = v["trace"];
        s.parent_trace = v["parent_trace"];
        return s;
    }
    int run_file(const std::string& path)
    {
        QueryResult r;
        Json::Value output;
        // Machine output contains one complete JSON result; legacy diagnostics go to stderr.
        auto original = std::cout.rdbuf(std::cerr.rdbuf());
        try {
            auto request = trace::read_file(path);
            allowed(request, { "version", "model", "query", "inputs" });
            require(request["version"].isInt() && request["version"].asInt() == 1, "Unsupported query request version");
            require(request["model"].isString(), "Missing model filename");
            auto spec = spec_from_json(request["query"]);
            r.request_id = spec.request_id;
            QueryContext context(spec.limits);
            ContextScope scope(context);
            try {
                context.check(Phase::loading);
                if (request.isMember("inputs")) {
                    require(request["inputs"].isObject(), "Inputs must be an object");
                    for (const auto& name : request["inputs"].getMemberNames())
                        env::Environment::INSTANCE().set(expr::ExprMgr::INSTANCE().make_identifier(name), expression(request["inputs"][name]));
                }
                auto& mm = model::ModelMgr::INSTANCE();
                mm.begin_load();
                require(parse::parseFile(request["model"].asCString()), "Model parse failed");
                const bool valid = mm.analyze();
                context.check(Phase::loading);
                require(valid, "Model validation failed");
                r = execute(spec, context);
            } catch (const Cancelled&) {
                r.reason = context.stop;
                r.status = ExecutionStatus::unknown;
            }
            output = r.json();
            output["constraints"] = source::catalog();
        } catch (const Exception& e) {
            r.status = ExecutionStatus::error;
            r.reason = StopReason::validation_error;
            source::Diagnostic d;
            d.code = "invalid-model";
            d.message = e.what();
            r.diagnostics = source::diagnostics();
            r.diagnostics.push_back(d);
            output = r.json();
            output["constraints"] = source::catalog();
        } catch (const std::invalid_argument& e) {
            r.status = ExecutionStatus::error;
            r.reason = StopReason::validation_error;
            source::Diagnostic d;
            d.code = "invalid-request";
            d.message = e.what();
            r.diagnostics = source::diagnostics();
            r.diagnostics.push_back(d);
            output = r.json();
            output["constraints"] = source::catalog();
        } catch (const std::exception& e) {
            r.status = ExecutionStatus::error;
            r.reason = StopReason::internal_error;
            source::Diagnostic d;
            d.code = "internal-error";
            d.message = e.what();
            r.diagnostics.push_back(d);
            output = r.json();
        }
        // No worker or partial output remains active when the result is published.
        std::cout.rdbuf(original);
        std::cout << output << std::endl;
        return r.exit_code();
    }
} // namespace query
