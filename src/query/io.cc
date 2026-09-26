#include <env/environment.hh>
#include <fstream>
#include <map>
#include <parse.hh>
#include <query/query.hh>
#include <query/trace.hh>
namespace query {
    static const std::map<std::string, Operation> operations = { { "check-init", Operation::check_init }, { "check-trans", Operation::check_trans }, { "pick-state", Operation::pick_state }, { "reach", Operation::reach }, { "simulate", Operation::simulate }, { "diameter", Operation::diameter }, { "validate-trace", Operation::validate_trace } };
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
        v["strategy"] = s.strategy;
        v["assumptions"] = Json::arrayValue;
        for (auto e : s.assumptions)
            v["assumptions"].append(source::print(e));
        if (s.target) v["target"] = source::print(s.target);
        if (s.until) v["until"] = source::print(s.until);
        v["enumerate"] = s.enumerate;
        v["count"] = s.count;
        v["trace_id"] = s.trace_id;
        v["limits"]["depth"] = Json::Int64(s.limits.depth);
        v["limits"]["states"] = Json::Int64(s.limits.states);
        v["limits"]["wall_ms"] = Json::Int64(s.limits.wall_ms);
        v["limits"]["conflicts"] = Json::Int64(s.limits.conflicts);
        v["limits"]["propagations"] = Json::Int64(s.limits.propagations);
        if (!s.parent_trace.isNull()) v["parent_trace"] = s.parent_trace;
        return v;
    }
    QuerySpec spec_from_json(const Json::Value& v)
    {
        allowed(v, { "operation", "request_id", "strategy", "target", "until", "assumptions", "limits", "enumerate", "count", "trace_id", "trace", "parent_trace" });
        require(v["operation"].isString() && operations.count(v["operation"].asString()), "Unsupported query operation");
        QuerySpec s;
        s.operation = operations.at(v["operation"].asString());
        for (auto n : { "request_id", "strategy", "trace_id" })
            if (v.isMember(n)) require(v[n].isString(), std::string("Expected string: ") + n);
        s.request_id = v.get("request_id", "").asString();
        s.strategy = v.get("strategy", "auto").asString();
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
