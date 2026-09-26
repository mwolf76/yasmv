#include <algorithms/base.hh>
#include <cerrno>
#include <env/environment.hh>
#include <parse.hh>
#include <query/trace.hh>
#include <sys/prctl.h>
#include <sys/wait.h>
#include <unistd.h>

namespace query {
    namespace {
        void require(bool condition, const char* message)
        {
            if (!condition) throw std::invalid_argument(message);
        }
        Json::Value error(const std::string& id, const std::string& message, bool internal = false)
        {
            QueryResult r;
            r.request_id = id;
            r.status = ExecutionStatus::error;
            r.reason = internal ? StopReason::internal_error : StopReason::validation_error;
            source::Diagnostic d;
            d.code = internal ? "session-worker-failed" : "invalid-session-request";
            d.message = message;
            r.diagnostics = source::diagnostics();
            r.diagnostics.push_back(d);
            return r.json();
        }
    } // namespace
    int run_session(const std::string& path)
    {
        // The snapshot owns every legacy manager through its process lifetime.
        // No QueryContext or background thread is alive at a fork boundary.
        auto original = std::cout.rdbuf(std::cerr.rdbuf());
        std::ostream machine(original);
        Json::StreamWriterBuilder writer;
        writer["indentation"] = "";
        auto send = [&](const Json::Value& v) { machine << Json::writeString(writer, v) << std::endl; };
        try {
            const auto request = trace::read_file(path);
            require(request.isObject(), "Expected session configuration");
            for (const auto& key : request.getMemberNames())
                require(key == "version" || key == "model" || key == "inputs", "Unknown session field");
            require(request["version"].isInt() && request["version"].asInt() == 1 && request["model"].isString(), "Invalid session version or model");
            if (request.isMember("inputs")) {
                require(request["inputs"].isObject(), "Expected input map");
                for (const auto& name : request["inputs"].getMemberNames()) {
                    require(request["inputs"][name].isString(), "Input value must be an expression");
                    auto e = parse::parseExpression(request["inputs"][name].asCString());
                    require(e != nullptr, "Invalid input expression");
                    env::Environment::INSTANCE().set(expr::ExprMgr::INSTANCE().make_identifier(name), e);
                }
            }
            const auto start = std::chrono::steady_clock::now();
            auto& mm = model::ModelMgr::INSTANCE();
            mm.begin_load();
            require(parse::parseFile(request["model"].asCString()) && mm.analyze(), "Model validation failed");
            algorithms::Algorithm compiled(mm.model());
            const auto fingerprint = identity();
            const auto catalog = source::catalog();
            algorithms::Algorithm::reuse(&compiled);
            // Parent must die promptly on runner shutdown, also while blocked on stdin.
            struct sigaction action {};
            action.sa_handler = signal_handler;
            sigemptyset(&action.sa_mask);
            sigaction(SIGTERM, &action, nullptr);
            sigaction(SIGINT, &action, nullptr);
            Json::Value ready;
            ready["version"] = 1;
            ready["status"] = "ready";
            ready["identity"] = fingerprint;
            ready["constraints"] = catalog;
            ready["load_ms"] = std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - start).count();
            send(ready);
            std::string line;
            while (!signal_pending && std::getline(std::cin, line)) {
                if (line.size() > 16 * 1024 * 1024) {
                    send(error("", "Session query exceeds 16 MiB"));
                    continue;
                }
                // Fork before parsing expressions: request internals never enter the snapshot.
                const pid_t parent = getpid();
                pid_t child = fork();
                if (child < 0) throw std::runtime_error("Cannot fork query worker");
                if (child == 0) {
                    prctl(PR_SET_PDEATHSIG, SIGKILL);
                    if (getppid() != parent) _exit(4);
                    signal_pending = 0;
                    signal(SIGTERM, signal_handler);
                    signal(SIGINT, signal_handler);
                    Json::Value response;
                    std::string id;
                    try {
                        Json::CharReaderBuilder reader;
                        reader["rejectDupKeys"] = true;
                        reader["failIfExtra"] = true;
                        Json::Value value;
                        std::string errors;
                        std::istringstream stream(line);
                        require(Json::parseFromStream(reader, stream, &value, &errors), "Invalid query JSON");
                        if (value["request_id"].isString()) id = value["request_id"].asString();
                        auto spec = spec_from_json(value);
                        response = execute(spec).json();
                        response["constraints"] = source::catalog();
                        response["statistics"]["compiled_snapshot"] = true;
                    } catch (const Exception& e) {
                        response = error(id, e.what());
                    } catch (const std::exception& e) {
                        response = error(id, e.what());
                    }
                    send(response);
                    // OS reclamation includes singleton arenas and all query-local caches.
                    _exit(0);
                }
                int status = 0;
                while (true) {
                    if (signal_pending) kill(child, SIGKILL);
                    if (waitpid(child, &status, 0) >= 0) break;
                    if (errno != EINTR) throw std::runtime_error("Cannot reap query worker");
                }
                if (signal_pending) break;
                if (!WIFEXITED(status) || WEXITSTATUS(status) != 0)
                    send(error("", "Isolated query worker terminated without a result", true));
            }
            algorithms::Algorithm::reuse(nullptr);
        } catch (const Exception& e) {
            send(error("", e.what()));
            std::cout.rdbuf(original);
            return 2;
        } catch (const std::exception& e) {
            send(error("", e.what()));
            std::cout.rdbuf(original);
            return 2;
        }
        std::cout.rdbuf(original);
        return 0;
    }
} // namespace query
