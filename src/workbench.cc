#include <cerrno>
#include <cmd/commands/commands.hh>
#include <cmd/interpreter.hh>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <iostream>
#include <poll.h>
#include <query/query.hh>
#include <query/source.hh>
#include <query/trace.hh>
#include <signal.h>
#include <sstream>
#include <sys/prctl.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <unistd.h>
#include <witness/witness_mgr.hh>
#include <workbench.hh>

namespace cmd {
    Json::Value read_progress_file(const std::string& path) { return query::trace::read_file(path); }
    int workbench(const std::vector<std::string>& arguments, bool replace_process)
    {
        namespace fs = std::filesystem;
        std::error_code error;
        const auto binary = fs::read_symlink("/proc/self/exe", error);
        if (error) {
            std::cerr << "Cannot locate yasmv executable: " << error.message() << '\n';
            return 2;
        }
        fs::path script;
        for (const auto& root : { binary.parent_path(), binary.parent_path().parent_path() / "share/yasmv", fs::path(YASMV_CLIENT_DATA), fs::path(YASMV_CLIENT_SOURCE) }) {
            auto candidate = root / "tools/workbench/launch.py";
            if (fs::is_regular_file(candidate, error)) {
                script = candidate;
                break;
            }
        }
        if (script.empty()) {
            std::cerr << "Workbench client is missing; install the yasmv data files.\n";
            return 2;
        }
        std::vector<std::string> storage { "python3", script.string(), "--binary", binary.string() };
        storage.insert(storage.end(), arguments.begin(), arguments.end());
        std::vector<char*> argv;
        for (auto& arg : storage)
            argv.push_back(arg.data());
        argv.push_back(nullptr);
        pid_t child = 0;
        if (!replace_process) {
            std::cout.flush();
            std::cerr.flush();
            child = fork();
            if (child == -1) {
                std::cerr << "Cannot start workbench: " << strerror(errno) << '\n';
                return 4;
            }
        }
        if (child == 0) {
            execvp(argv[0], argv.data());
            std::cerr << "Cannot start Python 3 workbench: " << strerror(errno) << '\n';
            if (!replace_process) _exit(2);
            return 2;
        }
        int status;
        while (waitpid(child, &status, 0) == -1) {
            if (errno == EINTR) continue;
            return 4;
        }
        return WIFEXITED(status) ? WEXITSTATUS(status) : 3;
    }

    namespace {
        int channel = -1;
        pid_t service = -1;
        std::string received;

        void start_workspace()
        {
            if (channel != -1) return;
            int sockets[2];
            if (socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, sockets)) throw std::runtime_error("Cannot create workspace channel");
            std::cout.flush();
            std::cerr.flush();
            service = fork();
            if (service == -1) {
                close(sockets[0]);
                close(sockets[1]);
                throw std::runtime_error("Cannot start workspace service");
            }
            if (service == 0) {
                close(sockets[0]);
                setsid();
                prctl(PR_SET_PDEATHSIG, SIGTERM);
                dup2(sockets[1], STDIN_FILENO);
                dup2(sockets[1], STDOUT_FILENO);
                close(sockets[1]);
                _exit(workbench({ "bridge" }, true));
            }
            close(sockets[1]);
            channel = sockets[0];
            std::atexit(close_workspace);
        }

        Json::Value exchange(const Json::Value& request)
        {
            start_workspace();
            query::signal_pending = 0;
            Json::StreamWriterBuilder writer;
            writer["indentation"] = "";
            const auto text = Json::writeString(writer, request) + "\n";
            size_t offset = 0;
            while (offset < text.size()) {
                auto count = send(channel, text.data() + offset, text.size() - offset, MSG_NOSIGNAL);
                if (count < 0 && errno == EINTR) continue;
                if (count <= 0) throw std::runtime_error("Workspace service disconnected");
                offset += count;
            }
            while (received.find('\n') == std::string::npos) {
                if (query::signal_pending) {
                    query::signal_pending = 0;
                    kill(service, SIGINT);
                }
                pollfd descriptor { channel, POLLIN, 0 };
                const auto ready = poll(&descriptor, 1, 100);
                if (ready < 0 && errno == EINTR) continue;
                if (ready < 0) throw std::runtime_error("Workspace channel poll failed");
                if (!ready) continue;
                char buffer[8192];
                auto count = recv(channel, buffer, sizeof(buffer), 0);
                if (count < 0 && errno == EINTR) continue;
                if (count <= 0) throw std::runtime_error("Workspace service disconnected");
                received.append(buffer, count);
                if (received.size() > 64 * 1024 * 1024) throw std::runtime_error("Workspace response exceeds 64 MiB");
            }
            auto end = received.find('\n');
            std::istringstream input(received.substr(0, end));
            received.erase(0, end + 1);
            Json::Value response;
            input >> response;
            if (!response.isObject() || !response["result"].isObject() || !response["result"]["status"].isString() || !response["text"].isString()) {
                throw std::runtime_error("Invalid workspace service response");
            }
            return response;
        }

        Json::Value shell_context()
        {
            Json::Value context(Json::objectValue);
            auto& mm = model::ModelMgr::INSTANCE();
            if (!mm.valid()) return context;
            auto identity = query::identity();
            context["identity"] = identity;
            context["document"]["source"] = source::contents();
            context["document"]["name"] = source::filename();
            context["document"]["root"] = identity["root"];
            context["document"]["inputs"] = identity["inputs"];
            context["microcode_directory"] = opts::OptsMgr::INSTANCE().cnf_microcode_directory();
            auto& wm = witness::WitnessMgr::INSTANCE();
            if (!wm.witnesses().empty()) {
                auto& current = wm.current();
                context["trace"] = current.artifact;
                context["trace_name"] = std::string(current.id());
                context["traces"] = Json::objectValue;
                for (auto w : wm.witnesses())
                    context["traces"][std::string(w->id())] = w->artifact;
            }
            return context;
        }
    } // namespace

    void close_workspace()
    {
        if (channel == -1) return;
        shutdown(channel, SHUT_WR);
        close(channel);
        channel = -1;
        int status;
        // The service receives EOF, cancels jobs, closes snapshots and reaps workers.
        while (waitpid(service, &status, 0) < 0 && errno == EINTR) {}
        service = -1;
        received.clear();
    }

    WorkspaceCommand::WorkspaceCommand(Interpreter& owner, const std::string& operation)
        : Command(owner)
        , f_operation(operation)
    {}

    utils::Variant WorkspaceCommand::operator()()
    {
        Json::Value request;
        request["operation"] = f_operation;
        request["arguments"] = f_arguments;
        request["context"] = shell_context();
        Json::Value response;
        try {
            response = exchange(request);
        } catch (...) {
            if (service > 0) kill(service, SIGTERM);
            close_workspace();
            throw;
        }
        const auto& result = response["result"];
        const auto status = result["status"].asString();
        if (response.isMember("trace") && !response["trace"].isNull()) {
            // Join worker evidence to the same native trace register used by
            // dump-trace, select-trace, read-trace, echo and simulate.
            query::QuerySpec spec;
            spec.operation = query::Operation::validate_trace;
            spec.trace = response["trace"];
            const auto replay = query::checked(spec);
            if (replay.status == query::ExecutionStatus::unknown) {
                std::cout << wrnPrefix << "Trace import interrupted; native selection preserved." << std::endl;
                return utils::Variant(unknownMessage);
            }
            if (replay.outcome != query::Outcome::valid) throw std::invalid_argument("Worker trace failed replay in the current shell model");
            auto& wm = witness::WitnessMgr::INSTANCE();
            const auto name = "workspace_" + std::to_string(wm.autoincrement());
            replay.witness->set_id(name);
            replay.witness->artifact = spec.trace;
            wm.record(*replay.witness);
            wm.set_current(*replay.witness);
            std::cout << outPrefix << "Selected trace `" << name << "`." << std::endl;
        }
        std::cout << response.get("text", "").asString() << std::flush;
        if (status == "unknown") return utils::Variant(unknownMessage);
        if (status == "error") {
            const auto reason = result.get("stop_reason", "").asString();
            f_owner.record_error(reason == "internal_error" || reason == "worker_failed" ? 4 : 2);
            return utils::Variant(errMessage);
        }
        const auto outcome = result.get("outcome", "").asString();
        return utils::Variant(outcome == "unreachable" || outcome == "unsatisfiable" || outcome == "violated" || outcome == "invalid" || outcome == "deadlocked" || outcome == "diverged" ? errMessage : okMessage);
    }
} // namespace cmd
