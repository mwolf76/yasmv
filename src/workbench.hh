#ifndef YASMV_WORKBENCH_HH
#define YASMV_WORKBENCH_HH
#include <cmd/command.hh>
#include <jsoncpp/json/json.h>
#include <string>
#include <vector>
namespace cmd {
    Json::Value read_progress_file(const std::string& path);
    int workbench(const std::vector<std::string>& arguments, bool replace_process);
    void close_workspace();
    class WorkspaceCommand final: public Command {
        std::string f_operation;
        Json::Value f_arguments { Json::objectValue };

    public:
        WorkspaceCommand(Interpreter& owner, const std::string& operation);
        Json::Value& arguments()
        {
            return f_arguments;
        }
        utils::Variant operator()() override;
    };
} // namespace cmd
#endif
