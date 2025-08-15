#ifndef __LAST_H_DEFINED__
#define __LAST_H_DEFINED__

#include <cmd/command.hh>

namespace cmd {

    class Last final: public Command {
        pchar f_message;

    public:
        explicit Last(Interpreter& owner);
        ~Last() override;

        utils::Variant operator()() override;
    };
    typedef Last* Last_ptr;

    class LastTopic: public CommandTopic {
    public:
        explicit LastTopic(Interpreter& owner);
        ~LastTopic() override;

        void usage() override;
    };

}; // namespace cmd
#endif
