#ifndef __LAST_H_DEFINED__
#define __LAST_H_DEFINED__

#include <cmd/command.hh>
class Last : public Command {
    pchar f_message;

public:
    Last(Interpreter& owner);
    virtual ~Last();

    utils::Variant virtual operator()();
};
typedef Last* Last_ptr;

class LastTopic : public CommandTopic {
public:
    LastTopic(Interpreter& owner);
    virtual ~LastTopic();

    void virtual usage();
};

#endif
