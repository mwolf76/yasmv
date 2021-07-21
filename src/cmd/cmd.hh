/*
 * @file cmd.hh
 * @brief Command interpreter subsystem related classes and definitions.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/
#ifndef CMD_H
#define CMD_H

#include <cmd/interpreter.hh>

/* -- commands */
#include <cmd/commands/do.hh>
#include <cmd/commands/help.hh>
#include <cmd/commands/echo.hh>
#include <cmd/commands/last.hh>
#include <cmd/commands/on.hh>
#include <cmd/commands/time.hh>
#include <cmd/commands/quit.hh>

#include <cmd/commands/read_model.hh>
#include <cmd/commands/dump_model.hh>

#include <cmd/commands/check.hh>
#include <cmd/commands/check_init.hh>
#include <cmd/commands/check_trans.hh>
#include <cmd/commands/reach.hh>

#include <cmd/commands/pick_state.hh>
#include <cmd/commands/simulate.hh>

#include <cmd/commands/list_traces.hh>
#include <cmd/commands/dump_trace.hh>
#include <cmd/commands/dup_trace.hh>

#include <cmd/commands/get.hh>
#include <cmd/commands/set.hh>
#include <cmd/commands/clear.hh>

class CommandMgr;
typedef CommandMgr* CommandMgr_ptr;

class CommandMgr  {
public:
    static CommandMgr& INSTANCE();

    // -- makers ----------------------------------------------------------------
    inline Command_ptr make_help()
    { return new Help(f_interpreter); }

    inline Command_ptr make_do()
    { return new Do(f_interpreter); }

    inline Command_ptr make_echo()
    { return new Echo(f_interpreter); }

    inline Command_ptr make_last()
    { return new Last(f_interpreter); }

    inline Command_ptr make_on()
    { return new On(f_interpreter); }

    inline Command_ptr make_time()
    { return new Time(f_interpreter); }

    inline Command_ptr make_quit()
    { return new Quit(f_interpreter); }

    inline Command_ptr make_read_model()
    { return new ReadModel(f_interpreter); }

    inline Command_ptr make_dump_model()
    { return new DumpModel(f_interpreter); }

    inline Command_ptr make_check()
    { return new Check(f_interpreter); }

    inline Command_ptr make_reach()
    { return new Reach(f_interpreter); }

    inline Command_ptr make_check_init()
    { return new CheckInit(f_interpreter); }

    inline Command_ptr make_check_trans()
    { return new CheckTrans(f_interpreter); }

    inline Command_ptr make_pick_state()
    { return new PickState(f_interpreter); }

    inline Command_ptr make_simulate()
    { return new Simulate(f_interpreter); }

    inline Command_ptr make_list_traces()
    { return new ListTraces(f_interpreter); }

    inline Command_ptr make_dump_trace()
    { return new DumpTrace(f_interpreter); }

    inline Command_ptr make_dup_trace()
    { return new DupTrace(f_interpreter); }

    inline Command_ptr make_get()
    { return new Get(f_interpreter); }

    inline Command_ptr make_set()
    { return new Set(f_interpreter); }

    inline Command_ptr make_clear()
    { return new Clear(f_interpreter); }

    // -- topicrs ----------------------------------------------------------------
    inline CommandTopic_ptr topic_help()
    { return new HelpTopic(f_interpreter); }

    inline CommandTopic_ptr topic_do()
    { return new DoTopic(f_interpreter); }

    inline CommandTopic_ptr topic_on()
    { return new OnTopic(f_interpreter); }

    inline CommandTopic_ptr topic_echo()
    { return new EchoTopic(f_interpreter); }

    inline CommandTopic_ptr topic_last()
    { return new LastTopic(f_interpreter); }

    inline CommandTopic_ptr topic_time()
    { return new TimeTopic(f_interpreter); }

    inline CommandTopic_ptr topic_quit()
    { return new QuitTopic(f_interpreter); }

    inline CommandTopic_ptr topic_read_model()
    { return new ReadModelTopic(f_interpreter); }

    inline CommandTopic_ptr topic_dump_model()
    { return new DumpModelTopic(f_interpreter); }

    inline CommandTopic_ptr topic_check()
    { return new CheckTopic(f_interpreter); }

    inline CommandTopic_ptr topic_reach()
    { return new ReachTopic(f_interpreter); }

    inline CommandTopic_ptr topic_check_init()
    { return new CheckInitTopic(f_interpreter); }

    inline CommandTopic_ptr topic_check_trans()
    { return new CheckTransTopic(f_interpreter); }

    inline CommandTopic_ptr topic_pick_state()
    { return new PickStateTopic(f_interpreter); }

    inline CommandTopic_ptr topic_simulate()
    { return new SimulateTopic(f_interpreter); }

    inline CommandTopic_ptr topic_list_traces()
    { return new ListTracesTopic(f_interpreter); }

    inline CommandTopic_ptr topic_dump_trace()
    { return new DumpTraceTopic(f_interpreter); }

    inline CommandTopic_ptr topic_dup_trace()
    { return new DupTraceTopic(f_interpreter); }

    inline CommandTopic_ptr topic_get()
    { return new GetTopic(f_interpreter); }

    inline CommandTopic_ptr topic_set()
    { return new SetTopic(f_interpreter); }

    inline CommandTopic_ptr topic_clear()
    { return new ClearTopic(f_interpreter); }

    inline bool is_success(Variant& v)
        { return v.is_string() && v.as_string() == okMessage; }

    inline bool is_failure(Variant& v)
        { return v.is_string() && v.as_string() == errMessage; }

protected:
    CommandMgr();
    ~CommandMgr();

private:
    static CommandMgr_ptr f_instance;
    Interpreter& f_interpreter;
};

#endif
