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
#include <cmd/commands/help.hh>
#include <cmd/commands/time.hh>
#include <cmd/commands/quit.hh>

#include <cmd/commands/read_model.hh>
#include <cmd/commands/write_model.hh>

#include <cmd/commands/check_invar.hh>

#include <cmd/commands/pick_state.hh>
#include <cmd/commands/simulate.hh>

#include <cmd/commands/list_traces.hh>
#include <cmd/commands/dump_trace.hh>
#include <cmd/commands/dup_trace.hh>

class CommandMgr;
typedef CommandMgr* CommandMgr_ptr;

class CommandMgr  {
public:
    static CommandMgr& INSTANCE();

    // -- makers ----------------------------------------------------------------
    inline Command_ptr make_help()
    { return new Help(f_interpreter); }

    inline Command_ptr make_time()
    { return new Time(f_interpreter); }

    inline Command_ptr make_quit()
    { return new Quit(f_interpreter); }

    inline Command_ptr make_read_model()
    { return new ReadModel(f_interpreter); }

    inline Command_ptr make_write_model()
    { return new WriteModel(f_interpreter); }

    inline Command_ptr make_check_invar()
    { return new CheckInvar(f_interpreter); }

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

protected:
    CommandMgr();
    ~CommandMgr();

private:
    static CommandMgr_ptr f_instance;
    Interpreter& f_interpreter;
};

#endif
