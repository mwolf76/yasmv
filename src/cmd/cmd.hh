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

#include <command.hh>
#include <interpreter.hh>

class CommandMgr;
typedef CommandMgr* CommandMgr_ptr;

class CommandMgr  {
public:
    static CommandMgr& INSTANCE()
    {
        if (! f_instance) {
            f_instance = new CommandMgr();
        }

        return (*f_instance);
    }

    // -- makers ----------------------------------------------------------------
    inline Command_ptr make_help(Atom topic)
    { return new HelpCommand(f_interpreter, topic); }

    inline Command_ptr make_time()
    { return new TimeCommand(f_interpreter); }

    inline Command_ptr make_quit(int retcode =0)
    { return new QuitCommand(f_interpreter, retcode); }

    inline Command_ptr make_load_model(const char *filepath)
    { return new LoadModelCommand(f_interpreter, filepath); }

    inline Command_ptr make_init()
    { return new InitCommand(f_interpreter); }

    inline Command_ptr make_simulate(Expr_ptr halt_cond, Expr_ptr resume_id, ExprVector& constraints)
    { return new SimulateCommand(f_interpreter, halt_cond, resume_id, constraints); }

    inline Command_ptr make_check(Expr_ptr formula)
    { return new CheckCommand(f_interpreter, formula); }

    inline Command_ptr make_witness_list()
    { return new WitnessListCommand(f_interpreter); }

    inline Command_ptr make_witness_show(Expr_ptr wid)
    { return new WitnessShowCommand(f_interpreter, wid); }

protected:
    CommandMgr();
    ~CommandMgr();

private:
    static CommandMgr_ptr f_instance;
    Interpreter& f_interpreter;
};

#endif
