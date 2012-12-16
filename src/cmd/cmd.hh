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
    inline Command_ptr make_quit(int retcode =0)
    { return new QuitCommand(f_interpreter, retcode); }

    inline Command_ptr make_load_model(const char *filepath)
    { return new LoadModelCommand(f_interpreter, filepath); }

    inline Command_ptr make_sat(Expr_ptr expr)
    { return new SATCommand(f_interpreter, expr); }

    inline Command_ptr make_simulate(int resume, int nsteps, ExprVector& constraints)
    { return new SimulateCommand(f_interpreter, resume, nsteps, constraints); }

    inline Command_ptr make_check_invspec(Expr_ptr expr)
    { return new CheckInvspecCommand(f_interpreter, expr); }

    inline Command_ptr make_now()
    { return new NowCommand(f_interpreter); }

protected:
    CommandMgr();
    ~CommandMgr();

private:
    static CommandMgr_ptr f_instance;
    Interpreter& f_interpreter;
};


#endif
