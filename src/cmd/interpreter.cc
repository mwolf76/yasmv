/*
 * @file interpreter.cc
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
#include <command.hh>
#include <interpreter.hh>

Interpreter_ptr Interpreter::f_instance = NULL;
Interpreter& Interpreter::INSTANCE()
{
    if (! f_instance) f_instance = new Interpreter();
    return (*f_instance);
}

Interpreter::Interpreter()
    : f_retcode(0)
    , f_status(READY)

      // default I/O streams
    , f_in(& std::cin)
    , f_out(& std::cout)
    , f_err(& std::cerr)
{
    TRACE << "Initialized command interpreter @" << this << endl;
}

Interpreter::~Interpreter()
{
    TRACE << "Deinitialized command interpreter @" << this << endl;
}

void Interpreter::quit(int retcode)
{
    f_retcode = retcode;
    f_status = LEAVING;
}

extern  ICommand* parseCommand(const char *command); // in utils.cc
void Interpreter::operator()()
{
    string cmdLine; (*f_in) >> cmdLine;
    Command_ptr cmd = parseCommand(cmdLine.c_str());

    if (NULL != cmd) {
        f_status = RUNNING;
        try {
            (*f_out) << "Running..." << endl;
            (*cmd)();
            (*f_out) << "Done." << endl;
        }

        catch (Exception& e) {
        }

        f_status = READY;
    }

    else {
        (*f_out) << "Parsing error" << endl;
    }

}
