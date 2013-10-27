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
    , f_leaving(false)

      // default I/O streams
    , f_in(& std::cin)
    , f_out(& std::cout)
    , f_err(& std::cerr)
{
    DEBUG << "Initialized command interpreter @" << this << endl;
}

Interpreter::~Interpreter()
{
    DEBUG << "Deinitialized command interpreter @" << this << endl;
}

void Interpreter::quit(int retcode)
{
    f_retcode = retcode;
    f_leaving = true;
}

extern  ICommand* parseCommand(const char *command); // in utils.cc
Variant& Interpreter::operator()(Command_ptr cmd)
{
    assert(NULL != cmd);

    try {
        f_last_result = (*cmd)();
    }

    catch (Exception& e) {
        f_last_result = Variant(e.what());
    }

    delete cmd;
    return f_last_result;
}

Variant& Interpreter::operator()()
{
    bool color (OptsMgr::INSTANCE().color());
    // cmd prompt
    f_last_result = Variant("Parsing Error");

    if (color) {
        (*f_out) <<  cyan << ">> " << normal;
    }
    else {
        (*f_out) <<  ">> ";
    }

    string cmdLine;
    if (std::getline(*f_in, cmdLine)) {
        (*f_out) << "<< " << cmdLine << endl;
        Command_ptr cmd = parseCommand(cmdLine.c_str());

        if (NULL != cmd) {
            (*this)(cmd);
        }
    }
    else {
        f_last_result = Variant("BYE");
        f_leaving = true;
    }

    return f_last_result;
}
