/*
 * @file command.hh
 * @brief Command-interpreter subsystem
 *
 * This header file contains the declarations required by the Command
 * class.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#ifndef COMMAND_H
#define COMMAND_H

#include <common/common.hh>
#include <expr/expr.hh>
#include <cmd/typedefs.hh>
#include <cmd/exceptions.hh>
#include <utils/variant.hh>

#include <string>

namespace cmd {

class Interpreter;

class Command {
protected:
    Interpreter& f_owner;

public:
    Command(Interpreter& owner);
    virtual ~Command();

    // functor-pattern
    utils::Variant virtual operator()() =0;

    // representation
    friend std::ostream& operator<<(std::ostream& os, Command& cmd);
};

class CommandTopic {
protected:
    Interpreter& f_owner;
    void display_manpage(const char *topic);

public:
    CommandTopic(Interpreter& owner);
    virtual ~CommandTopic();

    // inline help system
    void virtual usage() =0;
};

typedef std::vector<Command_ptr> CommandVector;
typedef CommandVector* CommandVector_ptr;

};

#endif /* COMMAND_H */
