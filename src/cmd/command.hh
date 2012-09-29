/*
 * @file command.hh
 * @brief Command-interpreter subsystem related classes and definitions.
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
#ifndef COMMAND_H
#define COMMAND_H

#include <common.hh>
#include <interpreter.hh>

class ICommand : public IObject {
public:
    // functor-pattern
    void virtual operator()() =0;

    // representation
    friend ostream& operator<<(ostream& os, ICommand& cmd);
};

// -- command definitions --------------------------------------------------
class Command : public ICommand {
public:
    Command(Interpreter& owner);
    virtual ~Command();

protected:
    Interpreter& f_owner;
};
typedef class ICommand* Command_ptr;

class LoadModelCommand : public Command {
public:
    LoadModelCommand(Interpreter& owner, const string& filename);
    virtual ~LoadModelCommand();

    void virtual operator()() =0;

private:
    string f_filename;
};

class FormatCommand : public Command {
public:
    FormatCommand(const char *fmt, ...);
    virtual ~FormatCommand();

    void virtual operator()() =0;

private:
    const char *fmt;
};

class QuitCommand : public Command {
public:
    QuitCommand(Interpreter& owner, int retcode);
    virtual ~QuitCommand();

    void virtual operator()();

private:
    int f_retcode;
};

#endif
