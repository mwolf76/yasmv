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
#include <variant.hh>
#include <interpreter.hh>
#include <expr.hh>
#include <compilers/compiler.hh>
#include <sat.hh>

#include <bmc/bmc.hh>

class ICommand : public IObject {
public:
    // functor-pattern
    Variant virtual operator()() =0;

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
    // from FILE
    LoadModelCommand(Interpreter& owner, const string& filename);

    virtual ~LoadModelCommand();

    Variant virtual operator()();

private:
    string f_filename;
};

class SATCommand : public Command {
public:
    SATCommand(Interpreter& owner, Expr_ptr expr);
    virtual ~SATCommand();

    Variant virtual operator()();

private:
    // SAT machinery
    Minisat::DDTermFactory f_factory;
    Minisat::SAT f_engine;
    Compiler f_compiler;

    // the expr to solve
    Expr_ptr f_expr;
};

class CheckInvspecCommand : public Command {
public:
    CheckInvspecCommand(Interpreter& owner, Expr_ptr expr);
    virtual ~CheckInvspecCommand();

    Variant virtual operator()();

private:
    // BMC machinery
    SATBMCFalsification f_engine;

    // the invariant expr
    Expr_ptr f_expr;
};


class NowCommand : public Command {
public:
    NowCommand(Interpreter& owner);
    virtual ~NowCommand();

    Variant virtual operator()();
};

class FormatCommand : public Command {
public:
    FormatCommand(const char *fmt, ...);
    virtual ~FormatCommand();

    Variant virtual operator()() =0;

private:
    const char *fmt;
};

class QuitCommand : public Command {
public:
    QuitCommand(Interpreter& owner, int retcode);
    virtual ~QuitCommand();

    Variant virtual operator()();

private:
    int f_retcode;
};

#endif
