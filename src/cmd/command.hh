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
#include <compiler/compiler.hh>
#include <sat.hh>

#include <bmc/bmc.hh>
#include <sim/simulation.hh>

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

/* Initiates a new simulation with given constraint. Simulation will
   autmatically halt on the initial state. */
class InitCommand : public Command {
public:
    InitCommand(Interpreter& owner,
                ExprVector& constraints);

    virtual ~InitCommand();

    Variant virtual operator()();

private:
    // Simulation machinery
    Simulation f_sim;

    // Simulation constraints
    Expr_ptr f_expr;

    // HALT condition
    Expr_ptr f_halt;
};

/* Performs a new simulation with given constraints and halting
   conditions. Simulation can be resumed unless it's last status is
   UNSAT. */
class SimulateCommand : public Command {
public:
    SimulateCommand(Interpreter& owner,
                    Expr_ptr halt_condition,
                    ExprVector& constraints);

    virtual ~SimulateCommand();

    Variant virtual operator()();

private:
    // Simulation machinery
    Simulation f_sim;

    // Simulation constraints
    Expr_ptr f_expr;

    // HALT condition
    Expr_ptr f_halt;
};


/* Simulates running pf model FSM, w/ given constraints. A non-null
   witness ID (i.e. a valid identifer) shall be given to indicate the
   point from which the resumed simulation will begin. */
class ResumeCommand : public Command {
public:
    ResumeCommand(Interpreter& owner,
                  Expr_ptr halt_condition,
                  ExprVector& constraints,
                  Expr_ptr witness_id);

    virtual ~ResumeCommand();

    Variant virtual operator()();

private:
    // Simulation machinery
    Simulation f_sim;

    // Simulation constraints
    Expr_ptr f_expr;

    // HALT condition
    Expr_ptr f_halt;

    // PAUSE condition
    Expr_ptr f_pause;
};

class CheckInvspecCommand : public Command {
public:
    CheckInvspecCommand(Interpreter& owner, Expr_ptr expr);
    virtual ~CheckInvspecCommand();

    Variant virtual operator()();

private:
    // BMC machinery
    BMC f_bmc;

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
