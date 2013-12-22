/*
 * @file command.cc
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
#include <ctime>
#include <common.hh>
#include <command.hh>

#include <expr.hh>
#include <mc.hh>
#include <sat.hh>

Command::Command(Interpreter& owner)
    : f_owner(owner)
{ DRIVEL << "Initialized command @" << this << endl; }

Command::~Command()
{ DRIVEL << "Deinitialized command @" << this << endl; }

LoadModelCommand::LoadModelCommand(Interpreter& owner, const string &filename)
    : Command(owner)
    , f_filename(filename)
{}

extern void parseFile(const char *filepath); // in utils.cc
Variant LoadModelCommand::operator()()
{
    // parsing
    parseFile(f_filename.c_str());

    // model analysis
    bool status = ModelMgr::INSTANCE().analyze();

    return Variant( status ? "OK" : "ERROR" );
}

LoadModelCommand::~LoadModelCommand()
{}

// -- Now ---------------------------------------------------------------
NowCommand::NowCommand(Interpreter& owner)
    : Command(owner)
{}

Variant NowCommand::operator()()
{
    return Variant(clock());
}

NowCommand::~NowCommand()
{}

// -- SAT ----------------------------------------------------------------------
SATCommand::SATCommand(Interpreter& owner, Expr_ptr expr)
    : Command(owner)
    , f_factory(CuddMgr::INSTANCE().dd())
    , f_engine(/* f_factory */)
    , f_compiler()
    , f_expr(expr)
{}

Variant SATCommand::operator()()
{
#if 0
    Expr_ptr ctx = ExprMgr::INSTANCE().make_main(); // default ctx
    ADD add = f_compiler.process(ctx, f_expr);
    f_engine.push(add, 0);

    ostringstream tmp;
    tmp << f_engine.solve();
    return Variant(tmp.str());
#endif

    return Variant ("Unsupported");
}

SATCommand::~SATCommand()
{}

// -- CheckInvspec -------------------------------------------------------------
CheckInvspecCommand::CheckInvspecCommand(Interpreter& owner, Expr_ptr invariant)
    : Command(owner)
    , f_bmc(* ModelMgr::INSTANCE().model(),
            invariant)
{}

Variant CheckInvspecCommand::operator()()
{
    f_bmc.process();

    ostringstream tmp; tmp << f_bmc.status();
    return Variant(tmp.str());
}

CheckInvspecCommand::~CheckInvspecCommand()
{}

// -- INIT  ----------------------------------------------------------------
InitCommand::InitCommand(Interpreter& owner,
                         ExprVector& constraints)
    : Command(owner)
    , f_sim(* ModelMgr::INSTANCE().model(),
            ExprMgr::INSTANCE().make_true(), constraints)
{}

Variant InitCommand::operator()()
{
    f_sim.process();

    ostringstream tmp;
    tmp << "Simulation is ";
    tmp << ((f_sim.status() == SIMULATION_SAT) ? "SAT" : "UNSAT");

    return Variant(tmp.str());
}

InitCommand::~InitCommand()
{}

// -- SIMULATE  ----------------------------------------------------------------
SimulateCommand::SimulateCommand(Interpreter& owner,
                                 Expr_ptr halt_cond,
                                 ExprVector& constraints)
    : Command(owner)
    , f_sim(* ModelMgr::INSTANCE().model(),
            halt_cond, constraints)
{}

Variant SimulateCommand::operator()()
{
    f_sim.process();

    ostringstream tmp;
    tmp << "Simulation is ";
    tmp << ((f_sim.status() == SIMULATION_SAT) ? "SAT" : "UNSAT");

    return Variant(tmp.str());
}

SimulateCommand::~SimulateCommand()
{}

// -- RESUME  ----------------------------------------------------------------
ResumeCommand::ResumeCommand(Interpreter& owner,
                             Expr_ptr halt_cond,
                             ExprVector& constraints,
                             Expr_ptr witness_id)
    : Command(owner)
    , f_sim(* ModelMgr::INSTANCE().model(),
            halt_cond, constraints, witness_id)
{}

Variant ResumeCommand::operator()()
{
    f_sim.process();

    ostringstream tmp;
    tmp << "Simulation is ";
    tmp << ((f_sim.status() == SIMULATION_SAT) ? "SAT" : "UNSAT");

    return Variant(tmp.str());
}

ResumeCommand::~ResumeCommand()
{}

// -- QUIT ---------------------------------------------------------------------
QuitCommand::QuitCommand(Interpreter& owner, int retcode)
    : Command(owner)
    , f_retcode(retcode)
{}

// sends a signal to the owner
Variant QuitCommand::operator()()
{
    f_owner.quit(f_retcode);
    return Variant("BYE");
}

QuitCommand::~QuitCommand()
{}
