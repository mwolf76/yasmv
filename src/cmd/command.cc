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

/* algorithms */
#include <bmc/bmc.hh>
#include <sim/simulation.hh>

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

    return Variant( status ? "Ok" : "ERROR" );
}

LoadModelCommand::~LoadModelCommand()
{}

// -- Help ---------------------------------------------------------------
HelpCommand::HelpCommand(Interpreter& owner, Atom topic)
    : Command(owner)
    , f_topic(topic)
{}

Variant HelpCommand::operator()()
{
    return Variant(clock());
}

HelpCommand::~HelpCommand()
{}

// -- Time ---------------------------------------------------------------
TimeCommand::TimeCommand(Interpreter& owner)
    : Command(owner)
{}

Variant TimeCommand::operator()()
{
    return Variant( clock());
}

TimeCommand::~TimeCommand()
{}

// -- Init -------------------------------------------------------------
InitCommand::InitCommand(Interpreter& owner)
    : Command(owner)
    , f_init(* ModelMgr::INSTANCE().model())
{}

Variant InitCommand::operator()()
{
    f_init.process();
    return Variant("Ok");
}

InitCommand::~InitCommand()
{}

// -- Check -------------------------------------------------------------
CheckCommand::CheckCommand(Interpreter& owner, Expr_ptr formula)
    : Command(owner)
    , f_bmc(* ModelMgr::INSTANCE().model(), formula)
{}

Variant CheckCommand::operator()()
{
    f_bmc.process();

    ostringstream tmp; tmp << f_bmc.status();
    return Variant(tmp.str());
}

CheckCommand::~CheckCommand()
{}

// -- SIMULATE  ----------------------------------------------------------------
SimulateCommand::SimulateCommand(Interpreter& owner,
                                 Expr_ptr halt_cond,
                                 Expr_ptr resume_id,
                                 ExprVector& constraints)
    : Command(owner)
    , f_sim(* ModelMgr::INSTANCE().model(),
            halt_cond, resume_id, constraints)
{}

Variant SimulateCommand::operator()()
{
    ostringstream tmp;
    f_sim.process();

    switch (f_sim.status()) {
    case SIMULATION_DONE:
        tmp << "Simulation done, see witness '" << f_sim.witness().id() << "'";
        break;
    case SIMULATION_HALTED:
        tmp << "Simulation halted, see witness '" << f_sim.witness().id() << "'";
        break;
    case SIMULATION_DEADLOCKED:
        tmp << "Simulation deadlocked, see witness '" << f_sim.witness().id() << "'";
        break;
    case SIMULATION_INTERRUPTED:
        tmp << "Simulation interrupted, see witness '" << f_sim.witness().id() << "'";
        break;
    default: assert( false ); /* unreachable */
    } /* switch */

    return Variant(tmp.str());
}

SimulateCommand::~SimulateCommand()
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

// -- WITNESS  ----------------------------------------------------------------
WitnessListCommand::WitnessListCommand(Interpreter& owner)
    : Command(owner)
{}

Variant WitnessListCommand::operator()()
{
    ostream &os(cout);

    const WitnessMap& map(WitnessMgr::INSTANCE().witnesses());
    for (WitnessMap::const_iterator eye = map.begin(); eye != map.end(); ++ eye) {
        os << (*eye).first << endl;
    }
    os << endl;

    return Variant("Ok");
}

WitnessListCommand::~WitnessListCommand()
{}

WitnessShowCommand::WitnessShowCommand(Interpreter& owner, Expr_ptr wid)
    : Command(owner)
    , f_wid(wid)
{}

Variant WitnessShowCommand::operator()()
{
    ostream &os(cout);

    Witness& w = WitnessMgr::INSTANCE().witness( f_wid->atom() );
    for (step_t k = 0; k < w.size(); ++ k) {
        os << " -- @ " << 1 + k << " -- " << endl;
        TimeFrame& tf = w[ k ];
        SymbIter symbs( *ModelMgr::INSTANCE().model(), NULL );
        while (symbs.has_next()) {
            ISymbol_ptr symb = symbs.next();
            FQExpr key(symb->ctx(), symb->expr(), k);
            os << symb->expr() << " = " << tf.value(key) << endl;
        }
    }

    return Variant("Ok");
}

WitnessShowCommand::~WitnessShowCommand()
{}

