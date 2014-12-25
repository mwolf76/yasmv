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

// -- Verify -------------------------------------------------------------
VerifyCommand::VerifyCommand(Interpreter& owner, Expr_ptr formula, ExprVector& constraints)
    : Command(owner)
    , f_bmc(* ModelMgr::INSTANCE().model(), formula, constraints)
{}

Variant VerifyCommand::operator()()
{
    f_bmc.process();

    ostringstream tmp; tmp << f_bmc.status();
    return Variant(tmp.str());
}

VerifyCommand::~VerifyCommand()
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
        tmp << "Simulation done";
        break;
    case SIMULATION_HALTED:
        tmp << "Simulation halted";
        break;
    case SIMULATION_DEADLOCKED:
        tmp << "Simulation deadlocked";
        break;
    case SIMULATION_INTERRUPTED:
        tmp << "Simulation interrupted";
        break;
    default: assert( false ); /* unreachable */
    } /* switch */
    if (f_sim.has_witness()) {
        tmp << ", registered witness '" << f_sim.witness().id() << "'";

        if (1) {
            ostream &os(cout);

            Witness& w (f_sim.witness());
            for (step_t time = w.first_time(); time <= w.last_time(); ++ time) {
                os << "-- @ " << 1 + time << endl;
                TimeFrame& tf = w[ time ];

                SymbIter symbs( *ModelMgr::INSTANCE().model(), NULL );
                while (symbs.has_next()) {

                    ISymbol_ptr symb = symbs.next();
                    Expr_ptr value = NULL;

                    if (symb->is_variable())  {
                        Expr_ptr expr (symb->expr());

                        try {
                            value = tf.value(expr);
                        }
                        catch (NoValue nv) {
                            value = ExprMgr::INSTANCE().make_undef();
                        }
                        os << expr << " = " << value << endl;
                    }
                    else if (symb->is_define()) {
                        Expr_ptr ctx (symb->ctx());
                        Expr_ptr expr (symb->expr());

                        try {
                            value = WitnessMgr::INSTANCE().eval( w, ctx, expr, time);
                        }
                        catch (NoValue nv) {
                            value = ExprMgr::INSTANCE().make_undef();
                        }
                        os << expr << " = " << value << endl;
                    }
                    else {
                        continue;
                    }

                }
                os << endl;
            }
        }
    }
    else {
        tmp << "(no witness available)";
    }
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
    for (step_t time = w.first_time(); time <= w.last_time(); ++ time) {
        os << "-- @ " << 1 + time << endl;
        TimeFrame& tf = w[ time ];

        SymbIter symbs( *ModelMgr::INSTANCE().model(), NULL );
        while (symbs.has_next()) {
            ISymbol_ptr symb = symbs.next();
            Expr_ptr expr (symb->expr());
            Expr_ptr value(tf.value(expr));

            os << symb->expr() << " = " << value << endl;
        }
        os << endl;
    }

    return Variant("Ok");
}

WitnessShowCommand::~WitnessShowCommand()
{}

