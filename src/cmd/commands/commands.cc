/*
 * @file commands.cc
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
#include <iostream>
#include <sstream>

#include <ctime>
#include <common.hh>
#include <commands.hh>

#include <expr.hh>

/* algorithms */
#include <bmc/bmc.hh>
#include <sim/simulation.hh>

Command::Command(Interpreter& owner)
    : f_owner(owner)
{
    DRIVEL
        << "Initialized command @" << this
        << std::endl;
}

Command::~Command()
{
    DRIVEL << "Deinitialized command @" << this
           << std::endl;
}

ModelLoadCommand::ModelLoadCommand(Interpreter& owner, const std::string &filename)
    : Command(owner)
    , f_filename(filename)
{}

extern void parseFile(const char *filepath); // in utils.cc
Variant ModelLoadCommand::operator()()
{
    // parsing
    parseFile(f_filename.c_str());

    // model analysis
    bool status = ModelMgr::INSTANCE().analyze();

    return Variant( status ? "Ok" : "ERROR" );
}

ModelLoadCommand::~ModelLoadCommand()
{}

ModelDumpCommand::ModelDumpCommand(Interpreter& owner)
    : Command(owner)
{}

Variant ModelDumpCommand::operator()()
{
    std::ostringstream oss;

    Model& model (ModelMgr::INSTANCE().model());

    oss
        << std::endl
        << std::endl;

    const Modules& modules (model.modules());
    for (Modules::const_iterator m = modules.begin();
         m != modules.end(); ++ m) {

        Module& module = dynamic_cast <Module&> (*m->second);

        oss
            << "MODULE "
            << module.name()
            << std::endl;

        /* INIT */
        const ExprVector init = module.init();
        if (init.begin() != init.end())
            oss << std::endl;
        for (ExprVector::const_iterator init_eye = init.begin();
             init_eye != init.end(); ++ init_eye) {

            Expr_ptr body (*init_eye);

            oss
                << "INIT "
                << body << ";"
                << std::endl;

        }

        /* INVAR */
        const ExprVector invar = module.invar();
        if (invar.begin() != invar.end())
            oss << std::endl;
        for (ExprVector::const_iterator invar_eye = invar.begin();
             invar_eye != invar.end(); ++ invar_eye) {

            Expr_ptr body (*invar_eye);

            oss
                << "INVAR "
                << body << ";"
                << std::endl;
        }

        /* TRANS */
        const ExprVector trans = module.trans();
        if (trans.begin() != trans.end())
            oss << std::endl;
        for (ExprVector::const_iterator trans_eye = trans.begin();
             trans_eye != trans.end(); ++ trans_eye) {

            Expr_ptr body (*trans_eye);

            oss
                << "TRANS "
                << body << ";"
                << std::endl;
        }
    }

    return Variant (oss.str());
}

ModelDumpCommand::~ModelDumpCommand()
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
    , f_init(*this, ModelMgr::INSTANCE().model())
{}

Variant InitCommand::operator()()
{
    f_init.process();
    return Variant("Ok");
}

InitCommand::~InitCommand()
{}

// -- JOB  ----------------------------------------------------------------
JobListCommand::JobListCommand(Interpreter& owner)
    : Command(owner)
{}

Variant JobListCommand::operator()()
{
    Jobs::const_iterator eye;
    std::ostream &os(std::cout);

    const Jobs& jobs(Interpreter::INSTANCE().jobs());
    for (eye = jobs.begin(); eye != jobs.end(); ++ eye) {
        os
            << (*eye) -> id()
            << "\t\t"
            << (*eye) -> elapsed()
            << std::endl;

    }
    os << std::endl;

    return Variant("Ok");
}

JobListCommand::~JobListCommand()
{}

JobStatusCommand::JobStatusCommand(Interpreter& owner, Expr_ptr wid)
    : Command(owner)
    , f_wid(wid)
{}

Variant JobStatusCommand::operator()()
{
    // ostream &os(cout);

    // Job& w = Interpreter::INSTANCE().job( f_wid->atom() );
    // for (step_t time = w.first_time(); time <= w.last_time(); ++ time) {
    //     os << "-- @ " << 1 + time << std::endl;
    //     TimeFrame& tf = w[ time ];

    //     SymbIter symbs( *ModelMgr::INSTANCE().model(), NULL );
    //     while (symbs.has_next()) {
    //         ISymbol_ptr symb = symbs.next();
    //         Expr_ptr expr (symb->expr());
    //         Expr_ptr value(tf.value(expr));

    //         os << symb->expr() << " = " << value << std::endl;
    //     }
    //     os << std::endl;
    // }

    return Variant("Ok");
}

JobStatusCommand::~JobStatusCommand()
{}

JobKillCommand::JobKillCommand(Interpreter& owner, Expr_ptr wid)
    : Command(owner)
    , f_wid(wid)
{}

Variant JobKillCommand::operator()()
{
    // ostream &os(cout);

    // Job& w = JobMgr::INSTANCE().job( f_wid->atom() );
    // for (step_t time = w.first_time(); time <= w.last_time(); ++ time) {
    //     os << "-- @ " << 1 + time << std::endl;
    //     TimeFrame& tf = w[ time ];

    //     SymbIter symbs( *ModelMgr::INSTANCE().model(), NULL );
    //     while (symbs.has_next()) {
    //         ISymbol_ptr symb = symbs.next();
    //         Expr_ptr expr (symb->expr());
    //         Expr_ptr value(tf.value(expr));

    //         os << symb->expr() << " = " << value << std::endl;
    //     }
    //     os << std::endl;
    // }

    return Variant("Ok");
}

JobKillCommand::~JobKillCommand()
{}

// -- Verify -------------------------------------------------------------
VerifyCommand::VerifyCommand(Interpreter& owner, Expr_ptr formula, ExprVector& constraints)
    : Command(owner)
    , f_bmc(*this, ModelMgr::INSTANCE().model(),
            formula, constraints)
{}

Variant VerifyCommand::operator()()
{
    std::ostringstream tmp;
    f_bmc.process();

    switch (f_bmc.status()) {
    case MC_FALSE:
        tmp << "Property is FALSE";
        break;
    case MC_TRUE:
        tmp << "Property is TRUE";
        break;
    case MC_UNKNOWN:
        tmp << "Property could not be decided";
        break;
    default: assert( false ); /* unreachable */
    } /* switch */
    if (f_bmc.has_witness()) {
        tmp
            << ", registered CEX witness `"
            << f_bmc.witness().id()
            << "`";
    }

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
    , f_sim(*this, ModelMgr::INSTANCE().model(),
            halt_cond, resume_id, constraints)
{}

Variant SimulateCommand::operator()()
{
    std::ostringstream tmp;
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
        tmp
            << ", registered witness `"
            << f_sim.witness().id() << "`";
    }
    else {
        tmp
            << "(no witness available)";
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
    WitnessList::const_iterator eye;
    std::ostream &os(std::cout);

    const WitnessList& witnesses(WitnessMgr::INSTANCE().witnesses());
    for (eye = witnesses.begin(); eye != witnesses.end(); ++ eye) {
        os
            << (*eye) -> id()
            << "\t\t"
            << (*eye) -> desc()
            << "\t\t"
            << (*eye) -> length()
            << std::endl;
    }
    os << std::endl;

    return Variant("Ok");
}

WitnessListCommand::~WitnessListCommand()
{}

WitnessDumpCommand::WitnessDumpCommand(Interpreter& owner, Expr_ptr wid)
    : Command(owner)
    , f_wid(wid)
{}

Variant WitnessDumpCommand::operator()()
{
    std::ostream &os(std::cout);

    Witness& w = WitnessMgr::INSTANCE().witness( f_wid->atom() );
    for (step_t time = w.first_time(); time <= w.last_time(); ++ time) {
        os << "-- @ " << 1 + time << std::endl;
        TimeFrame& tf = w[ time ];

        SymbIter symbs( ModelMgr::INSTANCE().model(), NULL );
        while (symbs.has_next()) {

            Symbol_ptr symb (symbs.next());
            Expr_ptr value (NULL);

            if (symb->is_variable())  {
                Expr_ptr expr (symb->expr());

                try {
                    value = tf.value(expr);
                }
                catch (NoValue nv) {
                    value = ExprMgr::INSTANCE().make_undef();
                }
                os << expr << " = " << value << std::endl;
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
                os << expr << " = " << value << std::endl;
            }
            else
                continue;
        }

        os << std::endl;
    }

    return Variant("Ok");
}

WitnessDumpCommand::~WitnessDumpCommand()
{}

