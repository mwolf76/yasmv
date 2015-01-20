/*
 * @file check_fsm.cc
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
#include <cmd/commands/check_fsm.hh>

CheckFSM::CheckFSM(Interpreter& owner)
    : Command(owner)
    , f_fsm(*this, ModelMgr::INSTANCE().model())
{}

Variant CheckFSM::operator()()
{ return run(); }

Variant CheckFSM::run()
{
    assert (false); // FIX: not yet implemented

    std::ostringstream tmp;
    f_fsm.process();

    switch (f_fsm.status()) {
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
    if (f_fsm.has_witness()) {
        tmp
            << ", registered CEX witness `"
            << f_fsm.witness().id()
            << "`";
    }

    return Variant(tmp.str());
}

CheckFSM::~CheckFSM()
{}

