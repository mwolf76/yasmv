/*
 * @file check_invar.cc
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
#include <cmd/commands/check_invar.hh>

CheckInvar::CheckInvar(Interpreter& owner, Expr_ptr phi)
    : Command(owner)
    , f_phi(phi)
    , f_bmc(*this, ModelMgr::INSTANCE().model())
{}

Variant CheckInvar::operator()()
{ return run(); }

Variant CheckInvar::run()
{
    std::ostringstream tmp;
    f_bmc.process( f_phi );

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

CheckInvar::~CheckInvar()
{}
