/*
 * @file check_ltl.cc
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
#include <cmd/commands/check_ltl.hh>

CheckLTL::CheckLTL(Interpreter& owner, Expr_ptr phi)
    : Command(owner)
    , f_phi(phi)
    , f_ltl(*this, ModelMgr::INSTANCE().model())
{}

Variant CheckLTL::operator()()
{ return run(); }

Variant CheckLTL::run()
{
    std::ostringstream tmp;
    f_ltl.process( f_phi );

    switch (f_ltl.status()) {
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
    if (f_ltl.has_witness()) {
        tmp
            << ", registered CEX witness `"
            << f_ltl.witness().id()
            << "`";
    }

    return Variant(tmp.str());
}

CheckLTL::~CheckLTL()
{}

