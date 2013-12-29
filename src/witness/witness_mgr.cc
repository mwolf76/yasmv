/**
 *  @file witness_mgr.cc
 *  @brief Witness module (WitnessMgr class)
 *
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2.1 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/

#include <witness_mgr.hh>

// static initialization
WitnessMgr_ptr WitnessMgr::f_instance = NULL;

WitnessMgr::WitnessMgr()
    : f_em(ExprMgr::INSTANCE())
    , f_tm(TypeMgr::INSTANCE())
    , f_evaluator(*this)
{}

Witness& WitnessMgr::witness( Atom id )
{
    WitnessMap::iterator eye = f_map.find( id );
    if (f_map.end() == eye) {
        throw UnknownWitnessId( id );
    }

    Witness_ptr wp = (*eye).second;
    return *wp;
}

void WitnessMgr::register_witness( Witness& w )
{
    Atom id (w.id());
    WitnessMap::iterator eye = f_map.find( id );
    if (f_map.end() != eye) {
        throw DuplicateWitnessId( id );
    }

    f_map.insert( make_pair <Atom, Witness_ptr> (id, &w));
}

const char* DuplicateWitnessId::what() const throw()
{
    ostringstream oss;
    oss << "Duplicate witness ID:  "
        << f_id << " is already registered."
        << endl
        ;

    return oss.str().c_str();
}

const char* UnknownWitnessId::what() const throw()
{
    ostringstream oss;
    oss << "Unknown witness ID:  "
        << f_id << " is not registered."
        << endl
        ;

    return oss.str().c_str();
}
