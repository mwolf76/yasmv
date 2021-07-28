/**
 * @file witness_mgr.cc
 * @brief Witness Manager class implementation.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#include <utility>
#include <witness_mgr.hh>

namespace witness {

// static initialization
WitnessMgr_ptr WitnessMgr::f_instance = NULL;

WitnessMgr::WitnessMgr()
    : f_em(expr::ExprMgr::INSTANCE())
    , f_tm(type::TypeMgr::INSTANCE())
    , f_evaluator(*this)
    , f_autoincrement(0)
{}

Witness& WitnessMgr::current()
{
    if (! f_curr_uid.size())
        return f_empty_witness;

    return witness(f_curr_uid);
}

void WitnessMgr::set_current( Witness& witness )
{
    expr::Atom uid
        (witness.id());

    WitnessMap::iterator eye
        (f_map.find( uid ));

    if (f_map.end() == eye)
        throw UnknownWitnessId( uid );

    f_curr_uid = uid;
}

Witness& WitnessMgr::witness( expr::Atom id )
{
    WitnessMap::iterator eye
        (f_map.find( id ));

    if (f_map.end() == eye)
        throw UnknownWitnessId( id );

    Witness_ptr wp
        ((*eye).second);

    return *wp;
}

void WitnessMgr::record( Witness& witness )
{
    expr::Atom uid
        (witness.id());

    WitnessMap::iterator eye
        (f_map.find( uid ));

    if (f_map.end() != eye)
        throw DuplicateWitnessId( uid );

    f_map.insert( std::pair <expr::Atom, Witness_ptr>
                  (uid, &witness));

    f_list.push_back( &witness );
}

unsigned WitnessMgr::autoincrement()
{
    return ++ f_autoincrement;
}

expr::Expr_ptr WitnessMgr::eval(Witness &w, expr::Expr_ptr ctx, expr::Expr_ptr body, step_t k)
{
    expr::Expr_ptr res;

    try {
        res = f_evaluator.process(w, ctx, body, k);
    }
    catch (NoValue& nv) {
        res = NULL;
    }

    return res;
}

};
