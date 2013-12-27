/**
 *  @file Base Algorithm.cc
 *  @brief Base Algorithm
 *
 *  This module contains definitions and services that implement an
 *  abstract algorithm.
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
#include <base.hh>

Algorithm::Algorithm(ostream &os)
    : f_os(os)
    , f_mm(ModelMgr::INSTANCE())
    , f_em(ExprMgr::INSTANCE())
    , f_tm(TypeMgr::INSTANCE())
    , f_engine(* new SAT())
{
    set_param("alg_name", "test");
    DEBUG  << "Creating Base algoritm instance "
           << get_param("alg_name")
           << " @" << this
           << endl;
}

Algorithm::~Algorithm()
{
    DEBUG << "Destroying Base algoritm instance "
          << get_param("alg_name")
          << " @" << this
          << endl;

    delete & f_engine;
}

void Algorithm::set_param(string key, Variant value)
{ f_params [ key ] = value; }

Variant& Algorithm::get_param(const string key)
{
    const ParametersMap::iterator eye = f_params.find(key);

    if (eye != f_params.end()) {
        return (*eye).second;
    }

    else return NilValue;
}
