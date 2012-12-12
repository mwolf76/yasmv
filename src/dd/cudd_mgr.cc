/**
 *  @file cudd_mgr.cc
 *  @brief Cudd module (CuddMgr class)
 *
 *  This module contains definitions and services that implement an
 *  cudd for symbols. For each symbol a boolean encoding is
 *  maintained, the cudd takes care of ADD variables definitions
 *  and is provides mapback services as well.
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
#include <cudd_mgr.hh>

CuddMgr_ptr CuddMgr::f_instance = NULL;

CuddMgr::CuddMgr()
{
    DRIVEL << "Initialized CuddMgr @ " << this << endl;
}

CuddMgr::~CuddMgr()
{
    CuddVector::iterator i;
    for (i = f_cudd_instances.begin(); i != f_cudd_instances.end(); ++ i)
        delete *i;

    DRIVEL << "Deinitialized EncodingMgr @ " << this << endl;
}

Cudd& CuddMgr::dd()
{
    Cudd* res = new Cudd();
    assert (NULL != res);

    /* Common setup for all dd instances */
    res -> AutodynEnable(CUDD_REORDER_SAME);

    f_cudd_instances.push_back(res);

    return *res;
}
