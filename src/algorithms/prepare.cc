/**
 *  @file prepare.cc
 *  @brief Prepare algorithm
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
#include <prepare.hh>

Prepare::Prepare(IModel& model)
    : Algorithm(model)
{}

Prepare::~Prepare()
{}

void Prepare::process()
{
    clock_t t0 = clock(), t1;
    double secs;

    TRACE << "Phase 1" << endl;
    prepare();

    TRACE << "Phase 2" << endl;
    compile();

    t1 = clock(); secs = (double) (t1 - t0) / (double) CLOCKS_PER_SEC;
    os () << "-- preparation completed, took " << secs
          << " seconds" << endl;

}
