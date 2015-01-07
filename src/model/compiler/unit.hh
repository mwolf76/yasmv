/**
 *  @file unit.hh
 *  @brief Basic expressions compiler - Output type definition
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

#ifndef UNIT_H
#define UNIT_H

#include <micro/micro.hh>

class CompilationUnit {
public:
    CompilationUnit( DDVector& dds,
                     MicroDescriptors& micro_descriptors,
                     MuxDescriptors& mux_descriptors)
        : f_dds( dds )
        , f_micro_descriptors( micro_descriptors )
        , f_mux_descriptors( mux_descriptors )
    {}

    const DDVector& dds() const
    { return f_dds; }

    const MicroDescriptors& micro_descriptors() const
    { return f_micro_descriptors; }

    const MuxDescriptors& mux_descriptors() const
    { return f_mux_descriptors; }

private:
    DDVector f_dds;
    MicroDescriptors f_micro_descriptors;
    MuxDescriptors f_mux_descriptors;
};
typedef vector<CompilationUnit> CompilationUnits;
#endif
