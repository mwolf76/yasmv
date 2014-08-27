/**
 *  @file micro.hh
 *  @brief Microcode library
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
#ifndef MICRO_H
#define MICRO_H

#include <common.hh>
#include <pool.hh>

// for the definition of Term
#include <dd.hh>

typedef ADD Term;
typedef vector<Term> Terms;

class MicroDescriptor {

public:
    MicroDescriptor( ExprType op, Terms& z, Terms &x, Terms &y)
        : f_op(op)
        , f_z(z)
        , f_x(x)
        , f_y(y)
    {
        assert (f_z.size() == f_x.size() &&
                f_z.size() == f_y.size());
    }

private:
    ExprType f_op;
    Terms f_z;
    Terms f_x;
    Terms f_y;
};

typedef vector<MicroDescriptor> MicroDescriptors;
#endif
