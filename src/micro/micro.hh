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

#include <dd.hh>

// <symb, is_signed?, width>
typedef tuple<bool, ExprType, int> OpTriple;
inline const OpTriple make_op_triple (bool is_signed, ExprType exprType, int width) {
    return make_tuple <bool, ExprType, int> (is_signed, exprType, width);
}

struct OpTripleHash {
    long operator() (const OpTriple& k) const
    {
        const long prime = 31;

        long res = 1;
        res = prime * res + (k.get<0>() ? 1231 : 1237);
        res = prime * res + k.get<1>();
        res = prime * res + k.get<2>();
        return res;
    }
};

struct OpTripleEq {
    bool operator() (const OpTriple& x, const OpTriple& y) const
    {
        return
            x.get<0>() == y.get<0>() &&
            x.get<1>() == y.get<1>() &&
            x.get<2>() == y.get<2>()  ;
    }
};

class MicroDescriptor {

public:
    MicroDescriptor( OpTriple triple, DDVector& z, DDVector &x, DDVector &y)
        : f_triple(triple)
        , f_z(z)
        , f_x(x)
        , f_y(y)
    {
        assert (f_z.size() == f_x.size() && f_z.size() == f_y.size());
    }

private:
    OpTriple f_triple;

    DDVector f_z;
    DDVector f_x;
    DDVector f_y;
};

typedef vector<MicroDescriptor> MicroDescriptors;

// compiler output
class Term {
public:
    Term()
        : f_formula()
        , f_descriptors()
    {}

    Term(DDVector& formula, MicroDescriptors& descriptors)
        : f_formula(formula)
        , f_descriptors(descriptors)
    {}

    inline const DDVector& formula() const
    { return f_formula; }

    inline const MicroDescriptors& descriptors() const
    { return f_descriptors; }

private:
    DDVector f_formula;
    MicroDescriptors f_descriptors;
};

typedef vector<Term> Terms;

#endif
