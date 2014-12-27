/**
 *  @file micro.cc
 *  @brief Micro module
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
#include <type.hh>
#include <micro.hh>

MicroDescriptor::MicroDescriptor(OpTriple triple, DDVector& z, DDVector &x, DDVector &y)
    : f_triple(triple)
    , f_z(z)
    , f_x(x)
    , f_y(y)
{}

ostream& operator<<(ostream& os, MicroDescriptor& md)
{
    os << md.triple();
    os << "([";
    const DDVector& z(md.z());
    for (DDVector::const_iterator zi = z.begin();;) {
        const DdNode* node (zi->getNode());
        if (! Cudd_IsConstant(node)) {
            os << node->index;
        }
        else {
            os << "-";
        }
        if (++ zi != z.end()) {
            os << ", ";
        } else break;
    }
    os << "], [";
    const DDVector& x(md.x());
    for (DDVector::const_iterator xi = x.begin();;) {
        const DdNode* node (xi->getNode());
        if (! Cudd_IsConstant(node)) {
            os << node->index;
        }
        else {
            os << "-";
        }
        if (++ xi != x.end()) {
            os << ", ";
        } else break;
    }
    os << "], [";
    const DDVector& y(md.y());
    for (DDVector::const_iterator yi = y.begin();;) {
        const DdNode* node (yi->getNode());
        if (! Cudd_IsConstant(node)) {
            os << node->index;
        }
        else {
            os << "-";
        }
        if (++ yi != y.end()) {
            os << ", ";
        } else break;
    }
    os << "])";

    return os;
}