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

MicroDescriptor::MicroDescriptor(OpTriple triple, DDVector& z, DDVector &x)
    : f_triple(triple)
    , f_z(z)
    , f_x(x)
{}

MicroDescriptor::MicroDescriptor(OpTriple triple, DDVector& z, DDVector &x, DDVector &y)
    : f_triple(triple)
    , f_z(z)
    , f_x(x)
    , f_y(y)
{}

MuxDescriptor::MuxDescriptor(unsigned width, DDVector& z, ADD cnd, DDVector &x, DDVector &y)
    : f_width(width)
    , f_z(z)
    , f_cnd(cnd)
    , f_x(x)
    , f_y(y)
{
}

ostream& operator<<(ostream& os, MicroDescriptor& md)
{
    os
        << md.triple()
        << "(z = [";

    const DDVector& z(md.z());
    for (DDVector::const_iterator zi = z.begin();;) {
        const DdNode* node (zi->getNode());

        if (! Cudd_IsConstant(node))
            os << node->index;
        else
            os << ((Cudd_V(node) == 0) ? 'F' : 'T');

        if (++ zi != z.end())
            os << ", ";
        else
            break;
    }
    os << "], x = [";
    const DDVector& x(md.x());
    for (DDVector::const_iterator xi = x.begin();;) {
        const DdNode* node (xi->getNode());
        if (! Cudd_IsConstant(node))
            os << node->index;
        else
            os << ((Cudd_V(node) == 0) ? 'F' : 'T');

        if (++ xi != x.end())
            os << ", ";
        else
            break;
    }
    os << "]";

    const DDVector& y(md.y());
    if (y.size()) {
        os << ", y = [";
        for (DDVector::const_iterator yi = y.begin();;) {
            const DdNode* node (yi->getNode());
            if (! Cudd_IsConstant(node))
                os << node->index;
            else
                os << ((Cudd_V(node) == 0) ? 'F' : 'T');
            if (++ yi != y.end())
                os << ", ";
            else
                break;
        }
        os << "]";
    }
    os << ")";


    return os;
}

ostream& operator<<(ostream& os, MuxDescriptor& md)
{
    os << "mux"
       << md.width()
       << "(z = [";

    const DDVector& z(md.z());
    for (DDVector::const_iterator zi = z.begin();;) {
        const DdNode* node (zi->getNode());
        if (! Cudd_IsConstant(node))
            os << node->index;
        else
            os << ((Cudd_V(node) == 0) ? 'F' : 'T');

        if (++ zi != z.end())
            os << ", ";
        else
            break;
    }

    os << "], (cnd = ";
    const ADD cnd(md.cnd());
    const DdNode* node (cnd.getNode());

    if (! Cudd_IsConstant(node))
        os << node->index;
    else
        os << ((Cudd_V(node) == 0) ? 'F' : 'T');

    os << "), x = [";
    const DDVector& x(md.x());
    for (DDVector::const_iterator xi = x.begin();;) {
        const DdNode* node (xi->getNode());
        if (! Cudd_IsConstant(node))
            os << node->index;
        else
            os << ((Cudd_V(node) == 0) ? 'F' : 'T');

        if (++ xi != x.end())
            os << ", ";
        else
            break;
    }
    os << "], y = [";
    const DDVector& y(md.y());
    for (DDVector::const_iterator yi = y.begin();;) {
        const DdNode* node (yi->getNode());
        if (! Cudd_IsConstant(node))
            os << node->index;
        else
            os << ((Cudd_V(node) == 0) ? 'F' : 'T');

        if (++ yi != y.end())
            os << ", ";
        else
            break;
    }
    os << "])";

    return os;
}

