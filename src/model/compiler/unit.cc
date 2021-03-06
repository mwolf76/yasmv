/**
 * @file unit.cc
 * @brief Expression compiler subsystem, output unit classes implementation.
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

#include <model/compiler/unit.hh>
#include <type/type.hh>

InlinedOperatorDescriptor::InlinedOperatorDescriptor(InlinedOperatorSignature ios,
                                                     DDVector& z, DDVector &x)
    : f_ios(ios)
    , f_z(z)
    , f_x(x)
{}

InlinedOperatorDescriptor::InlinedOperatorDescriptor(InlinedOperatorSignature ios,
                                                     DDVector& z, DDVector &x, DDVector &y)
    : f_ios(ios)
    , f_z(z)
    , f_x(x)
    , f_y(y)
{}

BinarySelectionDescriptor::BinarySelectionDescriptor(unsigned width, DDVector& z,
                                                     ADD cnd, ADD aux, DDVector &x, DDVector &y)
    : f_width(width)
    , f_z(z)
    , f_cnd(cnd)
    , f_aux(aux)
    , f_x(x)
    , f_y(y)
{}

MultiwaySelectionDescriptor::MultiwaySelectionDescriptor(unsigned elem_width,
                                                         unsigned elem_count,
                                                         DDVector& z, DDVector& cnds,
                                                         DDVector& acts, DDVector &x)
    : f_elem_width(elem_width)
    , f_elem_count(elem_count)
    , f_z(z)
    , f_cnds(cnds)
    , f_acts(acts)
    , f_x(x)
{}

std::ostream& operator<<(std::ostream& os, InlinedOperatorSignature ios)
{
    bool is_signed
        (ios_issigned(ios));
    ExprType optype
        (ios_optype(ios));
    unsigned width
        (ios_width(ios));

    os <<
        (is_signed ? "s" : "u");

    switch (optype) {
    case NEG: os << "neg"; break;
    case NOT: os << "not"; break;

    case PLUS: os << "add"; break; // see expr/expr.hh
    case SUB:  os << "sub"; break;
    case MUL:  os << "mul"; break;
    case DIV:  os << "div"; break;
    case MOD:  os << "mod"; break;

    case BW_NOT: os << "not"; break;
    case BW_AND: os << "and"; break;
    case BW_OR:  os << "or";  break;

    case BW_XOR: os << "xor"; break;
    case BW_XNOR: os << "xnor"; break;
    case IMPLIES: os << "implies"; break;

    case LSHIFT: os << "lsh"; break;
    case RSHIFT: os << "rsh"; break;

    case EQ: os << "eq"; break;
    case NE: os << "ne"; break;
    case LT: os << "lt"; break;
    case LE: os << "le"; break;
    case GT: os << "gt"; break;
    case GE: os << "ge"; break;

    default: assert(false);
    } /* switch() */

    os << width;

    return os;
}

std::string ios2string(InlinedOperatorSignature ios)
{
    std::ostringstream oss;
    oss
        << ios;

    return oss.str();
}

std::ostream& operator<<(std::ostream& os, InlinedOperatorDescriptor& md)
{
    os
        << md.ios()
        << "(z = [";

    const DDVector& z
        (md.z());
    for (DDVector::const_iterator zi = z.begin();;) {
        const DdNode* node
            (zi->getNode());

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

    const DDVector& x
        (md.x());
    for (DDVector::const_iterator xi = x.begin();;) {
        const DdNode* node
            (xi->getNode());

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

    const DDVector& y
        (md.y());
    if (y.size()) {
        os << ", y = [";
        for (DDVector::const_iterator yi = y.begin();;) {
            const DdNode* node
                (yi->getNode());

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

std::string ios2string(InlinedOperatorDescriptor& iod)
{
    std::ostringstream oss;
    oss
        << iod;

    return oss.str();
}

std::ostream& operator<<(std::ostream& os, BinarySelectionDescriptor& md)
{
    os << "ITE mux"
       << md.width()
       << "(z = [";

    const DDVector& z
        (md.z());
    for (DDVector::const_iterator zi = z.begin();;) {
        const DdNode* node
            (zi->getNode());

        if (! Cudd_IsConstant(node))
            os << node->index;
        else
            os << ((Cudd_V(node) == 0) ? 'F' : 'T');

        if (++ zi != z.end())
            os << ", ";
        else
            break;
    }

    os << "], (aux = "; {
        const ADD aux
            (md.aux());
        const DdNode* node
            (aux.getNode());

        assert(! Cudd_IsConstant(node));

        os
            << node->index
            << "), x = [";
    }

    const DDVector& x
        (md.x());
    for (DDVector::const_iterator xi = x.begin();;) {
        const DdNode* node
            (xi->getNode());

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

    const DDVector& y
        (md.y());
    for (DDVector::const_iterator yi = y.begin();;) {
        const DdNode* node
            (yi->getNode());

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

std::string bsd2string(BinarySelectionDescriptor& bsd)
{
    std::ostringstream oss;

    oss
        << bsd;

    return oss.str();
}

std::string msd2string(MultiwaySelectionDescriptor& msd)
{
    std::ostringstream oss;

    oss
        << msd;

    return oss.str();
}

std::ostream& operator<<(std::ostream& os, MultiwaySelectionDescriptor& md)
{
    os << "Array mux"
       << md.elem_count()
       << " x "
       << md.elem_width()
       << "(z = [";

    const DDVector& z
        (md.z());
    for (DDVector::const_iterator zi = z.begin();;) {
        const DdNode* node
            (zi->getNode());

        if (! Cudd_IsConstant(node))
            os << node->index;
        else
            os << ((Cudd_V(node) == 0) ? 'F' : 'T');

        if (++ zi != z.end())
            os << ", ";
        else
            break;
    }

    const DDVector& acts(md.acts());
    if (acts.size()) {
        os << ", acts = [";
        for (DDVector::const_iterator actsi = acts.begin();;) {
            const DdNode* node
                (actsi->getNode());

            if (! Cudd_IsConstant(node))
                os << node->index;
            else
                os << ((Cudd_V(node) == 0) ? 'F' : 'T');
            if (++ actsi != acts.end())
                os << ", ";
            else
                break;
        }
        os << "]";
    }

    os << "], x = [";
    const DDVector& x(md.x());
    for (DDVector::const_iterator xi = x.begin();;) {
        const DdNode* node
            (xi->getNode());

        if (! Cudd_IsConstant(node))
            os << node->index;
        else
            os << ((Cudd_V(node) == 0) ? 'F' : 'T');

        if (++ xi != x.end())
            os << ", ";
        else
            break;
    }
    os << "])";

    return os;
}
