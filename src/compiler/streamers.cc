/**
 * @file streamers.cc
 * @brief Expression compiler subsystem, streaming helpers implementation.
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

#include <compiler/streamers.hh>
#include <compiler/typedefs.hh>

#include <type/type.hh>

std::ostream& operator<<(std::ostream& os, const compiler::Unit& cu)
{
    return os
           << cu.expr();
}

std::ostream& operator<<(std::ostream& os, const compiler::InlinedOperatorSignature& ios)
{
    bool is_signed(compiler::ios_issigned(ios));
    expr::ExprType optype(compiler::ios_optype(ios));
    unsigned width(compiler::ios_width(ios));

    os << (is_signed ? "s" : "u");

    switch (optype) {
        case expr::ExprType::NEG:
            os << "neg";
            break;
        case expr::ExprType::NOT:
            os << "not";
            break;

        case expr::ExprType::PLUS:
            os << "add";
            break; // see expr/expr.hh
        case expr::ExprType::SUB:
            os << "sub";
            break;
        case expr::ExprType::MUL:
            os << "mul";
            break;
        case expr::ExprType::DIV:
            os << "div";
            break;
        case expr::ExprType::MOD:
            os << "mod";
            break;

        case expr::ExprType::BW_NOT:
            os << "not";
            break;
        case expr::ExprType::BW_AND:
            os << "and";
            break;
        case expr::ExprType::BW_OR:
            os << "or";
            break;

        case expr::ExprType::BW_XOR:
            os << "xor";
            break;
        case expr::ExprType::BW_XNOR:
            os << "xnor";
            break;
        case expr::ExprType::IMPLIES:
            os << "implies";
            break;

        case expr::ExprType::LSHIFT:
            os << "lsh";
            break;
        case expr::ExprType::RSHIFT:
            os << "rsh";
            break;

        case expr::ExprType::EQ:
            os << "eq";
            break;
        case expr::ExprType::NE:
            os << "ne";
            break;
        case expr::ExprType::LT:
            os << "lt";
            break;
        case expr::ExprType::LE:
            os << "le";
            break;
        case expr::ExprType::GT:
            os << "gt";
            break;
        case expr::ExprType::GE:
            os << "ge";
            break;

        default:
            assert(false);
    } /* switch() */

    os << width;

    return os;
}

std::string ios2string(const compiler::InlinedOperatorSignature& ios)
{
    std::ostringstream oss;
    oss
        << ios;

    return oss.str();
}

std::ostream& operator<<(std::ostream& os,
                         const compiler::InlinedOperatorDescriptor& md)
{
    auto ios { md.ios() };

    os
        << ios
        << "(z = [";

    const dd::DDVector& z { md.z() };
    for (dd::DDVector::const_iterator zi = z.begin();;) {
        const DdNode* node { zi->getNode() };

        if (!Cudd_IsConstant(node)) {
            os << node->index;
        } else {
            os << ((Cudd_V(node) == 0) ? 'F' : 'T');
        }

        if (++zi != z.end()) {
            os << ", ";
        } else {
            break;
        }
    }

    os << "], x = [";

    const dd::DDVector& x { md.x() };
    for (dd::DDVector::const_iterator xi = x.begin();;) {
        const DdNode* node { xi->getNode() };

        if (!Cudd_IsConstant(node)) {
            os << node->index;
        } else {
            os << ((Cudd_V(node) == 0) ? 'F' : 'T');
        }

        if (++xi != x.end()) {
            os << ", ";
        } else {
            break;
        }
    }

    os << "]";

    const dd::DDVector& y { md.y() };
    if (y.size()) {
        os << ", y = [";
        for (dd::DDVector::const_iterator yi = y.begin();;) {
            const DdNode* node { yi->getNode() };

            if (!Cudd_IsConstant(node)) {
                os << node->index;
            } else {
                os << ((Cudd_V(node) == 0) ? 'F' : 'T');
            }

            if (++yi != y.end()) {
                os << ", ";
            } else {
                break;
            }
        }
        os << "]";
    }
    os << ")";

    return os;
}

std::string ios2string(const compiler::InlinedOperatorDescriptor& iod)
{
    std::ostringstream oss;
    oss
        << iod;

    return oss.str();
}

std::ostream& operator<<(std::ostream& os, const compiler::BinarySelectionDescriptor& md)
{
    os << "ITE mux"
       << md.width()
       << "(z = [";

    const dd::DDVector& z { md.z() };
    for (dd::DDVector::const_iterator zi = z.begin();;) {
        const DdNode* node { zi->getNode() };

        if (!Cudd_IsConstant(node)) {
            os << node->index;
        } else {
            os << ((Cudd_V(node) == 0) ? 'F' : 'T');
        }

        if (++zi != z.end()) {
            os << ", ";
        } else {
            break;
        }
    }

    os << "], (aux = ";
    {
        const ADD aux { md.aux() };
        const DdNode* node { aux.getNode() };

        assert(!Cudd_IsConstant(node));

        os
            << node->index
            << "), x = [";
    }

    const dd::DDVector& x { md.x() };
    for (dd::DDVector::const_iterator xi = x.begin();;) {
        const DdNode* node { xi->getNode() };

        if (!Cudd_IsConstant(node)) {
            os << node->index;
        } else {
            os << ((Cudd_V(node) == 0) ? 'F' : 'T');
        }

        if (++xi != x.end()) {
            os << ", ";
        } else {
            break;
        }
    }

    os << "], y = [";

    const dd::DDVector& y(md.y());
    for (dd::DDVector::const_iterator yi = y.begin();;) {
        const DdNode* node { yi->getNode() };

        if (!Cudd_IsConstant(node)) {
            os << node->index;
        } else {
            os << ((Cudd_V(node) == 0) ? 'F' : 'T');
        }

        if (++yi != y.end()) {
            os << ", ";
        } else {
            break;
        }
    }
    os << "])";

    return os;
}

std::string bsd2string(const compiler::BinarySelectionDescriptor& bsd)
{
    std::ostringstream oss;

    oss
        << bsd;

    return oss.str();
}

std::string msd2string(const compiler::MultiwaySelectionDescriptor& msd)
{
    std::ostringstream oss;

    oss
        << msd;

    return oss.str();
}

std::ostream& operator<<(std::ostream& os, const compiler::MultiwaySelectionDescriptor& md)
{
    os << "Array mux"
       << md.elem_count()
       << " x "
       << md.elem_width()
       << "(z = [";

    const dd::DDVector& z { md.z() };
    for (dd::DDVector::const_iterator zi = z.begin();;) {
        const DdNode* node { zi->getNode() };

        if (!Cudd_IsConstant(node)) {
            os << node->index;
        } else {
            os << ((Cudd_V(node) == 0) ? 'F' : 'T');
        }

        if (++zi != z.end()) {
            os << ", ";
        } else {
            break;
        }
    }

    const dd::DDVector& acts { md.acts() };
    if (acts.size()) {
        os << ", acts = [";
        for (dd::DDVector::const_iterator actsi = acts.begin();;) {
            const DdNode* node { actsi->getNode() };

            if (!Cudd_IsConstant(node)) {
                os << node->index;
            } else {
                os << ((Cudd_V(node) == 0) ? 'F' : 'T');
            }

            if (++actsi != acts.end()) {
                os << ", ";
            } else {
                break;
            }
        }
        os << "]";
    }

    os << "], x = [";
    const dd::DDVector& x { md.x() };
    for (dd::DDVector::const_iterator xi = x.begin();;) {
        const DdNode* node { xi->getNode() };

        if (!Cudd_IsConstant(node)) {
            os << node->index;
        } else {
            os << ((Cudd_V(node) == 0) ? 'F' : 'T');
        }

        if (++xi != x.end()) {
            os << ", ";
        } else {
            break;
        }
    }
    os << "])";

    return os;
}
