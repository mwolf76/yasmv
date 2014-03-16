/**
 *  @file logger.cc
 *  @brief SAT types logging
 *
 *  This module contains the interface for services that implement an
 *  CNF clauses generation in a form that is suitable for direct
 *  injection into the SAT solver.
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
#include <sat.hh>

namespace Minisat {

    ostream &operator<<(ostream &out, const Lit &lit)
    {
        if (!var(lit)) return out;
        out << (sign(lit) ? "-" : "") << var(lit);
        return out;
    }

    ostream &operator<<(ostream &out, const Clause *clause)
    {
        out << (clause->learnt() ? "L" : "") << "(";
        for (int i = 0; i < clause->size()-1; ++i) {
            out << (*clause)[i] << " | ";
        }
        out << (*clause)[clause->size()-1] << ")";

        return out;
    }

    ostream &operator<<(ostream &out, const Clause &clause)
    {
        out << (&clause);

        return out;
    }

    ostream &operator<<(ostream &out, const vec<Lit> &lits)
    {
        for (int i = 0; i < lits.size()-1; ++i) {
            out << lits[i] << " ";
        }

        if (0 != lits.size()) {
            out << lits[lits.size()-1];
        }

        return out;
    }

    ostream &operator<<(ostream &os, const lbool &lb)
    {
        switch(lb.value) {
        case 0:
            os << "T";
            break;
        case 1:
            os << "F";
            break;
        case 2:
            os << "X";
            break;
        default:
            assert(0);
        }

        return os;
    }

    ostream &operator<<(ostream &os, const status_t &status)
    {
        switch (status) {
        case STATUS_SAT:
            os << "SAT";
            break;
        case STATUS_UNSAT:
            os << "UNSAT";
            break;
        case STATUS_UNKNOWN:
            os << "??";
            break;
        default:
            assert(0);
        }

        return os;
    }

};
