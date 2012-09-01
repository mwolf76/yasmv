// -*- C++ -*-
// solverlogger.cc: Output operators for various solver types (Lit, Clause, ...)
// Author: Alberto Griggio

#include "utils/solverlogger.hh"

namespace Minisat {

  ostream &operator<<(ostream &out, const Lit &lit)
  {
    out << (sign(lit) ? "~" : "") << var(lit);

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
    out << "{";

    for (int i = 0; i < lits.size()-1; ++i) {
      out << lits[i] << " ; ";
    }

    if (lits.size()) out << lits[lits.size()-1];
    out << "}";

    return out;
  }

}
