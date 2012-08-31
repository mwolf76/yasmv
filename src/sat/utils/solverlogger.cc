// -*- C++ -*-
// solverlog.cpp: Output operators for various solver types (Lit, Clause, ...)
// Author: Alberto Griggio
// $Id: solverlog.cpp,v 1.2 2007-07-27 11:34:01 nusmv Exp $

#include "utils/solverlogger.h"

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
