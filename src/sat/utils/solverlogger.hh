// -*- C++ -*-
// solverlogger.h: Output operators for various solver types (Lit, Clause, ...)
// Author: Alberto Griggio
// $Id: solverlogger.h,v 1.1 2007-06-06 09:03:55 nusmv Exp $

#ifndef SOLVERLOGGER_H_INCLUDED
#define SOLVERLOGGER_H_INCLUDED

#include <ostream>
#include "Vec.hh"
#include "SolverTypes.hh"

namespace Minisat {

  using std::ostream;

  ostream &operator<<(ostream &out, const Lit &lit);
  ostream &operator<<(ostream &out, const Clause *clause);
  ostream &operator<<(ostream &out, const Clause &clause);
  ostream &operator<<(ostream &out, const vec<Lit> &lits);

} // namespace msat

#endif // SOLVERLOGGER_H_INCLUDED
