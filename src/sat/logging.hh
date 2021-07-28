/**
 * @file sat/logging.hh
 * @brief SAT interface, logging helpers declarations.
 *
 * This module contains the interface for services that implement an
 * CNF clauses generation in a form that is suitable for direct
 * injection into the SAT solver.
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

#ifndef SAT_LOGGING_H
#define SAT_LOGGING_H

#include <sat/typedefs.hh>

namespace sat {

// streaming for various SAT related types
std::ostream &operator<<(std::ostream &os, const Minisat::Lit &lit);
std::ostream &operator<<(std::ostream &os, const vec<Lit> &lits);
std::ostream &operator<<(std::ostream &os, const status_t &status);
std::ostream &operator<<(std::ostream &os, const lbool &value);

std::ostream &operator<<(std::ostream &out, const Lit &lit);
std::ostream &operator<<(std::ostream &out, const vec<Lit> &lits);

};

#endif /* SAT_LOGGING_H */
