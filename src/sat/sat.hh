/**
 * @file sat.hh
 * @brief SAT module, toplevel header file.
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

#ifndef SAT_H
#define SAT_H

#include <sat/typedefs.hh>
#include <sat/exceptions.hh>

/* CNF registry class */
#include <sat/cnf_registry.hh>

/* time mapper class */
#include <sat/time_mapper.hh>

/* inlining helpers */
#include <sat/inlining.hh>

/* logging helpers */
#include <sat/logging.hh>

/* Engine class */
#include <sat/engine.hh>

/* Engine Mgr class */
#include <sat/engine_mgr.hh>

#endif /* SAT_H */
