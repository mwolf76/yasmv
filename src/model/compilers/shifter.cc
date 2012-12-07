/**
 *  @file shifter.cc
 *  @brief @Boolean compiler - time shifting component
 *
 *  This module implements the time shifter component of the
 *  compiler. The idea here is to perform a post-order visit of a
 *  given DD that has already been created as the result of compiling
 *  an expression at time 0 and create a new DD at time k, without the
 *  computational load of the compilation process.
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
#include <pool.hh>
#include <compiler.hh>

TimeShifter::TimeShifter(Compiler& owner)
    : DDNodeWalker(CuddMgr::INSTANCE())
    , f_owner(owner)
{ DEBUG << "Created TimeShifter @" << this << endl; }

TimeShifter::~TimeShifter()
{ DEBUG << "Destroying TimeShifter @" << this << endl; }

void TimeShifter::pre_hook()
{ assert( 1 == f_recursion_stack.size()); }

void TimeShifter::post_hook()
{ assert( 1 == 0 ); }

bool TimeShifter::condition(const DdNode *node)
{ return false; }

void TimeShifter::action(const DdNode *node)
{ assert (false); }
