/*
Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

 */

/**
 * @file common.hh
 *
 * @brief System wide definitions
 *
 */

#ifndef COMMON_H
#define COMMON_H
#include <config.h>

#include <cassert>
#include <utility>
#include <string>
#include <sstream>
#include <iostream>
#include <vector>
#include <set>

#include <tr1/unordered_set>
#include <tr1/unordered_map>

using std::pair;
using std::make_pair;

using std::string;
using std::ostringstream;
using std::ostream;
using std::vector;
using std::set;
using std::tr1::unordered_map;
using std::tr1::unordered_set;

using std::cout;
using std::cerr;
using std::endl;

class IVariable;
typedef vector<IVariable*> Variables;

class IDefine;
typedef vector<IDefine*> Defines;

class IAssign;
typedef vector<IAssign*> Assigns;

class IModule;
typedef vector<IModule*> Modules;

// logging support using ezlogger (cfr. http://axter.com/ezlogger/)
#include <logging.hh>

#endif