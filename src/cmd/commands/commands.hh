/*
 * @file command.hh
 * @brief Command-interpreter subsystem related classes and definitions.
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

#ifndef COMMANDS_H
#define COMMANDS_H

#include <common/common.hh>
#include <utils/variant.hh>

namespace cmd {

extern const std::string outPrefix;
extern const std::string wrnPrefix;

extern const std::string okMessage;
extern const std::string errMessage;
extern const std::string byeMessage;

inline bool is_success(utils::Variant& v)
{ return v.is_string() && v.as_string() == okMessage; }

inline bool is_failure(utils::Variant& v)
{ return v.is_string() && v.as_string() == errMessage; }

};

#endif /* COMMANDS_H */
