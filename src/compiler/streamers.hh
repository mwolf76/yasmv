/**
 * @file streamers.hh
 * @brief Basic expressions compiler - Output type definition
 *
 * This header file contains the declarations required by the
 * compilation types streamers.
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

#ifndef COMPILATION_STREAMERS_H
#define COMPILATION_STREAMERS_H

#include <vector>

#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_comparison.hpp>

std::ostream& operator<<(std::ostream& os, const compiler::CompilationUnit& cu);

std::ostream& operator<<(std::ostream& os, const compiler::InlinedOperatorSignature& ios);
std::string ios2string(const compiler::InlinedOperatorSignature ios);

std::ostream& operator<<(std::ostream& os, const compiler::InlinedOperatorDescriptor& iod);
std::string iod2string(const compiler::InlinedOperatorDescriptor& ios);

std::ostream& operator<<(std::ostream& os, const compiler::BinarySelectionDescriptor& md);
std::string bsd2string(const compiler::InlinedOperatorSignature& ios);

std::ostream& operator<<(std::ostream& os, const compiler::MultiwaySelectionDescriptor& md);
std::string msd2string(const compiler::InlinedOperatorSignature& ios);

#endif /* COMPILATION_STREAMERS_H */
