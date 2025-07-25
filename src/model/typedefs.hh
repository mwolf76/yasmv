/**
 * @file model/typedefs.hh
 * @brief Model module, typedefs.
 *
 * This header file contains the declarations required by the Model
 * class and its dependencies.
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

#ifndef MODEL_TYPEDEFS_H
#define MODEL_TYPEDEFS_H

#include <common/common.hh>

#include <boost/unordered_map.hpp>
#include <utils/pool.hh>

namespace model {

    using Model_ptr = class Model*;
    using Module_ptr = class Module*;


    using Modules = boost::unordered_map<expr::Expr_ptr, Module_ptr,
					 utils::PtrHash, utils::PtrEq>;

    using SymbolIndexMap = boost::unordered_map<expr::Expr_ptr, unsigned,
						utils::PtrHash, utils::PtrEq>;

    /* streaming helper */
    std::ostream& operator<<(std::ostream& os, Module& module);

}; // namespace model

#endif /* MODEL_TYPEDEFS_H */
