/**
 * @file symb/typedefs.hh
 * @brief Symbol interface, typedefs
 *
 * This header file contains the declarations required by the symbol
 * resolver.
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
#ifndef SYMBOL_TYPEDEFS_H
#define SYMBOL_TYPEDEFS_H

#include <expr/expr.hh>

#include <utils/pool.hh>

#include <boost/unordered_map.hpp>
#include <vector>

namespace symb {

    typedef class Symbol* Symbol_ptr;
    typedef boost::unordered_map<expr::Expr_ptr, Symbol_ptr,
                                 utils::PtrHash, utils::PtrEq>
        Symbols;

    typedef class Literal* Literal_ptr;
    typedef boost::unordered_map<expr::Expr_ptr, Literal_ptr,
                                 utils::PtrHash, utils::PtrEq>
        Literals;

    typedef class Constant* Constant_ptr;
    typedef boost::unordered_map<expr::Expr_ptr, Constant_ptr,
                                 utils::PtrHash, utils::PtrEq>
        Constants;

    typedef class Variable* Variable_ptr;
    typedef boost::unordered_map<expr::Expr_ptr, Variable_ptr,
                                 utils::PtrHash, utils::PtrEq>
        Variables;

    typedef class Parameter* Parameter_ptr;
    typedef std::vector<std::pair<expr::Expr_ptr, Parameter_ptr>> Parameters;

    typedef class Define* Define_ptr;
    typedef boost::unordered_map<expr::Expr_ptr, Define_ptr,
                                 utils::PtrHash, utils::PtrEq>
        Defines;

    typedef class Resolver* Resolver_ptr;

    typedef std::vector<std::pair<expr::Expr_ptr, Symbol_ptr>> SymbIterable;

}; // namespace symb

#endif /* SYMBOL_TYPEDEFS_H */
