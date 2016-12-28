/**
 * @file symb/iter.hh
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

#ifndef SYMBOL_ITER_H
#define SYMBOL_ITER_H

#include <common/common.hh>
#include <expr/expr.hh>
#include <utils/pool.hh>

#include <symb/typedefs.hh>

class Model;
class Symbol;

class SymbIter {
public:
    SymbIter(Model& model);
    ~SymbIter();

    /* true iff there are more symbols to be processed */
    bool has_next() const;

    /* yields next symbol, raises an exception if no such symbol exists. */
    std::pair <Expr_ptr, Symbol_ptr> next();

private:
    Model&  f_model;

    SymbIterable f_symbols;
    SymbIterable::const_iterator f_iter;
};

#endif /* SYMBOL_ITER_H */
