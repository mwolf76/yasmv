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
#include <utility>
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

    /* Identity lookup with iteration in insertion order. Module symbols
       were kept in pointer-hashed maps and walked in bucket order, so
       encodings, SAT variable numbering, witnesses and dumps depended on
       heap addresses and changed from one process to the next under
       ASLR. Declaration order is what every walker wants anyway.
       insert() keeps the first binding of a key, like the map it
       replaces. */
    template <typename V>
    class OrderedPtrMap {
    public:
        typedef std::pair<expr::Expr_ptr, V> value_type;
        typedef typename std::vector<value_type>::iterator iterator;
        typedef typename std::vector<value_type>::const_iterator const_iterator;

        iterator begin() { return f_items.begin(); }
        iterator end() { return f_items.end(); }
        const_iterator begin() const { return f_items.begin(); }
        const_iterator end() const { return f_items.end(); }
        size_t size() const { return f_items.size(); }
        bool empty() const { return f_items.empty(); }
        void clear() { f_items.clear(); f_index.clear(); }

        iterator find(expr::Expr_ptr key)
        {
            const auto i { f_index.find(key) };
            return f_index.end() == i ? f_items.end() : f_items.begin() + i->second;
        }
        const_iterator find(expr::Expr_ptr key) const
        {
            const auto i { f_index.find(key) };
            return f_index.end() == i ? f_items.end() : f_items.begin() + i->second;
        }

        std::pair<iterator, bool> insert(const value_type& item)
        {
            const auto i { f_index.find(item.first) };
            if (f_index.end() != i) {
                return std::make_pair(f_items.begin() + i->second, false);
            }
            f_index.emplace(item.first, f_items.size());
            f_items.push_back(item);
            return std::make_pair(f_items.end() - 1, true);
        }

    private:
        std::vector<value_type> f_items;
        boost::unordered_map<expr::Expr_ptr, size_t, utils::PtrHash, utils::PtrEq> f_index;
    };

    typedef OrderedPtrMap<Variable_ptr> Variables;

    typedef class Parameter* Parameter_ptr;
    typedef std::vector<std::pair<expr::Expr_ptr, Parameter_ptr>> Parameters;

    typedef class Define* Define_ptr;
    typedef OrderedPtrMap<Define_ptr> Defines;

    typedef class Resolver* Resolver_ptr;

    typedef std::vector<std::pair<expr::Expr_ptr, Symbol_ptr>> SymbIterable;

}; // namespace symb

#endif /* SYMBOL_TYPEDEFS_H */
