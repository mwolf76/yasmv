/**
 *  @file converter.cc
 *  @brief Custom Decision Diagram Manager class
 *
 *  This internal module contains definitions and services that
 *  implement a lightweight decision diagram class or YDD. YDDs are used
 *  to store compilation result in a time-independent fashion, in
 *  order to make it easy to instantiate timed expressions and convert
 *  them to CNF.
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
#include <compiler.hh>

Converter::Converter(Compiler& owner)
    : f_owner(owner)
{}

Converter::~Converter()
{}

bool Converter::condition(const DdNode *node)
{
    YDDMap::iterator eye;

    /* do visit on cache miss */
    if (f_cache.end() ==
        (eye = f_cache.find(const_cast<DdNode *>(node)))) {
        return true;
    }

    /* ... otherwise fix output stack and continue traversal */
    f_out_stack.push_back( (*eye).second );
    return false;
}

void Converter::action(const DdNode *node)
{
    YDD_ptr ldd = NULL, rhs, lhs;

    /* base: leaves */
    if (Cudd_IsConstant(node)) {
        value_t v = cuddV(node);
        assert (0 == v || 1 == v); /* 0-1 ADDs */

        ldd = make_ldd((bool) v);
        goto leave;
    }

    /* step: binary tree recursion */
    assert (2 <= f_out_stack.size());
    rhs = f_out_stack.back(); f_out_stack.pop_back();
    lhs = f_out_stack.back(); f_out_stack.pop_back();

    ldd = make_ldd(node->index, lhs, rhs);

 leave:
    assert( NULL != ldd );

    /* cache and return result */
    f_cache.insert( make_pair<DdNode *, YDD_ptr>
                    (const_cast<DdNode *>(node), ldd));

    f_out_stack.push_back(ldd);
}

YDD_ptr Converter::process(ADD input)
{
    f_out_stack.clear();

    (*this)(input);

    assert( 1 == f_out_stack.size());
    return f_out_stack.back();
}
