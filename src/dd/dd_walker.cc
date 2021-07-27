/**
 * @file dd_walker.cc
 * @brief DD walker class implementation.
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

#include <common/common.hh>
#include <dd_walker.hh>

namespace dd {

/* --- ADD Walker ----------------------------------------------------------- */
ADDWalker::ADDWalker()
{}

ADDWalker::~ADDWalker()
{}

ADDWalker& ADDWalker::operator() (ADD dd)
{
    /* setup toplevel act. record and perform walk. */
    add_activation_record call
        (dd.getNode());
    f_recursion_stack.push(call);

    /* actions before the walk */
    pre_hook();

    walk();

    /* actions after the walk */
    post_hook();

    return *this;
}

/* post-order visit strategy */
void ADDWalker::walk ()
{
    while(0 != f_recursion_stack.size()) {
    loop:
        add_activation_record curr
            (f_recursion_stack.top());
        assert (!Cudd_IsComplement(curr.node));

        register const DdNode *node
            (curr.node);

        /* leaves have no children */
        if (cuddIsConstant(node))
            curr.pc = DD_WALK_NODE;

        // restore caller location (simulate call return behavior)
        switch(curr.pc) {
        case DD_WALK_LHS:
            /* recur in THEN */
            f_recursion_stack.top().pc = DD_WALK_RHS;
            f_recursion_stack.push( add_activation_record( cuddT(node)));
            goto loop;

        case DD_WALK_RHS:
            /* recur in ELSE */
            f_recursion_stack.top().pc = DD_WALK_NODE;
            f_recursion_stack.push( add_activation_record( cuddE(node)));
            goto loop;

        case DD_WALK_NODE:
            /* process node in post-order. */
            if (condition(node))
                action(node);
            f_recursion_stack.pop();
            break;

        default: assert( false ); // unexpected
        } /* switch() */
    } // while
}

};
