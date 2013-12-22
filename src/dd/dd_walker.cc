/**
 * @file dd_walker.cc
 * @brief DD leaves walker
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/
#include <common.hh>
#include <dd_walker.hh>

/* --- ADD Walker ----------------------------------------------------------- */
ADDWalker::ADDWalker()
{}

ADDWalker::~ADDWalker()
{}

void ADDWalker::pre_hook()
{}

void ADDWalker::post_hook()
{}

ADDWalker& ADDWalker::operator() (ADD dd)
{

    /* setup toplevel act. record and perform walk. */
    add_activation_record call(dd.getNode());
    f_recursion_stack.push(call);

    pre_hook();

    walk();

    post_hook();

    return *this;
}

/* post-order visit strategy */
void ADDWalker::walk ()
{
    while(0 != f_recursion_stack.size()) {
    call:
        add_activation_record curr = f_recursion_stack.top();
        assert ( !Cudd_IsComplement(curr.node));

        /* process constant immediately, no recursion */
        if (cuddIsConstant(curr.node)) {
            if (condition(curr.node)) goto entry_node_POSTORDER;
            else {
                /* just skip it */
                f_recursion_stack.pop();
                continue;
            }
        }

        // restore caller location (simulate call return behavior)
        if (curr.pc != DD_PREORDER) {
            switch(curr.pc) {
            case DD_INORDER: goto entry_node_INORDER;
            case DD_POSTORDER: goto entry_node_POSTORDER;
            default: assert( false ); // unexpected
            }
        }

        /* if node is not a constant and fulfills condition, perform
           action on it. Recur into its children afterwards (pre-order). */
        if (condition(curr.node)) {
            /* recur in THEN */
            f_recursion_stack.top().pc = DD_INORDER;
            f_recursion_stack.push( add_activation_record( cuddT(curr.node)));
            goto call;

        entry_node_INORDER:
            /* recur in ELSE */
            f_recursion_stack.top().pc = DD_POSTORDER;
            f_recursion_stack.push( add_activation_record( cuddE(curr.node)));
            goto call;

        entry_node_POSTORDER:
            /* process node in post-order. */
            action(curr.node);
        }

        f_recursion_stack.pop();
    } // while
}


/* --- YDD Walker ----------------------------------------------------------- */
YDDWalker::YDDWalker()
{}

YDDWalker::~YDDWalker()
{}

void YDDWalker::pre_hook()
{}

void YDDWalker::post_hook()
{}

YDDWalker& YDDWalker::operator() (const YDD_ptr dd)
{

    /* setup toplevel act. record and perform walk. */
    ydd_activation_record call(dd);
    f_recursion_stack.push(call);

    pre_hook();

    walk();

    post_hook();

    return *this;
}

/* post-order visit strategy */
void YDDWalker::walk ()
{
    while(0 != f_recursion_stack.size()) {
    call:
        ydd_activation_record curr = f_recursion_stack.top();

        /* process constant immediately, no recursion */
        if (curr.node->is_const()) {
            if (condition(curr.node)) goto entry_node_POSTORDER;
            else {
                /* just skip it */
                f_recursion_stack.pop();
                continue;
            }
        }

        // restore caller location (simulate call return behavior)
        if (curr.pc != DD_PREORDER) {
            switch(curr.pc) {
            case DD_INORDER: goto entry_node_INORDER;
            case DD_POSTORDER: goto entry_node_POSTORDER;
            default: assert( false ); // unexpected
            }
        }

        /* if node is not a constant and fulfills condition, perform
           action on it. Recur into its children afterwards (pre-order). */
        if (condition(curr.node)) {
            /* recur in THEN */
            f_recursion_stack.top().pc = DD_INORDER;
            f_recursion_stack.push( ydd_activation_record( curr.node->Then()));
            goto call;

        entry_node_INORDER:
            /* recur in ELSE */
            f_recursion_stack.top().pc = DD_POSTORDER;
            f_recursion_stack.push( ydd_activation_record( curr.node->Else()));
            goto call;

        entry_node_POSTORDER:
            /* process node in post-order. */
            action(curr.node);
        }

        f_recursion_stack.pop();
    } // while
}
