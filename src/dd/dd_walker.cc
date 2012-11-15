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

DDWalker::DDWalker(CuddMgr& owner)
    : f_owner(owner)
    , f_data(NULL)
{ // DRIVEL << "Initialized walker @" << this << endl;
}

DDWalker::~DDWalker()
{ // DRIVEL << "Deinitialized walker @" << this << endl;
}

DDWalker& DDWalker::operator() (ADD dd)
{
    dd_activation_record call(dd.getNode());

    assert (NULL == f_data);
    size_t nelems = f_owner.dd().getManager()->size;
    f_data = (char *) malloc( nelems * sizeof(char));

    /* 0 is false, 1 is true, 2 is don't care */
    for (unsigned i = 0; i < nelems; ++ i) {
        *( f_data + i ) = 2;
    }

    // setup toplevel act. record and perform walk
    f_recursion_stack.push(call);
    walk();

    /* release temp memory */
    free(f_data); f_data = NULL;

    return *this;
}

void DDWalker::walk ()
{
    size_t rec_level = f_recursion_stack.size();
    assert (0 != rec_level);

    size_t rec_goal = rec_level -1; // support re-entrant invocation
    assert (0 == rec_goal);

    DdNode *N, *Nv, *Nnv;

    /* for fast access to the DD variables array */
    char *cell;

    while(f_recursion_stack.size() != rec_goal) {

    call:
        dd_activation_record curr = f_recursion_stack.top();
        N = Cudd_Regular(curr.node);

        /* if node is a constand and fulfills condition, perform action on it */
        if ( cuddIsConstant(N) ) {
            if (condition(curr.node)) {
                action(cuddV(curr.node));
            }

            // continue
            goto entry_RETURN;
        }

        /* init common to all paths below here */
        cell = f_data + N->index;

        if (Cudd_IsComplement(curr.node)) {
            Nv  = Cudd_Not(cuddT(N));
            Nnv = Cudd_Not(cuddE(N));
        }
        else {
            Nv  = cuddT(N);
            Nnv = cuddE(N);
        }

        // restore caller location (simulate call return behavior)
        if (curr.pc != DD_DEFAULT) {
            switch(curr.pc) {
            case DD_ELSE: goto entry_ELSE;
            case DD_RETURN: goto entry_RETURN;
            default: assert( false ); // unexpected
            }
        } /* pc != DEFAULT */

        // entry_THEN: (fallthru)
        *cell = 0; /* false */
        f_recursion_stack.top().pc = DD_ELSE;
        f_recursion_stack.push(dd_activation_record(Nnv));
        goto call;

    entry_ELSE:
        *cell = 1; /* true */
        f_recursion_stack.top().pc = DD_RETURN;
        f_recursion_stack.push(dd_activation_record(Nv));
        goto call;

    entry_RETURN:
        *cell = 2; /* don't care */

        f_recursion_stack.pop();
    } // while
}
