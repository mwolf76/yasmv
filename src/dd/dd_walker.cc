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

#include <dd/cudd_mgr.hh>
#include <dd_walker.hh>

namespace dd {

    /* --- ADD Walker ----------------------------------------------------------- */
    ADDWalker::ADDWalker(Cudd& dd)
        : f_dd(dd)
    {
        const void* instance { this };
        const void* dd_ptr { &dd };

        DEBUG
            << "Created DD walker instance @"
            << instance
            << " (cudd = @"
            << dd_ptr
            << ")"
            << std::endl;
    }

    ADDWalker::~ADDWalker()
    {
        const void* instance { this };
        DEBUG
            << "Destroyed DD walker instance @"
            << instance
            << std::endl;
    }

    ADDWalker& ADDWalker::operator()(ADD dd)
    {
        /* setup toplevel act. record and perform walk. */
        add_activation_record call { dd.getNode() };
        f_recursion_stack.push_back(call);

        /* actions before the walk */
        pre_hook();

        walk();

        /* actions after the walk */
        post_hook();

        return *this;
    }

    /* post-order visit strategy */
    void ADDWalker::walk()
    {
        DdManager* dd_mgr { f_dd.getManager() };
        f_variables = (short int*)
            calloc(dd_mgr->size, sizeof(short));

        while (0 != f_recursion_stack.size()) {
        loop:
            add_activation_record curr { f_recursion_stack.back() };
            assert(!Cudd_IsComplement(curr.node));

            register const DdNode* node { curr.node };

            /* leaves have no children */
            if (cuddIsConstant(node)) {
                curr.pc = DD_WALK_NODE;
            }

            // restore caller location (simulate call return behavior)
            switch (curr.pc) {
                case DD_WALK_LHS:
                    /* recur in THEN (i.e. assume TRUE) */
                    f_variables[node->index] = 1;

                    f_recursion_stack.back().pc = DD_WALK_RHS;
                    f_recursion_stack.push_back(add_activation_record(cuddT(node)));
                    goto loop;

                case DD_WALK_RHS:
                    /* recur in ELSE (i.e. assume FALSE) */
                    f_variables[node->index] = 2;

                    f_recursion_stack.back().pc = DD_WALK_NODE;
                    f_recursion_stack.push_back(add_activation_record(cuddE(node)));
                    goto loop;

                case DD_WALK_NODE:
                    /* process node in post-order. */
                    action(node);

                    /* restore DON'T CARE state */
                    if (!cuddIsConstant(node)) {
                        f_variables[node->index] = 0;
                    }

                    f_recursion_stack.pop_back();
                    break;

                default:
                    assert(false); // unexpected
            }
        }

        free(f_variables);
        f_variables = NULL;
    }

    short ADDWalker::variable(int index)
    {
        assert(f_variables);
        return f_variables[index];
    }

}; // namespace dd
