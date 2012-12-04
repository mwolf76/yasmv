/**
 * @file full_expr_walker.cc
 * @brief Expression walker
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

#include <expr.hh>
#include <full_expr_walker.hh>

FullWalker::FullWalker()
    : TemporalWalker()
{ // DRIVEL << "Initialized full walker @" << this << endl;
}

FullWalker::~FullWalker()
{ // DRIVEL << "Deinitialized full walker @" << this << endl;
}

void FullWalker::walk()
{
    size_t rec_level = f_recursion_stack.size();
    assert (0 != rec_level);

    size_t rec_goal = rec_level -1; // support re-entrant invocation

 resume:
    while(f_recursion_stack.size() != rec_goal) {

    loop:
        activation_record curr = f_recursion_stack.top();
        if (curr.pc != DEFAULT) {

            // restore caller location (simulate call return behavior)
            switch(curr.pc){
            case SET_1: goto entry_SET_1;

            case COMMA_1: goto entry_COMMA_1;
            case COMMA_2: goto entry_COMMA_2;

            case RANGE_1: goto entry_RANGE_1;
            case RANGE_2: goto entry_RANGE_2;

            // fallback on ancestor's walker and resume
            default:
                try { TemporalWalker::walk(); }
                catch (WalkerException &we) {
                    const char *nls = we.what();
                    DEBUG << "Caught " << nls << ", continuing..." << endl;
                }
                goto resume;
            }
        }

        assert(curr.expr);
        switch (curr.expr->f_symb) {

        case SET:
            if (walk_set_preorder(curr.expr)) {
                f_recursion_stack.top().pc = SET_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_SET_1:
                walk_set_postorder(curr.expr);
            }
            break;

        case COMMA:
            if (walk_comma_preorder(curr.expr)) {
                f_recursion_stack.top().pc = COMMA_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_COMMA_1:
                if (walk_comma_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = COMMA_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_COMMA_2:
                walk_comma_postorder(curr.expr);
            }
            break;

        case RANGE:
            if (walk_range_preorder(curr.expr)) {
                f_recursion_stack.top().pc = RANGE_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_RANGE_1:
                if (walk_range_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = RANGE_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_RANGE_2:
                walk_range_postorder(curr.expr);
            }
            break;


            // fallback on ancestor's walker and resume
        default:
            try {
                TemporalWalker::walk();
            }
            catch (WalkerException &we) {
                string msg (we.what());
                DEBUG << "Caught " << msg
                      << ", continuing..."
                      << endl;
            }
            goto resume;
        } // switch

        f_recursion_stack.pop();
    } // while (!empty)

}
