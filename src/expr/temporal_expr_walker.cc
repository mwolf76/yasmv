/**
 * @file temporal_expr_walker.cc
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
#include <temporal_expr_walker.hh>

TemporalWalker::TemporalWalker()
    : SimpleWalker()
{ DEBUG << "Initialized temporal walker @" << this << endl; }

TemporalWalker::~TemporalWalker()
{ DEBUG << "Deinitialized temporal walker @" << this << endl; }

void TemporalWalker::walk()
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
            // LTL
            case F_1: goto entry_F_1;
            case G_1: goto entry_G_1;
            case X_1: goto entry_X_1;
            case U_1: goto entry_U_1;
            case U_2: goto entry_U_2;
            case R_1: goto entry_R_1;
            case R_2: goto entry_R_2;

            // CTL A
            case AF_1: goto entry_AF_1;
            case AG_1: goto entry_AG_1;
            case AX_1: goto entry_AX_1;
            case AU_1: goto entry_AU_1;
            case AU_2: goto entry_AU_2;
            case AR_1: goto entry_AR_1;
            case AR_2: goto entry_AR_2;

            // CTL E
            case EF_1: goto entry_EF_1;
            case EG_1: goto entry_EG_1;
            case EX_1: goto entry_EX_1;
            case EU_1: goto entry_EU_1;
            case EU_2: goto entry_EU_2;
            case ER_1: goto entry_ER_1;
            case ER_2: goto entry_ER_2;

            // fallback on ancestor's walker and resume
            default:
                try { SimpleWalker::walk(); }
                catch (WalkerException &we) {
                    const char *nls = we.what();
                    DEBUG << "Caught " << nls << ", continuing..." << endl;
                }
                goto resume;
            }
        }

        assert(curr.expr);
        switch (curr.expr->f_symb) {

        // LTL ops
        case F:
            if (walk_F_preorder(curr.expr)) {
                f_recursion_stack.top().pc = F_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_F_1:
                walk_F_postorder(curr.expr);
            }
            break;

        case G:
            if (walk_G_preorder(curr.expr)) {
                f_recursion_stack.top().pc = G_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_G_1:
                walk_G_postorder(curr.expr);
            }
            break;

        case X:
            if (walk_X_preorder(curr.expr)) {
                f_recursion_stack.top().pc = X_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_X_1:
                walk_X_postorder(curr.expr);
            }
            break;

        case U:
            if (walk_U_preorder(curr.expr)) {
                f_recursion_stack.top().pc = U_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_U_1:
                if (walk_U_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = U_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                    goto loop;

                entry_U_2:
                    walk_U_postorder(curr.expr);
                }
            }
            break;

        case R:
            if (walk_R_preorder(curr.expr)) {
                f_recursion_stack.top().pc = R_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_R_1:
                if (walk_R_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = R_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                    goto loop;

                entry_R_2:
                    walk_R_postorder(curr.expr);
                }
            }
            break;

        // CTL A ops
        case AF:
            if (walk_AF_preorder(curr.expr)) {
                f_recursion_stack.top().pc = AF_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_AF_1:
                walk_AF_postorder(curr.expr);
            }
            break;

        case AG:
            if (walk_AG_preorder(curr.expr)) {
                f_recursion_stack.top().pc = AG_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_AG_1:
                walk_AG_postorder(curr.expr);
            }
            break;

        case AX:
            if (walk_AX_preorder(curr.expr)) {
                f_recursion_stack.top().pc = AX_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_AX_1:
                walk_AX_postorder(curr.expr);
            }
            break;

        case AU:
            if (walk_AU_preorder(curr.expr)) {
                f_recursion_stack.top().pc = AU_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_AU_1:
                if (walk_AU_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = AU_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                    goto loop;

                entry_AU_2:
                    walk_AU_postorder(curr.expr);
                }
            }
            break;

        case AR:
            if (walk_AR_preorder(curr.expr)) {
                f_recursion_stack.top().pc = AR_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_AR_1:
                if (walk_AR_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = AR_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                    goto loop;

                entry_AR_2:
                    walk_AR_postorder(curr.expr);
                }
            }
            break;

        // CTL E ops
        case EF:
            if (walk_EF_preorder(curr.expr)) {
                f_recursion_stack.top().pc = EF_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_EF_1:
                walk_EF_postorder(curr.expr);
            }
            break;

        case EG:
            if (walk_EG_preorder(curr.expr)) {
                f_recursion_stack.top().pc = EG_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_EG_1:
                walk_EG_postorder(curr.expr);
            }
            break;

        case EX:
            if (walk_EX_preorder(curr.expr)) {
                f_recursion_stack.top().pc = EX_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_EX_1:
                walk_EX_postorder(curr.expr);
            }
            break;

        case EU:
            if (walk_EU_preorder(curr.expr)) {
                f_recursion_stack.top().pc = EU_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_EU_1:
                if (walk_EU_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = EU_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                    goto loop;

                entry_EU_2:
                    walk_EU_postorder(curr.expr);
                }
            }
            break;

        case ER:
            if (walk_ER_preorder(curr.expr)) {
                f_recursion_stack.top().pc = ER_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_ER_1:
                if (walk_ER_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = ER_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                    goto loop;

                entry_ER_2:
                    walk_ER_postorder(curr.expr);
                }
            }
            break;

        // fallback on ancestor's walker and resume
        default:
            try { SimpleWalker::walk(); }
            catch (WalkerException &we) {
                const char *nls = we.what();
                DEBUG << "Caught " << nls << ", continuing..." << endl;
            }
            goto resume;
        } // switch

        f_recursion_stack.pop();
    } // while (!empty)

}
