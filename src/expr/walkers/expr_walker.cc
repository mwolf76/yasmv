/**
 * @file expr_walker.cc
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
#include <expr_walker.hh>

ExprWalker& ExprWalker::operator() (const Expr_ptr expr)
{
    // pre-walking hook
    this->pre_hook();

    activation_record call(expr);

    // setup toplevel act. record and perform walk
    f_recursion_stack.push(call);
    walk();

    // post-walking hook
    this->post_hook();

    return *this;
}

void ExprWalker::walk ()
{
    size_t rec_level = f_recursion_stack.size();
    assert (0 != rec_level);

    size_t rec_goal = rec_level -1; // support re-entrant invocation
    while(f_recursion_stack.size() != rec_goal) {

    loop:
        activation_record curr = f_recursion_stack.top();
        if (curr.pc != DEFAULT) {

            // restore caller location (simulate call return behavior)
            switch(curr.pc){
            case NEXT_1: goto entry_NEXT_1;

            case NEG_1: goto entry_NEG_1;
            case NOT_1: goto entry_NOT_1;

            case PLUS_1: goto entry_PLUS_1;
            case PLUS_2: goto entry_PLUS_2;

            case MUL_1: goto entry_MUL_1;
            case MUL_2: goto entry_MUL_2;

            case SUB_1: goto entry_SUB_1;
            case SUB_2: goto entry_SUB_2;

            case DIV_1: goto entry_DIV_1;
            case DIV_2: goto entry_DIV_2;

            case MOD_1: goto entry_MOD_1;
            case MOD_2: goto entry_MOD_2;

            case AND_1: goto entry_AND_1;
            case AND_2: goto entry_AND_2;

            case OR_1: goto entry_OR_1;
            case OR_2: goto entry_OR_2;

            case XOR_1: goto entry_XOR_1;
            case XOR_2: goto entry_XOR_2;

            case XNOR_1: goto entry_XNOR_1;
            case XNOR_2: goto entry_XNOR_2;

            case IMPLIES_1: goto entry_IMPLIES_1;
            case IMPLIES_2: goto entry_IMPLIES_2;

            case IFF_1: goto entry_IFF_1;
            case IFF_2: goto entry_IFF_2;

            case LSHIFT_1: goto entry_LSHIFT_1;
            case LSHIFT_2: goto entry_LSHIFT_2;

            case RSHIFT_1: goto entry_RSHIFT_1;
            case RSHIFT_2: goto entry_RSHIFT_2;

            case EQ_1: goto entry_EQ_1;
            case EQ_2: goto entry_EQ_2;

            case NE_1: goto entry_NE_1;
            case NE_2: goto entry_NE_2;

            case GT_1: goto entry_GT_1;
            case GT_2: goto entry_GT_2;

            case GE_1: goto entry_GE_1;
            case GE_2: goto entry_GE_2;

            case LT_1: goto entry_LT_1;
            case LT_2: goto entry_LT_2;

            case LE_1: goto entry_LE_1;
            case LE_2: goto entry_LE_2;

            case ITE_1: goto entry_ITE_1;
            case ITE_2: goto entry_ITE_2;

            case COND_1: goto entry_COND_1;
            case COND_2: goto entry_COND_2;

            case DOT_1: goto entry_DOT_1;
            case DOT_2: goto entry_DOT_2;

            case PARAMS_1: goto entry_PARAMS_1;
            case PARAMS_2: goto entry_PARAMS_2;

            case SUBSCRIPT_1: goto entry_SUBSCRIPT_1;
            case SUBSCRIPT_2: goto entry_SUBSCRIPT_2;

            case SET_1: goto entry_SET_1;

            case COMMA_1: goto entry_COMMA_1;
            case COMMA_2: goto entry_COMMA_2;

            default: throw UnsupportedEntryPointException(curr.pc);

            }
        }

        assert(NULL != curr.expr);
        pre_node_hook(curr.expr);

        switch (curr.expr->f_symb) {

        // unary temporal
        case NEXT:
            if (walk_next_preorder(curr.expr)) {
                f_recursion_stack.top().pc = NEXT_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_NEXT_1:
                walk_next_postorder(curr.expr);
            }
            break;

        // unary arithmetic/logical
        case NEG:
            if (walk_neg_preorder(curr.expr)) {
                f_recursion_stack.top().pc = NEG_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_NEG_1:
                walk_neg_postorder(curr.expr);
            }
            break;

        case NOT:
            if (walk_not_preorder(curr.expr)) {
                f_recursion_stack.top().pc = NOT_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_NOT_1:
                walk_not_postorder(curr.expr);
            }
            break;

        // basic arithmetical
        case PLUS:
            if (walk_add_preorder(curr.expr)) {
                f_recursion_stack.top().pc = PLUS_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_PLUS_1:
                if (walk_add_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = PLUS_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_PLUS_2:
                walk_add_postorder(curr.expr);
            }
            break;

        case SUB:
            if (walk_sub_preorder(curr.expr)) {
                f_recursion_stack.top().pc = SUB_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_SUB_1:
                if (walk_sub_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = SUB_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_SUB_2:
                walk_sub_postorder(curr.expr);
            }
            break;

        case MUL:
            if (walk_mul_preorder(curr.expr)) {
                f_recursion_stack.top().pc = MUL_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_MUL_1:
                if (walk_mul_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = MUL_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_MUL_2:
                walk_mul_postorder(curr.expr);
            }
            break;

        case DIV:
            if (walk_div_preorder(curr.expr)) {
                f_recursion_stack.top().pc = DIV_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_DIV_1:
                if (walk_div_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = DIV_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_DIV_2:
                walk_div_postorder(curr.expr);
            }
            break;

        case MOD:
            if (walk_mod_preorder(curr.expr)) {
                f_recursion_stack.top().pc = MOD_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_MOD_1:
                if (walk_mod_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = MOD_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_MOD_2:
                walk_mod_postorder(curr.expr);
            }
            break;

        // basic logical
        case AND:
            if (walk_and_preorder(curr.expr)) {
                f_recursion_stack.top().pc = AND_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_AND_1:
                if (walk_and_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = AND_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_AND_2:
                walk_and_postorder(curr.expr);
            }
            break;

        case OR:
            if (walk_or_preorder(curr.expr)) {
                f_recursion_stack.top().pc = OR_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_OR_1:
                if (walk_or_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = OR_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_OR_2:
                walk_or_postorder(curr.expr);
            }
            break;

        case XOR:
            if (walk_xor_preorder(curr.expr)) {
                f_recursion_stack.top().pc = XOR_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_XOR_1:
                if (walk_xor_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = XOR_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_XOR_2:
                walk_xor_postorder(curr.expr);
            }
            break;

        case XNOR:
            if (walk_xnor_preorder(curr.expr)) {
                f_recursion_stack.top().pc = XNOR_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_XNOR_1:
                if (walk_xnor_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = XNOR_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_XNOR_2:
                walk_xnor_postorder(curr.expr);
            }
            break;

        case IMPLIES:
            if (walk_implies_preorder(curr.expr)) {
                f_recursion_stack.top().pc = IMPLIES_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_IMPLIES_1:
                if (walk_implies_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = IMPLIES_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_IMPLIES_2:
                walk_implies_postorder(curr.expr);
            }
            break;

        case IFF:
            if (walk_iff_preorder(curr.expr)) {
                f_recursion_stack.top().pc = IFF_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_IFF_1:
                if (walk_iff_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = IFF_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_IFF_2:
                walk_iff_postorder(curr.expr);
            }
            break;

        case LSHIFT:
            if (walk_lshift_preorder(curr.expr)) {
                f_recursion_stack.top().pc = LSHIFT_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_LSHIFT_1:
                if (walk_lshift_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = LSHIFT_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_LSHIFT_2:
                walk_lshift_postorder(curr.expr);
            }
            break;

        case RSHIFT:
            if (walk_rshift_preorder(curr.expr)) {
                f_recursion_stack.top().pc = RSHIFT_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_RSHIFT_1:
                if (walk_rshift_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = RSHIFT_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_RSHIFT_2:
                walk_rshift_postorder(curr.expr);
            }
            break;

        // relational
        case EQ:
            if (walk_eq_preorder(curr.expr)) {
                f_recursion_stack.top().pc = EQ_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_EQ_1:
                if (walk_eq_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = EQ_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_EQ_2:
                walk_eq_postorder(curr.expr);
            }
            break;

        case NE:
            if (walk_ne_preorder(curr.expr)) {
                f_recursion_stack.top().pc = NE_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_NE_1:
                if (walk_ne_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = NE_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_NE_2:
                walk_ne_postorder(curr.expr);
            }
            break;

        case GT:
            if (walk_gt_preorder(curr.expr)) {
                f_recursion_stack.top().pc = GT_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_GT_1:
                if (walk_gt_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = GT_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_GT_2:
                walk_gt_postorder(curr.expr);
            }
            break;


        case GE:
            if (walk_ge_preorder(curr.expr)) {
                f_recursion_stack.top().pc = GE_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_GE_1:
                if (walk_ge_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = GE_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_GE_2:
                walk_ge_postorder(curr.expr);
            }
            break;


        case LT:
            if (walk_lt_preorder(curr.expr)) {
                f_recursion_stack.top().pc = LT_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_LT_1:
                if (walk_lt_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = LT_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_LT_2:
                walk_lt_postorder(curr.expr);
            }
            break;

        case LE:
            if (walk_le_preorder(curr.expr)) {
                f_recursion_stack.top().pc = LE_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_LE_1:
                if (walk_le_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = LE_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_LE_2:
                walk_le_postorder(curr.expr);
            }
            break;

        // ITE
        case ITE:
            if (walk_ite_preorder(curr.expr)) {
                f_recursion_stack.top().pc = ITE_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_ITE_1:
                if (walk_ite_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = ITE_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_ITE_2:
                walk_ite_postorder(curr.expr);
            }
            break;

        case COND:
            if (walk_cond_preorder(curr.expr)) {
                f_recursion_stack.top().pc = COND_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_COND_1:
                if (walk_cond_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = COND_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_COND_2:
                walk_cond_postorder(curr.expr);
            }
            break;

        case DOT:
            if (walk_dot_preorder(curr.expr)) {
                f_recursion_stack.top().pc = DOT_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_DOT_1:
                if (walk_dot_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = DOT_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_DOT_2:
                walk_dot_postorder(curr.expr);
            }
            break;

        case PARAMS:
            if (walk_params_preorder(curr.expr)) {
                f_recursion_stack.top().pc = PARAMS_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_PARAMS_1:
                if (walk_params_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = PARAMS_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_PARAMS_2:
                walk_params_postorder(curr.expr);
            }
            break;

        case SUBSCRIPT:
            if (walk_subscript_preorder(curr.expr)) {
                f_recursion_stack.top().pc = SUBSCRIPT_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_SUBSCRIPT_1:
                if (walk_subscript_inorder(curr.expr)) {
                    f_recursion_stack.top().pc = SUBSCRIPT_2;
                    f_recursion_stack.push(activation_record(curr.expr->u.f_rhs));
                    goto loop;
                }

            entry_SUBSCRIPT_2:
                walk_subscript_postorder(curr.expr);
            }
            break;

        case SET:
            if (walk_neg_preorder(curr.expr)) {
                f_recursion_stack.top().pc = SET_1;
                f_recursion_stack.push(activation_record(curr.expr->u.f_lhs));
                goto loop;

            entry_SET_1:
                walk_neg_postorder(curr.expr);
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


        // leaves
        case ICONST:
        case HCONST:
        case OCONST:

        case IDENT:
            walk_leaf(curr.expr);
            break;

        default:
            throw UnsupportedOperatorException(curr.expr->f_symb);

        } // switch

        assert(NULL != curr.expr);
        post_node_hook(curr.expr);

        f_recursion_stack.pop();
    } // while (!empty)

}
