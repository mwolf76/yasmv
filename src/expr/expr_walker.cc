/*
  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >

  This library is free software; you can redistribute it and/or
  modify it under the terms of the GNU Lesser General Public
  License as published by the Free Software Foundation; either
  version 2.1 of the License, or (at your option) any later version.

  This library is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public
  License along with this library; if not, write to the Free Software
  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

*/

/**
 * @file expr_walker.cc
 *
 * @brief Expression walker
 *
 */
#include <common.hh>

#include <expr.hh>
#include <expr_walker.hh>

Walker::Walker()
{}

Walker::~Walker()
{}

Walker& Walker::operator() (const Expr_ptr expr) {

  // TODO: review this
  assert(f_stack.empty());

  // before walking hook
  this->pre_hook();

  activation_record call(expr);

  // setup toplevel act. record and perform walk
  f_stack.push(call); walk();

  // TODO: review this
  assert(f_stack.empty());

  // after walking hook
  this->post_hook();

  return *this;
}

void Walker::walk () {

  while(! f_stack.empty()) {

  loop:
    activation_record curr = f_stack.top();

    if (curr.pc != DEFAULT) {
      switch(curr.pc){
      case F_1: goto entry_F_1;
      case G_1: goto entry_G_1;
      case X_1: goto entry_X_1;
      case U_1: goto entry_U_1;
      case U_2: goto entry_U_2;
      case R_1: goto entry_R_1;
      case R_2: goto entry_R_2;

      case AF_1: goto entry_AF_1;
      case AG_1: goto entry_AG_1;
      case AX_1: goto entry_AX_1;
      case AU_1: goto entry_AU_1;
      case AU_2: goto entry_AU_2;
      case AR_1: goto entry_AR_1;
      case AR_2: goto entry_AR_2;

      case EF_1: goto entry_EF_1;
      case EG_1: goto entry_EG_1;
      case EX_1: goto entry_EX_1;
      case EU_1: goto entry_EU_1;
      case EU_2: goto entry_EU_2;
      case ER_1: goto entry_ER_1;
      case ER_2: goto entry_ER_2;

      case INIT_1: goto entry_INIT_1;
      case NEXT_1: goto entry_NEXT_1;

      case NEG_1: goto entry_NEG_1;
      case NOT_1: goto entry_NOT_1;

      case ADD_1: goto entry_ADD_1;
      case ADD_2: goto entry_ADD_2;

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


        // ..

      default: assert(0);
      }
    }

    switch (curr.expr->f_symb) {

      // LTL ops
    case F:
      if (walk_F_preorder(curr.expr)) {
        curr.pc = F_1;
        f_stack.push(activation_record(curr.expr->f_lhs));
        goto loop;

      entry_F_1:
        walk_F_postorder(curr.expr);
      }
      break;

    case G:
      if (walk_G_preorder(curr.expr)) {
        curr.pc = G_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_G_1:
        walk_G_postorder(curr.expr);
      }
      break;

    case X:
      if (walk_X_preorder(curr.expr)) {
        curr.pc = X_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_X_1:
        walk_X_postorder(curr.expr);
      }
      break;

    case U:
      if (walk_U_preorder(curr.expr)) {
        curr.pc = U_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_U_1:
        if (walk_U_inorder(curr.expr)) {
          curr.pc = U_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
          goto loop;

        entry_U_2:
          walk_U_postorder(curr.expr);
        }
      }
      break;

    case R:
      if (walk_R_preorder(curr.expr)) {
        curr.pc = R_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_R_1:
        if (walk_R_inorder(curr.expr)) {
          curr.pc = R_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
          goto loop;

        entry_R_2:
          walk_R_postorder(curr.expr);
        }
      }
      break;

      // CTL A ops
    case AF:
      if (walk_AF_preorder(curr.expr)) {
        curr.pc = AF_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_AF_1:
        walk_AF_postorder(curr.expr);
      }
      break;

    case AG:
      if (walk_AG_preorder(curr.expr)) {
        curr.pc = AG_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_AG_1:
        walk_AG_postorder(curr.expr);
      }
      break;

    case AX:
      if (walk_AX_preorder(curr.expr)) {
        curr.pc = AX_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_AX_1:
        walk_AX_postorder(curr.expr);
      }
      break;

    case AU:
      if (walk_AU_preorder(curr.expr)) {
        curr.pc = AU_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_AU_1:
        if (walk_AU_inorder(curr.expr)) {
          curr.pc = AU_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
          goto loop;

        entry_AU_2:
          walk_AU_postorder(curr.expr);
        }
      }

    case AR:
      if (walk_AR_preorder(curr.expr)) {
        curr.pc = AR_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_AR_1:
        if (walk_AR_inorder(curr.expr)) {
          curr.pc = AR_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
          goto loop;

        entry_AR_2:
          walk_AR_postorder(curr.expr);
        }
      }

      // CTL E ops
    case EF:
      if (walk_EF_preorder(curr.expr)) {
        curr.pc = EF_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_EF_1:
        walk_EF_postorder(curr.expr);
      }
      break;

    case EG:
      if (walk_EG_preorder(curr.expr)) {
        curr.pc = EG_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_EG_1:
        walk_EG_postorder(curr.expr);
      }
      break;

    case EX:
      if (walk_EX_preorder(curr.expr)) {
        curr.pc = EX_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_EX_1:
        walk_EX_postorder(curr.expr);
      }
      break;

    case EU:
      if (walk_EU_preorder(curr.expr)) {
        curr.pc = EU_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_EU_1:
        if (walk_EU_inorder(curr.expr)) {
          curr.pc = EU_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
          goto loop;

        entry_EU_2:
          walk_EU_postorder(curr.expr);
        }
      }

    case ER:
      if (walk_ER_preorder(curr.expr)) {
        curr.pc = ER_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_ER_1:
        if (walk_ER_inorder(curr.expr)) {
          curr.pc = ER_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
          goto loop;

        entry_ER_2:
          walk_ER_postorder(curr.expr);
        }
      }

      // unary temporal
    case INIT:
      if (walk_init_preorder(curr.expr)) {
        curr.pc = INIT_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_INIT_1:
        walk_init_postorder(curr.expr);
      }
      break;

    case NEXT:
      if (walk_next_preorder(curr.expr)) {
        curr.pc = NEXT_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_NEXT_1:
        walk_next_postorder(curr.expr);
      }
      break;

      // unary
    case NEG:
      if (walk_next_preorder(curr.expr)) {
        curr.pc = NEG_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_NEG_1:
        walk_neg_postorder(curr.expr);
      }
      break;

    case NOT:
      if (walk_next_preorder(curr.expr)) {
        curr.pc = NOT_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_NOT_1:
        walk_not_postorder(curr.expr);
      }
      break;

      // basic arithmetical
    case ADD:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = ADD_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_ADD_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = ADD_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_ADD_2:
        walk_add_postorder(curr.expr);
      }
      break;

    case SUB:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = SUB_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_SUB_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = SUB_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_SUB_2:
        walk_add_postorder(curr.expr);
      }
      break;

    case MUL:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = MUL_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_MUL_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = MUL_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_MUL_2:
        walk_add_postorder(curr.expr);
      }
      break;

    case DIV:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = DIV_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_DIV_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = DIV_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_DIV_2:
        walk_add_postorder(curr.expr);
      }
      break;

    case MOD:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = MOD_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_MOD_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = MOD_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_MOD_2:
        walk_add_postorder(curr.expr);
      }
      break;

      // basic logical
    case AND:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = AND_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_AND_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = AND_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_AND_2:
        walk_add_postorder(curr.expr);
      }
      break;

    case OR:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = OR_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_OR_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = OR_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_OR_2:
        walk_add_postorder(curr.expr);
      }
      break;

    case XOR:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = XOR_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_XOR_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = XOR_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_XOR_2:
        walk_add_postorder(curr.expr);
      }
      break;

    case XNOR:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = XNOR_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_XNOR_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = XNOR_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_XNOR_2:
        walk_add_postorder(curr.expr);
      }
      break;

    case IMPLIES:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = IMPLIES_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_IMPLIES_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = IMPLIES_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_IMPLIES_2:
        walk_add_postorder(curr.expr);
      }
      break;

    case IFF:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = IFF_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_IFF_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = IFF_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_IFF_2:
        walk_add_postorder(curr.expr);
      }
      break;

    case LSHIFT:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = LSHIFT_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_LSHIFT_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = LSHIFT_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_LSHIFT_2:
        walk_add_postorder(curr.expr);
      }
      break;

    case RSHIFT:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = RSHIFT_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_RSHIFT_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = RSHIFT_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_RSHIFT_2:
        walk_add_postorder(curr.expr);
      }
      break;

      // relational
    case EQ:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = EQ_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_EQ_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = EQ_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_EQ_2:
        walk_add_postorder(curr.expr);
      }
      break;

    case NE:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = NE_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_NE_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = NE_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_NE_2:
        walk_add_postorder(curr.expr);
      }
      break;

    case GT:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = GT_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_GT_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = GT_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_GT_2:
        walk_add_postorder(curr.expr);
      }
      break;


    case GE:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = GE_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_GE_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = GE_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_GE_2:
        walk_add_postorder(curr.expr);
      }
      break;


    case LT:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = LT_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_LT_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = LT_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_LT_2:
        walk_add_postorder(curr.expr);
      }
      break;


    case LE:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = LE_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_LE_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = LE_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_LE_2:
        walk_add_postorder(curr.expr);
      }
      break;

      // ITE

    case ITE:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = ITE_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_ITE_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = ITE_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_ITE_2:
        walk_add_postorder(curr.expr);
      }
      break;


    case COND:
      if (walk_add_preorder(curr.expr)) {
        curr.pc = COND_1;
        f_stack.push(activation_record(DEFAULT, curr.expr->f_lhs));
        goto loop;

      entry_COND_1:
        if (walk_add_inorder(curr.expr)) {
          curr.pc = COND_2;
          f_stack.push(activation_record(DEFAULT, curr.expr->f_rhs));
          goto loop;
        }

      entry_COND_2:
        walk_add_postorder(curr.expr);
      }
      break;

    case ICONST:
    case UWCONST:
    case SWCONST:
    case IDENT:
    case LITERAL:
      walk_leaf(curr.expr);

    default: assert(0);
    } // switch

    f_stack.pop();
  } // while (!empty)

}
