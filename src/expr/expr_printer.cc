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
 * @file printer.cc
 *
 * @brief Expression printer
 *
 */

#include <common.hh>
#include <expr.hh>
#include <printer.hh>

#define LHS (*this) << expr.f_lhs
#define RHS (*this) << expr.f_rhs
#define print f_os <<

Printer::Printer(ostream& os)
  : f_os(os)
{}

Printer& Printer::operator<< (string str) {
  f_os << str ; return (*this);
}

Printer& Printer::operator<< (const Expr& expr) {
  switch (expr.f_symb) {

    // LTL ops
  case F: print "F ("; LHS; print ") "; break;
  case G: print "G ("; LHS; print ") "; break;
  case X: print "X ("; LHS; print ") "; break;
  case U: print "U ("; LHS; print ") "; break;
  case R: print "R ("; LHS; print ") "; break;

    // CTL A ops
  case AF: print "AF ("; LHS; print ") "; break;
  case AG: print "AG ("; LHS; print ") "; break;
  case AX: print "AX ("; LHS; print ") "; break;
  case AU: print "AU ("; LHS; print ") "; break;
  case AR: print "AR ("; LHS; print ") "; break;

    // CTL E ops
  case EF: print "EF ("; LHS; print ") "; break;
  case EG: print "EG ("; LHS; print ") "; break;
  case EX: print "EX ("; LHS; print ") "; break;
  case EU: print "EU ("; LHS; print ") "; break;
  case ER: print "ER ("; LHS; print ") "; break;

    // unary temporal
  case INIT: print "init ("; LHS; print ") "; break;
  case NEXT: print "next ("; LHS; print ") "; break;

    // unary
  case NEG: print "- "; LHS; print " "; break;
  case NOT: print "! "; LHS; print " "; break;

    // basic arithmetical
  case PLUS: print "("; LHS; print " + "; RHS; print ")"; break;
  case SUB:  print "("; LHS; print " - "; RHS; print ")"; break;
  case DIV:  print "("; LHS; print " / "; RHS; print ")"; break;
  case MUL:  print "("; LHS; print " * "; RHS; print ")"; break;
  case MOD:  print "("; LHS; print " % "; RHS; print ")"; break;


    // basic logical
  case AND: print "("; LHS; print " & "; RHS; print ")"; break;
  case OR:  print "("; LHS; print " | "; RHS; print ")"; break;
  case XOR:  print "("; LHS; print " xor "; RHS; print ")"; break;
  case XNOR:  print "("; LHS; print " xnor "; RHS; print ")"; break;
  case IMPLIES:  print "("; LHS; print " -> "; RHS; print ")"; break;
  case IFF:  print "("; LHS; print " <-> "; RHS; print ")"; break;
  case LSHIFT:  print "("; LHS; print " << "; RHS; print ")"; break;
  case RSHIFT:  print "("; LHS; print " >> "; RHS; print ")"; break;

    // relational
  case EQ: print "("; LHS; print " == "; RHS; print ")"; break;
  case NE: print "("; LHS; print " != "; RHS; print ")"; break;
  case GT: print "("; LHS; print " > "; RHS; print ")"; break;
  case GE: print "("; LHS; print " >= "; RHS; print ")"; break;
  case LT: print "("; LHS; print " < "; RHS; print ")"; break;
  case LE: print "("; LHS; print " <= "; RHS; print ")"; break;

    // ITE
  case ITE: print "("; LHS; print " : "; RHS; print ")"; break;
  case COND: LHS; print " ? "; RHS; break;

    // leaves
  case ICONST: print  expr.f_ull; break;
    // case UWCONST: print  expr.f_value; break;
    // case SCONST: print  expr.f_value; break;
  case IDENT: print  expr.f_atom; break;
  case LITERAL: print  expr.f_atom; break;

  case NIL: assert(0);

  default: assert(0);
  }

  return (*this);
}

#endif
