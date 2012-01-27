#include <expr.hh>
#include <expr_printer.hh>

// static initialization
ExprMgr* ExprMgr::f_instance = NULL;
// const Expr& ExprMgr::nil = Expr();

ostream& operator<<(ostream& os, const Expr_ptr t)
{ Printer (os) << t; return os; }

void link_expr()
{}
