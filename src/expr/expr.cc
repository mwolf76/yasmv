#include <expr.hh>
#include <expr_mgr.hh>
#include <expr_printer.hh>

// static initialization
ExprMgr* ExprMgr::f_instance = NULL;
// const Expr& ExprMgr::nil = Expr();

// very inefficient
ostream& operator<<(ostream& os, const Expr_ptr t)
{
  Printer (os) << t;
  return os;
}

// -- dummy
void link_expr()
{ cout << "* Expr active" << endl; }
