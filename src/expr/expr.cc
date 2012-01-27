#include <expr.hh>
#include <expr_mgr.hh>

// static initialization
ExprMgr* ExprMgr::f_instance = NULL;
// const Expr& ExprMgr::nil = Expr();

ostream& operator<<(ostream& os, const Expr& t)
{ return os << ""; }

// -- dummy
void link_expr()
{ cout << "* Expr active" << endl; }
