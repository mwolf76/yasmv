#include <expr.hh>
#include <types.hh>

// static initialization
ExprMgr* ExprMgr::f_instance = NULL;
// const Expr& ExprMgr::nil = Expr();

// get rid of this Goddammit!!!
void link_expr()
{}

bool EnumType::has_symbs() const
{
  bool res = false;
  ExprMgr& em = ExprMgr::INSTANCE();

  for (EnumLiterals::iterator eye = f_literals.begin();
       (!res) && (eye != f_literals.end()); eye ++) {

    res |= em.is_identifier(*eye);
  }

  return res;
}

bool EnumType::has_numbers() const
{
  bool res = false;
  ExprMgr& em = ExprMgr::INSTANCE();

  for (EnumLiterals::iterator eye = f_literals.begin();
       (!res) && (eye != f_literals.end()); eye ++) {

    res |= em.is_numeric(*eye);
  }

  return res;
}
