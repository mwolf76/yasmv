#include <model.hh>

// static initialization
TypeMgr_ptr TypeMgr::f_instance = NULL;

// static initialization
ModelMgr_ptr ModelMgr::f_instance = NULL;

// symbol resolution
ISymbol_ptr Model::fetch_symbol(const FQExpr& fqexpr)
{
  const Expr_ptr ctx = fqexpr.ctx();
  const Expr_ptr symb = fqexpr.expr();

  Modules::iterator eye = f_modules.find(ctx);
  if (eye == f_modules.end()) throw BadContext(ctx);
  IModule_ptr module = (*eye).second;

  // suggested resolve order: constants, params, defs, vars
  Variables vars = module->get_localVars();
  Variables::iterator viter = vars.find(FQExpr(ctx, symb));
  if (viter != vars.end()) {
    return (*viter).second;
  }

  Defines defs = module->get_localDefs();
  Defines::iterator diter = defs.find(symb);
  if (diter != defs.end()) {
    return (*diter).second;
  }

  Constants cnts = module->get_localConsts();
  Constants::iterator citer = cnts.find(symb);
  if (citer != cnts.end()) {
    return (*citer).second;
  }

  // if all of the above fail...
  throw UnresolvedSymbol(symb, ctx);
}

bool ISymbol::is_variable(void) const
{
  return NULL != dynamic_cast <const IVariable_ptr>
    (const_cast <const ISymbol_ptr> (this));
}

IVariable& ISymbol::as_variable(void) const
{
  IVariable_ptr res = dynamic_cast <const IVariable_ptr>
    (const_cast <const ISymbol_ptr> (this));
  assert (res);
  return (*res);
}

bool ISymbol::is_define(void) const
{
  return NULL != dynamic_cast <const IDefine_ptr>
    (const_cast <const ISymbol_ptr> (this));
}

IDefine& ISymbol::as_define(void) const
{
  IDefine_ptr res = dynamic_cast <const IDefine_ptr>
    (const_cast <const ISymbol_ptr> (this));
  assert (res);
  return (*res);
}

bool ISymbol::is_const() const
{
  return NULL != dynamic_cast <const IConstant_ptr>
    (const_cast <const ISymbol_ptr> (this));
}

IConstant& ISymbol::as_const(void) const
{
  IConstant_ptr res = dynamic_cast <const IConstant_ptr>
    (const_cast <const ISymbol_ptr> (this));
  assert (res);
  return (*res);
}

ostream& operator<<(ostream& os, Module& module)
{ return os << module.get_name(); }

ostream& operator<<(ostream& os, Type_ptr type_ptr )
{ return os << type_ptr->get_repr(); }
