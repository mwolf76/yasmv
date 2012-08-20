/**
 *  @file model.cc
 *  @brief Model module
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
 *
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2.1 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/

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
{ return os << module.expr(); }

ostream& operator<<(ostream& os, Type_ptr type_ptr )
{ return os << type_ptr->get_repr(); }

ostream& operator<<(ostream& os, AnalyzerException& ae)
{ return os << ae.what(); }


//

Module::Module(const Expr_ptr name)
    : f_name(name)
    , f_formalParams()
    , f_isaDecls()
    , f_localVars()
    , f_localDefs()
    , f_localConsts()
    , f_init()
    , f_invar()
    , f_trans()
    , f_fair()
    , f_assgn()
    , f_ltlspecs()
    , f_ctlspecs()
{}

void Module::add_formalParam(Expr_ptr identifier)
{
    logger << "Module " << (*this)
           << ", adding param " << identifier << endl;
    f_formalParams.push_back(identifier);
}

void Module::add_isaDecl(Expr_ptr identifier)
{
    logger << "Module " << (*this)
           << ", adding isadecl " << identifier << endl;
    f_isaDecls.push_back(identifier);
}


void Module::add_localVar(Expr_ptr name, IVariable_ptr var)
{
    logger << "Module " << (*this)
           << ", adding local var " << var << endl;
    f_localVars.insert(make_pair<FQExpr,
                       IVariable_ptr>(FQExpr(expr(), name), var));
}

void Module::add_localDef(Expr_ptr name, IDefine_ptr def)
{
    logger << "Module " << (*this)
           << ", adding local def " << name << endl;
    f_localDefs.insert(make_pair<FQExpr,
                       IDefine_ptr>(FQExpr(expr(), name), def));
}

void Module::add_localConst(Expr_ptr name, IConstant_ptr k)
{
    logger << "Module " << (*this)
           << ", adding local const " << name << endl;
    f_localConsts.insert(make_pair<FQExpr,
                         IConstant_ptr>(FQExpr(expr(), name), k));
}

void Module::add_assign(IAssign_ptr assign)
{ assert (0); // f_assgn.push_back(assign);
}

void Module::add_init(Expr_ptr expr)
{
    logger << "Module " << (*this)
           << ", adding INIT " << expr << endl;
    f_init.push_back(expr);
}

void Module::add_invar(Expr_ptr expr)
{
    logger << "Module " << (*this)
           << ", adding INVAR " << expr << endl;
    f_invar.push_back(expr);
}

void Module::add_trans(Expr_ptr expr)
{
    logger << "Module " << (*this)
           << ", adding TRANS " << expr << endl;
    f_trans.push_back(expr);
}

void Module::add_fairness(Expr_ptr expr)
{
    logger << "Module " << (*this)
           << ", adding FAIRNESS " << expr << endl;
    f_fair.push_back(expr);
}

void Module::add_ltlspec(Expr_ptr formula)
{
    logger << "Module " << (*this)
           << ", adding LTLSPEC " << formula << endl;
    f_ltlspecs.push_back(formula);
}

void Module::add_ctlspec(Expr_ptr formula)
{
    logger << "Module " << (*this)
           << ", adding CTLSPEC " << formula << endl;
    f_ctlspecs.push_back(formula);
}
