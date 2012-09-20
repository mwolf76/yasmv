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

// TODO: this does not belong here
#include <cudd.hh>
CuddMgr_ptr CuddMgr::f_instance = NULL;

void Model::add_module(Expr_ptr name, IModule_ptr module)
{
    TRACE << "Added module: '" << name << "'" << endl;
    f_modules.insert( make_pair<Expr_ptr, IModule_ptr> (name, module));
}

// symbol resolution
ISymbol_ptr Model::fetch_symbol(const Expr_ptr ctx, const Expr_ptr symb)
{
    Modules::iterator eye = f_modules.find(ctx);
    if (eye == f_modules.end()) throw BadContext(ctx);
    IModule_ptr module = (*eye).second;

    // suggested resolve order: constants, parameters, defines, variables
    Constants cnts = module->get_localConsts();
    Constants::iterator citer = cnts.find(symb);
    if (citer != cnts.end()) {
        return (*citer).second;
    }

    // not yet implemented: params

    Defines defs = module->get_localDefs();
    Defines::iterator diter = defs.find(symb);
    if (diter != defs.end()) {
        return (*diter).second;
    }

    Variables vars = module->get_localVars();
    Variables::iterator viter = vars.find(symb);
    if (viter != vars.end()) {
        return (*viter).second;
    }

    // if all of the above fail...
    throw UnresolvedSymbol(ctx, symb);
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
    TRACE << "Module " << (*this)
          << ", added param " << identifier << endl;
    f_formalParams.push_back(identifier);
}

void Module::add_isaDecl(Expr_ptr identifier)
{
    TRACE << "Module " << (*this)
          << ", added isadecl " << identifier << endl;
    f_isaDecls.push_back(identifier);
}


void Module::add_localVar(Expr_ptr name, IVariable_ptr var)
{
    TRACE << "Module " << (*this)
          << ", added local var " << var << endl;
    f_localVars.insert(make_pair<FQExpr,
                       IVariable_ptr>(FQExpr(expr(), name), var));
}

void Module::add_localDef(Expr_ptr name, IDefine_ptr body)
{
    TRACE << "Module " << (*this)
          << ", added local def " << name << endl;
    f_localDefs.insert(make_pair<FQExpr,
                       IDefine_ptr>(FQExpr(expr(), name), body));
}

void Module::add_localConst(Expr_ptr name, IConstant_ptr k)
{
    TRACE << "Module " << (*this)
          << ", added local const " << name << endl;
    f_localConsts.insert(make_pair<FQExpr,
                         IConstant_ptr>(FQExpr(expr(), name), k));
}

void Module::add_assign(Expr_ptr lvalue, IDefine_ptr def)
{
    TRACE << "Module " << (*this)
          << ", added assign "
          << lvalue
          << " := "
          << def->body()
          << endl;

    f_assgn.insert(make_pair<FQExpr,
                   IDefine_ptr>(FQExpr(expr(), lvalue), def));
}

void Module::add_init(Expr_ptr expr)
{
    TRACE << "Module " << (*this)
          << ", added INIT " << expr << endl;
    f_init.push_back(expr);
}

void Module::add_invar(Expr_ptr expr)
{
    TRACE << "Module " << (*this)
          << ", added INVAR " << expr << endl;
    f_invar.push_back(expr);
}

void Module::add_trans(Expr_ptr expr)
{
    TRACE << "Module " << (*this)
          << ", added TRANS " << expr << endl;
    f_trans.push_back(expr);
}

void Module::add_fairness(Expr_ptr expr)
{
    TRACE << "Module " << (*this)
          << ", added FAIRNESS " << expr << endl;
    f_fair.push_back(expr);
}

void Module::add_ltlspec(Expr_ptr formula)
{
    TRACE << "Module " << (*this)
          << ", added LTLSPEC " << formula << endl;
    f_ltlspecs.push_back(formula);
}

void Module::add_ctlspec(Expr_ptr formula)
{
    TRACE << "Module " << (*this)
          << ", added CTLSPEC " << formula << endl;
    f_ctlspecs.push_back(formula);
}
