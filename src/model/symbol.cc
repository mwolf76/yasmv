/**
 *  @file symbol.cc
 *  @brief Symbol classes
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
#include <type_exceptions.hh>

void Model::add_module(Expr_ptr name, IModule_ptr module)
{
    DEBUG << "Added module: '" << name << "'" << endl;
    f_modules.insert( make_pair<Expr_ptr, IModule_ptr> (name, module));
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

bool ISymbol::is_temporary(void) const
{
    return NULL != dynamic_cast <const ITemporary_ptr>
        (const_cast <const ISymbol_ptr> (this));
}

ITemporary& ISymbol::as_temporary(void) const
{
    ITemporary_ptr res = dynamic_cast <const ITemporary_ptr>
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

ostream& operator<<(ostream& os, AnalyzerException& ae)
{ return os << ae.what(); }


//

Module::Module(const Expr_ptr name)
    : f_name(name)

    , f_localConsts()
    , f_localVars()
    , f_localDefs()

    , f_init()
    , f_trans()
{}

void Module::add_localVar(Expr_ptr name, IVariable_ptr var)
{
    DEBUG << "Module " << (*this)
          << ", added local var " << var << endl;
    f_localVars.insert(make_pair<FQExpr,
                       IVariable_ptr>(FQExpr(expr(), name), var));
}

void Module::add_localDef(Expr_ptr name, IDefine_ptr body)
{
    DEBUG << "Module " << (*this)
          << ", added local def " << name << endl;
    f_localDefs.insert(make_pair<FQExpr,
                       IDefine_ptr>(FQExpr(expr(), name), body));
}

void Module::add_localConst(Expr_ptr name, IConstant_ptr k)
{
    DEBUG << "Module " << (*this)
          << ", added local const " << name << endl;
    f_localConsts.insert(make_pair<FQExpr,
                         IConstant_ptr>(FQExpr(expr(), name), k));
}

void Module::add_init(Expr_ptr expr)
{
    DEBUG << "Module " << (*this)
          << ", added INIT " << expr << endl;
    f_init.push_back(expr);
}

void Module::add_trans(Expr_ptr expr)
{
    DEBUG << "Module " << (*this)
          << ", added TRANS " << expr << endl;
    f_trans.push_back(expr);
}

Model::Model()
    : f_modules()
{
    DEBUG << "Initialized Model instance @" << this << endl;
}

Model::~Model()
{
    // TODO: free memory for symbols... (they've been allocated using new)
}

SymbIter::SymbIter(IModel& model, Expr_ptr formula)
    : f_model(model)
    , f_formula(formula)
{
    assert( !f_formula ); // TODO implement COI

    /* Fetch modules from model */
    const Modules& modules = f_model.modules();

    for (Modules::const_iterator mi = modules.begin();
         mi != modules.end(); ++ mi) {

        IModule& module = * (*mi).second;

        { /* defines */
            Defines defs = module.get_localDefs();
            for (Defines::const_iterator di = defs.begin();
                 di != defs.end(); ++ di) {

                IDefine_ptr def = (*di).second;
                f_symbols.push_back(def);
            }
        }

        { /* variables */
            Variables vars = module.get_localVars();
            for (Variables::const_iterator vi = vars.begin();
                 vi != vars.end(); ++ vi) {

                IVariable_ptr var = (*vi).second;
                f_symbols.push_back(var);
            }
        }
    }

    f_iter = f_symbols.begin();
}

SymbIter::~SymbIter()
{
}
