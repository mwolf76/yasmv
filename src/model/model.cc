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
#include <type.hh>
#include <model.hh>

ostream& operator<<(ostream& os, Module& module)
{ return os << module.expr(); }

ostream& operator<<(ostream& os, Exception& e)
{ return os << e.what(); }

void Model::add_module(Expr_ptr name, IModule_ptr module)
{
    DEBUG << "Added module: '" << name << "'" << endl;
    f_modules.insert( make_pair<Expr_ptr, IModule_ptr> (name, module));
}

Module::Module(const Expr_ptr name)
    : f_name(name)

    , f_localVars()
    , f_localDefs()

    , f_init()
    , f_trans()
{}

void Module::add_var(Expr_ptr name, IVariable_ptr var)
{
    Expr_ptr type_repr( var -> type() -> repr());
    DEBUG << "Module " << (*this)
          << ", added var "
          << name
          << ", of type "
          << type_repr
          << endl;

    f_locals.push_back(name);
    f_localVars.insert(make_pair<FQExpr,
                       IVariable_ptr>(FQExpr(expr(), name), var));
}

const ExprVector& Module::locals() const
{
    return f_locals;
}

const Variables& Module::vars() const
{
    return f_localVars;
}

void Module::add_def(Expr_ptr name, IDefine_ptr body)
{
    DEBUG << "Module " << (*this)
          << ", added local def "
          << name
          << endl;

    f_locals.push_back(name);
    f_localDefs.insert(make_pair<FQExpr,
                       IDefine_ptr>(FQExpr(expr(), name), body));
}

const Defines& Module::defs() const
{
    return f_localDefs;
}

void Module::add_init(Expr_ptr expr)
{
    DEBUG << "Module " << (*this)
          << ", added INIT " << expr << endl;
    f_init.push_back(expr);
}

const ExprVector& Module::init() const
{
    return f_init;
}

void Module::add_invar(Expr_ptr expr)
{
    DEBUG << "Module " << (*this)
          << ", added INVAR " << expr << endl;
    f_invar.push_back(expr);
}

const ExprVector& Module::invar() const
{
    return f_invar;
}


void Module::add_trans(Expr_ptr expr)
{
    DEBUG << "Module " << (*this)
          << ", added TRANS " << expr << endl;
    f_trans.push_back(expr);
}

const ExprVector& Module::trans() const
{
    return f_trans;
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

        const Defines& defs = module.defs();
        const Variables& vars = module.vars();

        /* iterate over locals to preserve symbols ordering */
        const ExprVector& locals = module.locals();

        for (ExprVector::const_iterator i = locals.begin();
             i != locals.end(); ++ i) {

            FQExpr key( module.expr(), *i);
            ISymbol_ptr symbol = NULL;

            do {
                Defines::const_iterator di = defs.find(key);
                if (di != defs.end()) {
                    symbol = (*di).second;
                    break;
                }

                Variables::const_iterator vi = vars.find(key);
                if (vi != vars.end()) {
                    symbol = (*vi).second;
                    break;
                }
            } while(0);

            if (symbol)  {
                f_symbols.push_back(symbol);
            }
        }
    }

    f_iter = f_symbols.begin();
}

SymbIter::~SymbIter()
{
}
