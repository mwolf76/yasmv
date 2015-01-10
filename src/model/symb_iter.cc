/**
 *  @file symb_iter.cc
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

SymbIter::SymbIter(Model& model, Expr_ptr formula)
    : f_model(model)
    , f_formula(formula)
{
    assert( !f_formula ); // TODO implement COI

    /* Fetch modules from model */
    const Modules& modules = f_model.modules();

    for (Modules::const_iterator mi = modules.begin();
         mi != modules.end(); ++ mi) {

        Module& module = * (*mi).second;

        const Defines& defs = module.defs();
        const Variables& vars = module.vars();

        /* iterate over locals to preserve symbols ordering */
        const ExprVector& locals = module.locals();

        for (ExprVector::const_iterator i = locals.begin();
             i != locals.end(); ++ i) {

            FQExpr key( module.name(), *i);
            Symbol_ptr symbol = NULL;

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
