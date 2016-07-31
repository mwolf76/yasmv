/**
 * @file symb_iter.cc
 * @brief Symbol Iterator class implementation.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#include <model.hh>
#include <stack>

SymbIter::SymbIter(Model& model, Expr_ptr formula)
    : f_model(model)
    , f_formula(formula)
{
    assert( !f_formula ); // TODO implement COI

    ExprMgr& em
        (ExprMgr::INSTANCE());
    const Modules& modules
        (model.modules());
    Expr_ptr main_module
        (em.make_main());

    Modules::const_iterator main_iter
        (modules.find(main_module));

    if (modules.end() == main_iter)
        throw ModuleNotFound(main_module);

    Module& main_
        (*main_iter -> second);

    /* two iterations, putting DEFINEs after VARs. This ensures
       defines can be calculated on-the fly using a single pass. */
#define SI_PASS_VARS (0)
#define SI_PASS_DEFS (1)
    for (int pass = 0; pass < 2; ++ pass) {

        std::stack< std::pair<Expr_ptr, Module_ptr> > stack;
        stack.push( std::make_pair< Expr_ptr, Module_ptr >
                    (em.make_empty(), &main_));

        /* walk of var decls, starting from main module */
        while (0 < stack.size()) {

            const std::pair< Expr_ptr, Module_ptr > top
                (stack.top()); stack.pop();

            Expr_ptr full_name
                (top.first);
            Module& module
                (* top.second);
            Variables vars
                (module.vars());
            Variables::const_iterator vi;
            for (vi = vars.begin(); vars.end() != vi; ++ vi) {

                Expr_ptr id
                    (vi -> first);
                Variable& var
                    (* vi -> second);
                Type_ptr vtype
                    (var.type());
                Expr_ptr inner_name
                    (em.make_dot( full_name, id));

                if (vtype -> is_instance()) {
                    InstanceType_ptr instance = vtype -> as_instance();
                    Module&  module( model.module(instance -> name()));

                    stack.push( std::make_pair< Expr_ptr, Module_ptr >
                                (inner_name, &module));
                }
                else if (SI_PASS_VARS == pass)
                    f_symbols.push_back(std::make_pair< Expr_ptr, Symbol_ptr >
                                        (full_name, &var ));
            }

            if (SI_PASS_DEFS == pass) {
                Defines defs (module.defs());
                Defines::const_iterator di;
                for (di = defs.begin(); defs.end() != di; ++ di) {

                    Define& def
                        (* di -> second);

                    f_symbols.push_back(std::make_pair< Expr_ptr, Symbol_ptr >
                                        (full_name, &def));
                }
            }
        }
    }
    f_iter = f_symbols.begin();
}

SymbIter::~SymbIter()
{
}
