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
#include <stack>

SymbIter::SymbIter(Model& model, Expr_ptr formula)
    : f_model(model)
    , f_formula(formula)
{
    assert( !f_formula ); // TODO implement COI

    ExprMgr& em (ExprMgr::INSTANCE());

    const Modules& modules = model.modules();
    Expr_ptr main_module = em.make_main();

    Modules::const_iterator main_iter = modules.find(main_module);

    if (modules.end() == main_iter)
        throw ModuleNotFound(main_module);

    Module& main_ = *main_iter -> second;

    std::stack< std::pair<Expr_ptr, Module_ptr> > stack;
    stack.push( std::make_pair< Expr_ptr, Module_ptr >
                (em.make_empty(), &main_));

    /* walk of var decls, starting from main module */
    while (0 < stack.size()) {

        const std::pair< Expr_ptr, Module_ptr > top (stack.top()); stack.pop();

        Expr_ptr ctx ( top.first );
        Module& module ( * top.second );

        Variables attrs (module.vars());
        Variables::const_iterator vi;
        for (vi = attrs.begin(); attrs.end() != vi; ++ vi) {

            Expr_ptr id( vi -> first.expr());

            Variable& var (* vi -> second);
            Type_ptr vtype (var.type());
            Expr_ptr local_ctx (em.make_dot( ctx, id));

            if (vtype -> is_instance()) {
                InstanceType_ptr instance = vtype -> as_instance();
                Module&  module( model.module(instance -> name()));

                stack.push( std::make_pair< Expr_ptr, Module_ptr >
                            (local_ctx, &module));
            }
            else
                f_symbols.push_back( std::make_pair< Expr_ptr, Symbol_ptr > (ctx, &var ));
        }
    }

    f_iter = f_symbols.begin();
}

SymbIter::~SymbIter()
{
}
