/**
 *  @file compiler.cc
 *
 *  Copyright (C) 2011-2015 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
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
#include <utility>
#include <compiler.hh>

// synchronized
CompilationUnit Compiler::process(Expr_ptr ctx, Expr_ptr body)
{
    boost::mutex::scoped_lock lock
        (f_process_mutex);

    {
        /* pass 1: preprocessing */
        clear_internals();
        f_preprocess = true;

        // walk body in given ctx
        f_ctx_stack.push_back(ctx);

        // toplevel (time is assumed at 0, arbitraryly nested next allowed)
        f_time_stack.push_back(0);

        /* Invoke walker on the body of the expr to be processed */
        (*this)(body);
    }

    {
        /* pass 2: compilation */
        clear_internals();
        f_preprocess = false;

        // walk body in given ctx
        f_ctx_stack.push_back(ctx);

        // toplevel (time is assumed at 0, arbitraryly nested next allowed)
        f_time_stack.push_back(0);

        /* Invoke walker on the body of the expr to be processed */
        (*this)(body);
    }

    return CompilationUnit( f_add_stack, f_inlined_operator_descriptors,
                            f_expr2bsd_map, f_multiway_selection_descriptors);
}

Compiler::Compiler()
    : f_cache()
    , f_inlined_operator_descriptors()
    , f_expr2bsd_map()
    , f_ite_uf_map()
    , f_type_stack()
    , f_add_stack()
    , f_ctx_stack()
    , f_time_stack()
    , f_owner(ModelMgr::INSTANCE())
    , f_enc(EncodingMgr::INSTANCE())
    , f_temp_auto_index(0)
{
    DRIVEL
        << "Created Compiler @"
        << this
        << std::endl;
}

Compiler::~Compiler()
{
    DRIVEL
        << "Destroying Compiler @"
        << this
        << std::endl;
}

