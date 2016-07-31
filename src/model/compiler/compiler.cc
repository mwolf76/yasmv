/**
 * @file compiler.cc
 * @brief Model compiler subsystem implementation.
 *
 * Copyright (C) 2011-2015 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
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

#include <utility>
#include <compiler.hh>

// synchronized
CompilationUnit Compiler::process(Expr_ptr ctx, Expr_ptr body)
{
    boost::mutex::scoped_lock lock
        (f_process_mutex);

    /* Pass 1: build encodings */
    pass1(ctx, body);

    /* Pass 2: perform boolean compilation using DDs */
    pass2(ctx, body);

    /* Pass 3: post-processing needed to activate binary and multiway
       selection MUXes

       1. ITE MUXes, for each descriptor, we need to conjunct
       `! AND ( prev_conditions ) AND cnd <-> aux` to the original
       formula.

       2. Array MUXes, for each descriptor, push a conjunct `cnd_i <->
       act_i, i in [0..n_elems[` to the original formula.
    */
    pass3();

    return CompilationUnit(f_add_stack, f_inlined_operator_descriptors,
                           f_expr2bsd_map, f_multiway_selection_descriptors);
}

Compiler::Compiler()
    : f_compilation_cache()
    , f_inlined_operator_descriptors()
    , f_expr2bsd_map()
    , f_bsuf_map()
    , f_type_stack()
    , f_add_stack()
    , f_ctx_stack()
    , f_time_stack()
    , f_owner(ModelMgr::INSTANCE())
    , f_enc(EncodingMgr::INSTANCE())
    , f_temp_auto_index(0)
{
    const void* instance (this);
    DRIVEL
        << "Created Compiler @"
        << instance
        << std::endl;
}

Compiler::~Compiler()
{
    const void* instance(this);
    DRIVEL
        << "Destroying Compiler @"
        << instance
        << std::endl;
}
