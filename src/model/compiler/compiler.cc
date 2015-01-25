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

    f_elapsed = clock();

    /* pass 1: preprocessing */
    clear_internals();
    f_preprocess = true;

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);

    // toplevel (time is assumed at 0, arbitraryly nested next allowed)
    f_time_stack.push_back(0);

    /* Invoke walker on the body of the expr to be processed */
    (*this)(body);

    /* pass 2: compilation */
    clear_internals();
    f_preprocess = false;

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);

    // toplevel (time is assumed at 0, arbitraryly nested next allowed)
    f_time_stack.push_back(0);

    /* Invoke walker on the body of the expr to be processed */
    (*this)(body);

    // sanity conditions
    assert(1 == f_add_stack.size());
    assert(1 == f_type_stack.size());
    assert(1 == f_ctx_stack.size());
    assert(1 == f_time_stack.size());

    // Exactly one 0-1 ADD expected here
    ADD res
        (f_add_stack.back());
    assert( res.FindMin().Equals(f_enc.zero()) );
    assert( res.FindMax().Equals(f_enc.one()) );

    unsigned res_sz
        (f_add_stack.size());
    unsigned mcr_sz
        (f_micro_descriptors.size());
    unsigned imux_sz
        (f_mux_map.size());
    unsigned amux_sz
        (f_array_mux_vector.size());

    /* generates additional fragments for MUXes activation, this is
       required for proper encoding of ITEs and array selectors. See
       worker class `CNFMuxcodeInjector` for more details on MUX
       internals. */
    post_process_muxes();

    f_elapsed = clock() - f_elapsed;
    double secs
        ((double) f_elapsed / (double) CLOCKS_PER_SEC);

    DEBUG
        << "Compilation of " << ctx << "::" << body
        << " took " << secs << " seconds, "
        << res_sz << " DDs, "
        << mcr_sz << " Microdescriptors, "
        << imux_sz << " ITE MUXes, "
        << amux_sz << " Array MUXes."
        << std::endl;

    return CompilationUnit( f_add_stack, f_micro_descriptors, f_mux_map, f_array_mux_vector);
}

Compiler::Compiler()
    : f_cache()
    , f_micro_descriptors()
    , f_mux_map()
    , f_toplevel_map()
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

