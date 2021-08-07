/**
 * @file compiler.cc
 * @brief Model compiler subsystem implementation.
 *
 * Copyright (C) 2011-2015 Marco Pensallorto < marco AT pensallorto DOT gmail
 * DOT com >
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

#include <compiler.hh>

namespace compiler {

EStatus& operator++(EStatus& status) {
    return status = static_cast<EStatus> (1 + static_cast <int> (status));
}

Unit Compiler::process(expr::Expr_ptr ctx, expr::Expr_ptr body)
{
    /* the compiler can be shared among multiple strategies running on multiple threads */
    boost::mutex::scoped_lock lock { f_process_mutex };

    f_status = READY;

    /* Pass 1: build encodings */
    build_encodings(ctx, body);

    /* Pass 2: perform boolean compilation using DDs */
    compile(ctx, body);

    /* Pass 3: checking internal structures */
    check_internals(ctx, body);

    /* Pass 4: ITE MUXes, for each descriptor, we need to conjunct `! AND (
       prev_conditions ) AND cnd <-> aux` to the original formula. */
    activate_ite_muxes(ctx, body);

    /* Pass 5: Array MUXes, for each descriptor, push a conjunct `cnd_i <-> act_i, i in
       [0..n_elems[` to the original formula. */
    activate_array_muxes(ctx, body);

    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    return Unit(em.make_dot(ctx, body), f_add_stack, f_inlined_operator_descriptors,
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
    , f_owner(model::ModelMgr::INSTANCE())
    , f_enc(enc::EncodingMgr::INSTANCE())
    , f_preprocessor()
    , f_temp_auto_index(0)
    , f_status(READY)
{
    const void* instance { this };
    DRIVEL
        << "Initialized Compiler @"
        << instance
        << std::endl;
}

Compiler::~Compiler()
{
    const void* instance { this };
    DRIVEL
        << "Destroyed Compiler @"
        << instance
        << std::endl;
}

} // namespace compiler
