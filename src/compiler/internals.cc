/**
 * @file internals.cc
 * @brief Model compiler subsystem, internals implementation.
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

#include <compiler.hh>

namespace compiler {

/* auto id generator */
expr::Expr_ptr Compiler::make_auto_id()
{
    expr::ExprMgr& em
        (f_owner.em());

    std::ostringstream oss;
    oss << "__tmp" << f_temp_auto_index ++ ;

    return em.make_identifier(oss.str());
}

/* build an auto fresh ADD variable and register its encoding */
ADD Compiler::make_auto_dd()
{
    expr::ExprMgr& em
        (f_owner.em());
    type::TypeMgr& tm
        (f_owner.tm());
    type::Type_ptr boolean
        (tm.find_boolean());

    enc::BooleanEncoding_ptr be
        (reinterpret_cast<enc::BooleanEncoding_ptr>
         (f_enc.make_encoding( boolean )));

    // register encoding, a FQExpr is needed for UCBI booking
    expr::Expr_ptr aid
        (make_auto_id());
    expr::Expr_ptr ctx
        (f_ctx_stack.back());
    step_t time
        (f_time_stack.back());

    expr::TimedExpr key
        (em.make_dot( ctx, aid), time);
    f_enc.register_encoding(key, be);

    dd::DDVector& bits (be -> bits());
    return bits[0]; // just one
}

/* build an auto DD vector of fresh ADD variables. */
void Compiler::make_auto_ddvect(dd::DDVector& dv, unsigned width)
{
    assert(0 == dv.size());
    for (unsigned i = 0; i < width; ++ i )
        dv.push_back(make_auto_dd());
}

void Compiler::pre_node_hook(expr::Expr_ptr expr)
{
    DRIVEL
        << "compiler pre-node: "
        << expr
        << std::endl;

    /* assemble memoization key */
    assert( 0 < f_ctx_stack.size() );
    expr::Expr_ptr ctx
        (f_ctx_stack.back());

    assert(0 < f_time_stack.size());
    step_t time
        (f_time_stack.back());

    expr::TimedExpr key
        (f_owner.em().make_dot(ctx, expr), time);

    if (f_status == ENCODING)
        DRIVEL
            << "(encoding) " << key << "..."
            << std::endl;
    else if (f_status == COMPILING)
        DRIVEL
            << "(compiling) " << key << "..."
            << std::endl;
    else assert(false); /* unreachable */
}

void Compiler::post_node_hook(expr::Expr_ptr expr)
{
    DRIVEL
        << "compiler post-node: "
        << expr
        << std::endl;

    expr::ExprMgr& em
        (f_owner.em());

    /* cache is disabled for SETs, COMMAs and CONDs. This allows for
       anonymous determinization variables on the fly. */
    if (em.is_cond(expr) ||
        em.is_set(expr)  ||
        em.is_set_comma(expr))
        return;

    /* no caching during encoding */
    if (f_status == ENCODING)
        return;

    /* no cache when compiling types */
    if (em.is_type(expr))
        return;

    /* assemble memoization key */
    assert(0 < f_ctx_stack.size());
    expr::Expr_ptr ctx
        (f_ctx_stack.back());

    assert(0 < f_time_stack.size());
    step_t time
        (f_time_stack.back());

    expr::TimedExpr key
        (em.make_dot( ctx, expr), time);

    assert(0 < f_type_stack.size());
    type::Type_ptr type = f_type_stack.back();

    if (type -> is_time())
        return;

    if (type -> is_instance())
        return;

    if (type -> is_array())
        return;

    if (type -> is_scalar()) {
        dd::DDVector dv;
        unsigned i, width = type -> width();

        if (width > f_add_stack.size()) {
            unsigned add_stack_size
                (f_add_stack.size());

            ERR
                << "width: "
                << width
                << ", max expected: "
                << add_stack_size
                << std::endl;
            assert(false);
        }

        dd::DDVector::reverse_iterator ri;
        for (i = 0, ri = f_add_stack.rbegin();
             i < width; ++ i, ++ ri) {
            dv.push_back(*ri);
        }
        assert (dv.size() == width);

        expr::Expr_ptr timedExpression
            (em.make_at(em.make_instant(time), em.make_dot(ctx, expr)));

        /* memoize result */
        f_compilation_cache.insert( std::pair<expr::TimedExpr, Unit>
            (key, Unit(timedExpression, dv, f_inlined_operator_descriptors,
                       f_expr2bsd_map, f_multiway_selection_descriptors)));

        return;
    }

    assert(false);
}

bool Compiler::cache_miss(const expr::Expr_ptr expr)
{
    expr::Expr_ptr ctx
        (f_ctx_stack.back());

    expr::TimedExpr key
        (f_owner.em().make_dot( f_ctx_stack.back(), expr), f_time_stack.back());

    CompilationMap::iterator eye
        (f_compilation_cache.find(key));

    if (eye != f_compilation_cache.end()) {
        const type::Type_ptr type
            (f_owner.type(expr, ctx));

        DRIVEL
            << "Cache hit for " << expr
            << ", type is " << type
            << std::endl;

        Unit& unit
            ((*eye).second);

        /* push cached DDs (reversed) */
        {
            const dd::DDVector& dds
                (unit.dds());

            dd::DDVector::const_reverse_iterator i;
            for (i = dds.rbegin(); i != dds.rend(); ++ i )
                f_add_stack.push_back(*i);
        }

        /* push cached microcode inlined operator descriptors */
        {
            const InlinedOperatorDescriptors& vec
                (unit.inlined_operator_descriptors());

            InlinedOperatorDescriptors::const_iterator i;
            for (i = vec.begin(); vec.end() != i; ++ i)
                f_inlined_operator_descriptors.push_back(*i);
        }

        /* push cached binary selection descriptors */
        {
            const Expr2BinarySelectionDescriptorsMap& map
                (unit.binary_selection_descriptors_map());

            Expr2BinarySelectionDescriptorsMap::const_iterator i;
            for (i = map.begin(); map.end() != i; ++ i)
                f_expr2bsd_map.insert(*i);
        }

        /* push cached Array multiplexer chains */
        {
            const MultiwaySelectionDescriptors& vec
                (unit.array_mux_descriptors());

            MultiwaySelectionDescriptors::const_iterator i;
            for (i = vec.begin(); vec.end() != i; ++ i)
                f_multiway_selection_descriptors.push_back(*i);
        }

        /* push cached type */
        f_type_stack.push_back(type);

        /* cache hit */
        return false;
    }

    /* cache miss */
    return true;
}

void Compiler::pre_hook()
{}

void Compiler::post_hook()
{}

void Compiler::clear_internals()
{
    f_add_stack.clear();
    f_type_stack.clear();
    f_ctx_stack.clear();
    f_time_stack.clear();

    f_inlined_operator_descriptors.clear();
    f_expr2bsd_map.clear();
    f_multiway_selection_descriptors.clear();
    f_bsuf_map.clear();
}

void Compiler::build_encodings(expr::Expr_ptr ctx, expr::Expr_ptr body)
{
    const void *p { ctx };
    DEBUG
        << "(pass 1/5) building encodings for "
        << "`" << ctx << "` (@" << p << ")"
        << " :: "
        << body
        << std::endl;

    ++ f_status;
    assert (EStatus::ENCODING == f_status);

    clear_internals();
    f_ctx_stack.push_back(ctx);
    f_time_stack.push_back(0);
    (*this)(body);
}

void Compiler::compile(expr::Expr_ptr ctx, expr::Expr_ptr body)
{
    const void *p { ctx };
    DEBUG
        << "(pass 2/5) compiling for "
        << "`" << ctx << "` (@" << p << ")"
        << " :: "
        << body
        << std::endl;

    ++ f_status;
    assert (EStatus::COMPILING == f_status);

    clear_internals();
    f_ctx_stack.push_back(ctx);
    f_time_stack.push_back(0);
    (*this)(body);
}

void Compiler::check_internals(expr::Expr_ptr ctx, expr::Expr_ptr body)
{
    const void *p { ctx };
    DEBUG
        << "(pass 3/5) checking internals for "
        << "`" << ctx << "` (@" << p << ")"
        << " :: "
        << body
        << std::endl;

    ++ f_status;
    assert (EStatus::CHECKING == f_status);

    /* Exactly one 0-1 ADD expected here */
    ADD res { f_add_stack.back() };
    assert(1 == f_add_stack.size());

    assert(1 == f_add_stack.size());
    assert(1 == f_type_stack.size());
    assert(1 == f_ctx_stack.size());
    assert(1 == f_time_stack.size());

    assert(res.FindMin().Equals(f_enc.zero()));
    assert(res.FindMax().Equals(f_enc.one()));
}

void Compiler::activate_ite_muxes(expr::Expr_ptr ctx, expr::Expr_ptr body)
{
    const void *p { ctx };

    DEBUG
        << "(pass 4/5) activating ITE MUXes for "
        << "`" << ctx << "` (@" << p << ")"
        << " :: "
        << body
        << std::endl;

    ++ f_status;
    assert (EStatus::ACTIVATING_ITE_MUXES == f_status);

    /* ITE MUXes */
    for (Expr2BinarySelectionDescriptorsMap::const_iterator i = f_expr2bsd_map.begin();
         f_expr2bsd_map.end() != i; ++ i) {

        expr::Expr_ptr toplevel { i -> first };
        const BinarySelectionDescriptors& descriptors { i -> second };

        DRIVEL
            << "Processing ITE MUX activation clauses for `"
            << toplevel << "`"
            << std::endl;

        ADD prev { f_enc.zero() };

        BinarySelectionDescriptors::const_reverse_iterator j;
        for (j = descriptors.rbegin(); descriptors.rend() != j; ++ j) {
            ADD act { prev.Cmpl().Times(j -> cnd()) };

            PUSH_DD(act.Xnor(j -> aux()));
            prev = act;
        }
    }
}

void Compiler::activate_array_muxes(expr::Expr_ptr ctx, expr::Expr_ptr body)
{
    const void *p { ctx };
    DEBUG
        << "(pass 4/5) activating array MUXes for  "
        << "`" << ctx << "` (@" << p << ")"
        << " :: "
        << body
        << std::endl;

    ++ f_status;
    assert (EStatus::ACTIVATING_ARRAY_MUXES == f_status);

    /* Array MUXes */
    MultiwaySelectionDescriptors::const_iterator i;
    for (i = f_multiway_selection_descriptors.begin();
         f_multiway_selection_descriptors.end() != i; ++ i) {

        const dd::DDVector& cnds { i -> cnds() };
        const dd::DDVector& acts { i -> acts() };

        dd::DDVector::const_iterator ci { begin(cnds) };
        dd::DDVector::const_iterator ai { begin(acts) };

        while (cnds.end() != ci) {
            PUSH_DD((*ci).Xnor(*ai));
            ++ ci;
            ++ ai;
        }
        assert(acts.end() == ai);
    }
}

enc::Encoding_ptr Compiler::find_encoding( const expr::TimedExpr& key, const type::Type_ptr type )
{
    enc::Encoding_ptr res;

    /* build a new encoding for this symbol if none is available. */
    res = f_enc.find_encoding(key);
    if (! res) {
        DEBUG
            << "Registering new encoding of type "
            << type << " for " << key
            << std::endl;

        res = f_enc.make_encoding(type);
        f_enc.register_encoding(key, res);
    }

    assert( NULL != res );
    return res;
}

} // namespace compiler