/**
 * @file walker.cc
 * @brief Expression compiler subsystem, walker pattern implementations.
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

#include <proxy.hh>

/**
 * Compilation engine is implemented using a simple expression walker
 * pattern: (a) on preorder, return true if the node has not yet been
 * visited; (b) always do in-order (for binary nodes); (c) perform
 * proper compilation in post-order hooks.

 * The compiler does two full traversals of the input expr:
 * 1. f_preprocess, encodings are built - postorder hooks are skipped;
 * 2. ! f_preprocess proper compilation is carried out.
 */

bool Compiler::walk_next_preorder(const Expr_ptr expr)
{
    step_t curr_time
        (f_time_stack.back());
    f_time_stack.push_back(curr_time + 1);
    return true;
}
void Compiler::walk_next_postorder(const Expr_ptr expr)
{
    assert (0 < f_time_stack.size());
    f_time_stack.pop_back(); // reset time stack
}

bool Compiler::walk_neg_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Compiler::walk_neg_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_unary_algebraic(expr))
        algebraic_neg(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Compiler::walk_not_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_unary_boolean(expr))
        boolean_not(expr);

    else assert(false); // unreachable
}

bool Compiler::walk_bw_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Compiler::walk_bw_not_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_unary_algebraic(expr))
        algebraic_bw_not(expr);

    else assert(false); // unreachable
}

bool Compiler::walk_add_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_add_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_add_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_algebraic(expr))
        algebraic_plus(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_sub_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_sub_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_sub_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_algebraic(expr)) {
        algebraic_sub(expr);
    }
    else assert( false ); // unexpected
}

bool Compiler::walk_div_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_div_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_div_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_algebraic(expr))
        algebraic_div(expr);

    else assert( false ); // unexpected
}

bool Compiler::walk_mul_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_mul_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_mul_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_algebraic(expr))
        algebraic_mul(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_mod_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_mod_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_mod_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_algebraic(expr))
        algebraic_mod(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_and_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_and_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_boolean(expr))
        boolean_and(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_bw_and_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_bw_and_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_bw_and_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_algebraic(expr))
        algebraic_bw_and(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_or_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_boolean(expr))
        boolean_or(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_bw_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_bw_or_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_bw_or_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_algebraic(expr))
        algebraic_bw_or(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_bw_xor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_bw_xor_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_bw_xor_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_algebraic(expr))
        algebraic_bw_xor(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_bw_xnor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_bw_xnor_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_bw_xnor_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_algebraic(expr))
        algebraic_bw_xnor(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_guard_preorder(const Expr_ptr expr)
{
    ExprMgr& em
        (f_owner.em());

    /* rewrite GUARD into IMPLIES */
    Expr_ptr rewrite
        (em.make_implies( expr->lhs(), expr->rhs()));

    DEBUG
        << "Rewrote "
        << expr
        << " into "
        << rewrite
        << std::endl;

    /* compiling rewritten expression */
    (*this) (rewrite);

    return false;
}
bool Compiler::walk_guard_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_guard_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;
}

bool Compiler::walk_implies_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_implies_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_boolean(expr))
        boolean_implies(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_type_preorder(const Expr_ptr expr)
{
    Type_ptr tp
        (f_owner.tm().find_type_by_def(expr));

    f_type_stack.push_back(tp);

    return false;
}
bool Compiler::walk_type_inorder(const Expr_ptr expr)
{ return false; }
void Compiler::walk_type_postorder(const Expr_ptr expr)
{ assert(false); }

bool Compiler::walk_cast_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_cast_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_cast_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    Expr_ptr ctx
        (f_ctx_stack.back());
    Type_ptr tgt_type
        (f_owner.type( expr->lhs(), ctx));
    Type_ptr src_type
        (f_owner.type( expr->rhs(), ctx));
    Type_ptr cur_type
        (f_type_stack.back());

    assert  (cur_type -> width() ==
             src_type -> width()) ;

    f_type_stack.pop_back();
    f_type_stack.pop_back();
    f_type_stack.push_back(tgt_type);

    if (src_type -> is_boolean() && tgt_type -> is_boolean())
        return; /* nop */

    else if (src_type -> is_boolean() && tgt_type -> is_algebraic())
        algebraic_cast_from_boolean(expr);

    else if (src_type -> is_algebraic() && tgt_type -> is_boolean())
        boolean_cast_from_algebraic(expr);

    else if (src_type -> is_algebraic() && tgt_type -> is_algebraic())
        algebraic_cast_from_algebraic(expr);

    else assert (false); // unreachable
}

bool Compiler::walk_lshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_lshift_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_lshift_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_algebraic(expr))
        algebraic_lshift(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_rshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_rshift_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_rshift_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_algebraic(expr))
        algebraic_rshift(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_assignment_preorder(const Expr_ptr expr)
{
    ExprMgr& em
        (f_owner.em());

    /* rewrite `x := <expr>` into `NEXT(x) = <expr>` */
    Expr_ptr rewrite
        (em.make_eq( em.make_next(expr->lhs()), expr->rhs()));

    DEBUG
        << "Rewrote `"
        << expr
        << "` into `"
        << rewrite
        << "`"
        << std::endl;

    /* compiling rewritten expression */
    (*this)(rewrite);

    return false;
}
bool Compiler::walk_assignment_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_assignment_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;
}

bool Compiler::walk_eq_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_eq_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_eq_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_boolean(expr))
        boolean_equals(expr);

    else if (is_binary_enumerative(expr))
        enumerative_equals(expr);

    else if (is_binary_algebraic(expr))
        algebraic_equals(expr);

    else if (is_binary_array(expr))
        array_equals(expr);

    else throw UnexpectedExpression(expr);
}

bool Compiler::walk_ne_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_ne_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_ne_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_boolean(expr))
        boolean_not_equals(expr);

    else if (is_binary_enumerative(expr))
        enumerative_not_equals(expr);

    else if (is_binary_algebraic(expr))
        algebraic_not_equals(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_gt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_gt_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_gt_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_algebraic(expr))
        algebraic_gt(expr);

    else assert( false );
}

bool Compiler::walk_ge_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_ge_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_ge_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_algebraic(expr))
        algebraic_ge(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_lt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_lt_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_lt_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_algebraic(expr))
        algebraic_lt(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_le_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_le_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_le_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_binary_algebraic(expr))
        algebraic_le(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_ite_preorder(const Expr_ptr expr)
{
    if (!cache_miss(expr))
        return false;

    if (COMPILING == f_status &&
        is_ite_algebraic( expr -> rhs())) {

        /* perform a lookhead on RHS to collect nested ITEs */
        BinarySelectionUnionFindMap::const_iterator eye
            (f_bsuf_map.find( expr ));

        Expr_ptr parent = expr;
        if (f_bsuf_map.end() != eye)
            parent = eye -> second;

        f_bsuf_map.insert( std::pair< Expr_ptr, Expr_ptr >
                           ( expr->rhs(), parent ));
    }

    return true;
}
bool Compiler::walk_ite_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_ite_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_ite_boolean(expr))
        boolean_ite(expr);

    else if (is_ite_enumerative(expr))
        enumerative_ite(expr);

    else if (is_ite_algebraic(expr))
        algebraic_ite(expr);

    else if (is_ite_array(expr))
        array_ite(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_cond_preorder(const Expr_ptr expr)
{ return true; }
bool Compiler::walk_cond_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_cond_postorder(const Expr_ptr expr)
{}

bool Compiler::walk_dot_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_dot_inorder(const Expr_ptr expr)
{
    ExprMgr& em
        (f_owner.em());

    f_type_stack.pop_back();

    Expr_ptr ctx
        (em.make_dot( f_ctx_stack.back(), expr -> lhs()));
    f_ctx_stack.push_back(ctx);

    return true;
}
void Compiler::walk_dot_postorder(const Expr_ptr expr)
{ f_ctx_stack.pop_back(); }

/* on-demand preprocessing to expand defines delegated to Preprocessor */
bool Compiler::walk_params_preorder(const Expr_ptr expr)
{
    Expr_ptr ctx
        (f_ctx_stack.back());

    (*this)(f_owner.preprocess( expr, ctx));

    return false;
}
bool Compiler::walk_params_inorder(const Expr_ptr expr)
{ assert( false ); return false; /* unreachable */ }
void Compiler::walk_params_postorder(const Expr_ptr expr)
{ assert( false ); return ; /* unreachable */ }

bool Compiler::walk_params_comma_preorder(const Expr_ptr expr)
{ return true; }
bool Compiler::walk_params_comma_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_params_comma_postorder(const Expr_ptr expr)
{ }

bool Compiler::walk_subscript_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Compiler::walk_subscript_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_subscript_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    if (is_subscript_boolean(expr))
        boolean_subscript(expr);

    else if (is_subscript_enumerative(expr))
        enumerative_subscript(expr);

    else if (is_subscript_algebraic(expr))
        algebraic_subscript(expr);

    else assert( false ); // unreachable
}

bool Compiler::walk_array_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Compiler::walk_array_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    TypeMgr& tm
        (TypeMgr::INSTANCE());

    unsigned elems, width;

    POP_TYPE(type);

    if (type -> is_array()) {
        ArrayType_ptr array_type
            (type -> as_array());

        elems = array_type -> nelems();
        width = array_type -> of() -> width();

        PUSH_TYPE(array_type);

        /* Here we fiddle a bit with the ordering of DDs to
           keep consistency with the array equals op. */
        POP_DV(dvs, width * elems);
        for (unsigned i = 0; i < elems; ++ i) {
            for (unsigned j = 0; j < width; ++ j) {
                PUSH_DD(dvs[i * width + width - j - 1]);
            }
        }
    }
    else if (type -> is_scalar()) {
        ScalarType_ptr scalar_type
            (type -> as_scalar());
        ArrayType_ptr array_type
            (tm.find_array_type(scalar_type, 1));
        PUSH_TYPE(array_type);
        return; /* no need to do anything */
    }
    else assert(false); // unreachable
}

bool Compiler::walk_array_comma_preorder(const Expr_ptr expr)
{ return true; }
bool Compiler::walk_array_comma_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_array_comma_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    TypeMgr& tm
        (TypeMgr::INSTANCE());

    POP_TYPE(rhs_type);
    POP_TYPE(lhs_type);

    ArrayType_ptr array_type
        (NULL);

    if (rhs_type -> is_array()) {
        array_type = rhs_type -> as_array();
        ScalarType_ptr of_type
            (array_type -> of());

        // not necessarily the same type, but compatible
        assert( lhs_type -> width() == of_type -> width());

        ArrayType_ptr new_array_type
            (tm.find_array_type( of_type, 1 + array_type -> nelems()));

        PUSH_TYPE(new_array_type);
        return;
    }

    if (rhs_type -> is_scalar()) {
        ScalarType_ptr of_type
            (rhs_type -> as_scalar());

        // not necessarily the same type, but compatible
        assert( lhs_type -> width() == of_type -> width());

        array_type = tm.find_array_type(of_type, 2);
        PUSH_TYPE(array_type);
    }
}

/* non-deterministic expressions are not cachable */
bool Compiler::walk_set_preorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_set_postorder(const Expr_ptr expr)
{}

/* non-deterministic expression are not cachable */
bool Compiler::walk_set_comma_preorder(const Expr_ptr expr)
{ return true; }
bool Compiler::walk_set_comma_inorder(const Expr_ptr expr)
{ return true; }
void Compiler::walk_set_comma_postorder(const Expr_ptr expr)
{
    if (ENCODING == f_status)
        return;

    TypeMgr& tm
        (TypeMgr::INSTANCE());

    POP_TYPE(rhs_type);
    POP_TYPE(lhs_type);
    assert(rhs_type -> width() == lhs_type -> width());

    if (rhs_type -> is_monolithic()) {

        POP_DD(rhs);
        POP_DD(lhs);

        // anonymous determinization variable
        FRESH_DD(det);
        PUSH_DD(det);

        PUSH_DD(lhs);
        PUSH_DD(rhs);

        PUSH_TYPE( tm.find_boolean());
        PUSH_TYPE( lhs_type );
        PUSH_TYPE( rhs_type );

        if (rhs_type -> is_boolean())
            boolean_ite(expr);
        else if (rhs_type -> is_enum())
            enumerative_ite(expr);
        else assert(false);
    }

    else if (rhs_type -> is_algebraic()) {

        unsigned width
            (rhs_type -> width());

        POP_DV( rhs, width );
        POP_DV( lhs, width );

        // anonymous determinization variable
        FRESH_DD(det);
        PUSH_DD(det);

        PUSH_DV(lhs, width);
        PUSH_DV(rhs, width);

        PUSH_TYPE( tm.find_boolean());
        PUSH_TYPE( lhs_type );
        PUSH_TYPE( rhs_type );

        algebraic_ite(expr);
    }

    else assert(false);
}
