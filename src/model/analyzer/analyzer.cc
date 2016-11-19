/**
 * @file analyzer.cc
 * @brief Semantic analyzer module
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

#include <common.hh>

#include <expr/expr.hh>
#include <type/type.hh>
#include <symb/proxy.hh>

#include <model/analyzer/analyzer.hh>

Analyzer::Analyzer(ModelMgr& owner)
    : f_ctx_stack()
    , f_owner(owner)
{
    const void *instance
        (this);

    DRIVEL
        << "Created Analyzer @"
        << instance
        << std::endl;
}

Analyzer::~Analyzer()
{
    const void *instance
        (this);

    DRIVEL
        << "Destroying Analyzer @"
        << instance
        << std::endl;
}

void Analyzer::process(Expr_ptr expr, Expr_ptr ctx, analyze_section_t section)
{
    assert(section == ANALYZE_INIT  ||
           section == ANALYZE_INVAR ||
           section == ANALYZE_TRANS ||
           section == ANALYZE_DEFINE);

    // this needs to be set only once
    f_section = section;

    // remove previous results
    f_expr_stack.clear();
    f_ctx_stack.clear();

    // walk body in given ctx
    f_ctx_stack.push_back(ctx);

    // invoke walker on the body of the expr to be processed
    (*this)(expr);
    assert(! f_expr_stack.size());
}

void Analyzer::generate_framing_conditions()
{
    DEBUG
        << "Generating frame conditions ..."
        << std::endl ;

    /* identifer -> list of guards */
    typedef boost::unordered_map<Expr_ptr, ExprVector, PtrHash, PtrEq> ProcessingMap;

    ExprMgr& em
        (owner().em());

    ProcessingMap map;

    /* pass 1: build a scheleton map */
    for (DependencyTrackingMap::const_iterator i = f_dependency_tracking_map.begin();
         i != f_dependency_tracking_map.end(); ++ i) {

        Expr_ptr ident
            (i->second);

        ProcessingMap::const_iterator pmi
            (map.find(ident));

        if (map.end() == pmi)
            map.insert(std::make_pair<Expr_ptr, ExprVector>
                       (ident, ExprVector()));
    }

    /* pass 2: group together all guards associated with each var identifier */
    for (DependencyTrackingMap::const_iterator i = f_dependency_tracking_map.begin();
         i != f_dependency_tracking_map.end(); ++ i) {

        Expr_ptr guard
            (i->first);

        Expr_ptr ident
            (i->second);

        ProcessingMap::iterator pmi
            (map.find(ident));

        /* right? */
        assert(map.end() != pmi);

        ExprVector& ev
            (pmi->second);

        ev.push_back(guard);
    }

    /* pass 3: for each group of clauses, for each pair <p, q>, p and q must be
       mutually exclusive (i.e. `p ^ q` must be UNSAT). */
    for (ProcessingMap::iterator i = map.begin();
         i != map.end(); ++ i) {

        Expr_ptr ident
            (i->first);

        const ExprVector& ev
            (i->second);

        unsigned input_length
            (ev.size());

        if (2 <= input_length) {
            for (unsigned i = 0; i < input_length - 1; ++ i) {
                Expr_ptr p
                    (ev[i]);

                for (unsigned j = i + 1; j < input_length; ++ j) {
                    Expr_ptr q
                        (ev[j]);

                    if (! mutually_exclusive(p, q)) {
                        std::ostringstream oss;

                        oss
                            << "Found two guards that are NOT mutually exclusive for identifier `"
                            << ident
                            << "`:"
                            << std::endl
                            << p
                            << std::endl
                            << q
                            << std::endl;

                        const char *tmp
                            (oss.str().c_str());

                        WARN
                            << tmp;
                    }
                }
            }
        }
    }

    /* pass 4: for each expr vector, build the conjunction of all (mutually
       exclusive) negated guards and associate it to the variable identifier.
       The resulting expr will be used as guard for a newly generated TRANS of
       the form: <guard> -> <var> := var. */
    Module& main
        (owner().model().main_module());

    for (ProcessingMap::iterator i = map.begin();
         i != map.end(); ++ i) {

        Expr_ptr ident
            (i->first);

        ExprVector& ev
            (i->second);

        Expr_ptr guard
            (NULL);

        for (ExprVector::const_iterator j = ev.begin();
             j != ev.end(); ++ j) {

            Expr_ptr expr
                (*j);

            guard = (guard)
                ? em.make_and(guard, em.make_not(expr))
                : em.make_not(expr)
                ;
        }

        /* Add this synthetic TRANS will be added to the `synthetic` module. */
        main.add_trans(em.make_implies(guard,
                                       em.make_eq(em.make_next(ident),
                                                  ident)));
    }
}

bool Analyzer::mutually_exclusive(Expr_ptr p, Expr_ptr q) const
{
    return true;
}

bool Analyzer::walk_F_preorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_F_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_G_preorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_G_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_X_preorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_X_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_U_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_U_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_U_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_R_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_R_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_R_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_next_preorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_next_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_neg_preorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_neg_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_not_preorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_not_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_bw_not_preorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_bw_not_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_add_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_add_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_add_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_sub_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_sub_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_sub_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_div_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_div_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_div_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_mul_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_mul_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_mul_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_mod_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_mod_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_mod_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_and_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_and_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_bw_and_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_bw_and_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_bw_and_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_or_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_or_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_bw_or_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_bw_or_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_bw_or_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_bw_xor_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_bw_xor_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_bw_xor_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_bw_xnor_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_bw_xnor_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_bw_xnor_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_guard_preorder(const Expr_ptr expr)
{
    ExprMgr& em
        (owner().em());

    if (f_section == ANALYZE_INIT)
        throw SemanticException("Guards not allowed in INITs");

    if (f_section == ANALYZE_INVAR)
        throw SemanticException("Guards not allowed in INVARs");

    if (f_section == ANALYZE_DEFINE)
        throw SemanticException("Guards not allowed in DEFINEs");

    /* now we know it's a TRANS */
    if (1 != f_expr_stack.size())
        throw SemanticException("Guards are only allowed toplevel in TRANSes");

    Expr_ptr guard
        (expr->lhs());

    Expr_ptr action
        (expr->rhs());

    if (! em.is_assignment(action))
        throw SemanticException("Guarded actions must be assignments");

    Expr_ptr ident
        (action->lhs());

    DEBUG
        << "Tracking dependency: "
        << ident
        << " -> "
        << guard
        << std::endl;

    f_dependency_tracking_map.insert(std::make_pair<Expr_ptr, Expr_ptr>
                     (guard, ident));

    return true;
}

bool Analyzer::walk_guard_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_guard_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_implies_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_implies_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_cast_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_cast_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_cast_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_type_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_type_inorder(const Expr_ptr expr)
{ assert(false); /* unreachable */ return false; }
void Analyzer::walk_type_postorder(const Expr_ptr expr)
{ assert(false); /* unreachable */ }

bool Analyzer::walk_lshift_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_lshift_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_lshift_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_rshift_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_rshift_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_rshift_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_assignment_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_assignment_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_assignment_postorder(const Expr_ptr expr)
{
    if (f_section == ANALYZE_INIT)
        throw SemanticException("Assignments not allowed in INITs");

    if (f_section == ANALYZE_INVAR)
        throw SemanticException("Assignments not allowed in INVARs");

    if (f_section == ANALYZE_DEFINE)
        throw SemanticException("Assignments not allowed in DEFINEs");

    ExprMgr& em
        (owner().em());

    Expr_ptr ident
        (expr->lhs());

    if (! em.is_identifier(ident))
        throw SemanticException("Assignments require an identifier for lhs");

    /* assignment lhs *must* be an ordinary state variable */
    Expr_ptr ctx
        (f_ctx_stack.back());
    Expr_ptr full
        (em.make_dot(ctx, ident));

    ResolverProxy resolver;

    Symbol_ptr symb
        (resolver.symbol(full));

    if (symb->is_variable()) {

        const Variable& var
            (symb -> as_variable());

        /* INPUT vars are in fact bodyless, typed DEFINEs */
        if (var.is_input())
            throw SemanticException("Assignments not allowed on input vars.");

        /* FROZEN vars can not be assigned */
        if (var.is_frozen())
            throw SemanticException("Assignments can not be used on frozen vars.");
    }

    /* 6. DEFINEs, simply process them recursively :-) */
    else if (symb->is_define()) {

      Define& define
        (symb -> as_define());

      Expr_ptr body
        (define.body());

      /* recur in body */
      walk_assignment_postorder(body);
    }
}

bool Analyzer::walk_eq_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_eq_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_eq_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_ne_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_ne_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_ne_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_gt_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_gt_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_gt_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_ge_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_ge_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_ge_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_lt_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_lt_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_lt_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_le_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_le_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_le_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_ite_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_ite_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_ite_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_cond_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_cond_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_cond_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_dot_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_dot_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_dot_postorder(const Expr_ptr expr)
{}

/* on-demand preprocessing to expand defines delegated to Preprocessor */
bool Analyzer::walk_params_preorder(const Expr_ptr expr)
{
    Expr_ptr ctx
        (f_ctx_stack.back());

    (*this)(f_owner.preprocess(expr, ctx));

    return false;
}
bool Analyzer::walk_params_inorder(const Expr_ptr expr)
{ assert( false ); return false; /* unreachable */ }
void Analyzer::walk_params_postorder(const Expr_ptr expr)
{ assert( false ); return ; /* unreachable */ }

bool Analyzer::walk_params_comma_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_params_comma_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_params_comma_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_subscript_preorder(const Expr_ptr expr)
{ return true; }
bool Analyzer::walk_subscript_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_subscript_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_array_preorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_array_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_array_comma_preorder(Expr_ptr expr)
{ return true; }

bool Analyzer::walk_array_comma_inorder(Expr_ptr expr)
{ return true; }

void Analyzer::walk_array_comma_postorder(Expr_ptr expr)
{}

bool Analyzer::walk_set_preorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_set_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_set_comma_preorder(Expr_ptr expr)
{ return true; }

bool Analyzer::walk_set_comma_inorder(Expr_ptr expr)
{ return true; }

void Analyzer::walk_set_comma_postorder(Expr_ptr expr)
{}

void Analyzer::walk_leaf(const Expr_ptr expr)
{}
