/**
 *  @file internals.cc
 *  @brief Boolean compiler - internal services
 *
 *  This module contains definitions and services that implement the
 *  booolean expressions compilation into a form which is suitable for
 *  the SAT analysis. Current implementation uses ADDs to perform
 *  expression manipulation and booleanization. Expressions are
 *  assumed to be type-safe, only boolean expressions on arithmetic
 *  predicates are supported. The final result of expression
 *  compilation must be a 0-1 ADD which is suitable for CNF clauses
 *  injection directly into the SAT solver. The compilation engine is
 *  implemented using a simple walker pattern: (a) on preorder, return
 *  true if the node has not yet been visited; (b) always do in-order
 *  (for binary nodes); (c) perform proper compilation in post-order
 *  hooks.
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
#include <common.hh>

#include <expr.hh>
#include <compiler.hh>

/* Helpers */
#define FETCH_DDS(store, count)                                   \
    for (unsigned i = 0; i < (count); ++ i) {                     \
        (store)[i] = f_add_stack.back();                          \
        f_add_stack.pop_back();                                   \
    }

#define PUSH_DDS(store, count)                                    \
    for (unsigned i = 0; i < (count); ++ i) {                     \
        unsigned ndx = (count) - i - 1;                           \
        f_add_stack.push_back((store) [ndx]);                     \
    }

#define ALGEBRIZE_RHS(sz)                       \
    do {                                        \
        algebraic_from_constant((sz));          \
    } while (0)

#define ALGEBRIZE_LHS(sz)                       \
    do {                                        \
        ADD tmp[(sz)];                          \
        FETCH_DDS(tmp, (sz));                   \
        algebraic_from_constant((sz));          \
        PUSH_DDS(tmp, (sz));                    \
    } while (0)

static inline bool _iff(bool a, bool b)
{ return (!(a) || (b)) && (!(b) || (a)); }

// algebrization primitive
void Compiler::algebraic_from_constant(unsigned width)
{
    POP_ADD(add);
    assert (f_enc.is_constant(add));

    value_t value = f_enc.const_value(add);
    unsigned base = Cudd_V(f_enc.base().getNode());
    if (value < 0) {
        value += pow(base, width); // 2's complement
    }
    for (unsigned i = 0; i < width; ++ i) {
        ADD digit = f_enc.constant(value % base);
        f_add_stack.push_back(digit);
        value /= base;
    }

    assert (value == 0); // not overflowing
}

/* ITE is not a proper const manipulation as it *always* is a function
   of the condition. The result of an ITE is an algebraic. The size of
   the expression poses a bit of a problem. After some thought I
   realized a way to determine the necessary number of bits relying on
   an extra stack and some recursion magic on the innermost relational
   operator. This leaves the case when both operands of the relational
   are abstract. This can be sorted out by means of rewriting, but as it
   is not probably worth the effort, as of now it is unsupported. */
void Compiler::integer_ite(const Expr_ptr expr)
{
    assert(0 < f_rel_type_stack.size());
    Type_ptr type = f_rel_type_stack.back();
    unsigned width = type -> width();

    // reverse order
    ALGEBRIZE_LHS(width);
    ALGEBRIZE_RHS(width);

    /* fix type stack, constants are always unsigned */
    f_type_stack.pop_back();
    f_type_stack.pop_back();
    f_type_stack.push_back( type );
    f_type_stack.push_back( type );

    /* we can now re-use general case algorithm for algebraic ITEs */
    algebraic_ite(expr);
}

/* For relationals we need to do some work. Namely, we look-ahead lhs
   and rhs types using the inferrer, to determine the expected
   type. This is used to settle the ITE(const, const) algebrization
   uncertainty. This comment applies to all relational operators. */
void Compiler::relational_type_lookahead(const Expr_ptr expr)
{
    Expr_ptr ctx (f_ctx_stack.back());
    Type_ptr rhs_type = f_owner.type( expr->rhs(), ctx);
    Type_ptr lhs_type = f_owner.type( expr->lhs(), ctx);

    if (! lhs_type -> is_constant() &&
        ! rhs_type -> is_constant()) {
        assert( lhs_type == rhs_type ); // FIXME: throw
        f_rel_type_stack.push_back( rhs_type );
    }

    else if ( lhs_type -> is_constant() &&
              ! rhs_type -> is_constant()) {
        f_rel_type_stack.push_back( rhs_type );
    }

    else if ( rhs_type -> is_constant() &&
              ! lhs_type -> is_constant()) {
        f_rel_type_stack.push_back( lhs_type );
    }

    /* Uh Oh, both are constants. There is no easy way out of this for now. */
    else {
        assert( false ); // unsupported;
    }
}

void Compiler::relational_type_cleanup()
{
    assert(0 < f_rel_type_stack.size());
    f_rel_type_stack.pop_back();
}

unsigned Compiler::algebrize_operation(bool ternary, bool relational)
{
    unsigned res = 0;
    unsigned stack_size = f_type_stack.size();
    assert ((ternary ? 3 : 2) <= stack_size);
    TypeMgr& tm = f_owner.tm();

    const Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();
    const Type_ptr lhs_type = f_type_stack.back(); f_type_stack.pop_back();
    if (ternary)
        f_type_stack.pop_back(); /* ITEs require an extra pop() */

    // both algebraic, not both consts
    assert( rhs_type -> is_algebraic() &&
            lhs_type -> is_algebraic() &&
            !( rhs_type -> is_constant() &&
               lhs_type -> is_constant()));

    if (rhs_type -> is_constant()  ||
        lhs_type -> is_constant()) {

        if (lhs_type -> is_constant()) {
            res = rhs_type -> width();
            ALGEBRIZE_LHS(res);
            f_type_stack.push_back( (!relational) ? rhs_type : tm.find_boolean());
        }
        else if (rhs_type -> is_constant()) {
            res = lhs_type -> width();
            ALGEBRIZE_RHS(res);
            f_type_stack.push_back( (!relational) ? lhs_type : tm.find_boolean());
        }
        else assert(0);
    }
    else {
        // neither const -> size and signedness must match
        assert( lhs_type -> width() ==
                rhs_type -> width() &&

                _iff( lhs_type -> is_signed_algebraic(),
                      rhs_type -> is_signed_algebraic()));


        // Nothing do be done, just add result type to the type stack
        res = rhs_type -> width();
        f_type_stack.push_back( (!relational) ? rhs_type : tm.find_boolean()); // arbitrary
    }

    // sanity check
    assert( stack_size - (ternary ? 2 : 1) == f_type_stack.size());
    return res;
}

/* Discards an operand (and corresponding type). This is needed for
   rewrites. */
void Compiler::algebraic_discard_op()
{
    const Type_ptr type = f_type_stack.back(); f_type_stack.pop_back();
    unsigned width = type -> width();

    /* discard DDs */
    for (unsigned i = 0; i < width; ++ i) {
        f_add_stack.pop_back();
    }
}

/* Builds a temporary encoding. This is used by some algebraic
   algorithms (e.g. neg, algebraic-to-bool cast, ...) */
Expr_ptr Compiler::make_temporary_encoding(ADD dds[], unsigned width)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    ostringstream oss;
    oss << "__tmp" << f_temp_auto_index ++ ;

    Expr_ptr expr = em.make_identifier(oss.str());

    /* Register temporary symbol into resolver (temporaries are global) */
    f_owner.resolver()->add_symbol(em.make_temp(), expr,
                                   new Temporary(expr,
                                                 tm.find_unsigned( width )));

    /* register encoding, using fqexpr */
    const FQExpr& key = FQExpr(expr);
    f_temp_encodings [ key ] = new AlgebraicEncoding(width, false, dds);

    return expr;
}

/* Builds a temporary boolean encoding. This is used by Pass 3 */
BooleanEncoding_ptr Compiler::make_chain_encoding()
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    ostringstream oss;
    oss << "__ac" << f_temp_auto_index ++ ;

    Expr_ptr expr = em.make_identifier(oss.str());

    /* register encoding, using fqexpr */
    BooleanEncoding_ptr be = reinterpret_cast<BooleanEncoding_ptr>
        (f_enc.make_encoding( tm.find_boolean()));

    const FQExpr& key = FQExpr(expr);
    f_enc.register_encoding(key, be);

    return be;
}


void Compiler::pre_node_hook(Expr_ptr expr)
{
    /* assemble memoization key */
    assert( 0 < f_ctx_stack.size() );
    Expr_ptr ctx = f_ctx_stack.back();

    assert( 0 < f_time_stack.size() );
    step_t time = f_time_stack.back();

    FQExpr key(ctx, expr, time);

    TRACE << "Processing " << key << "..." << endl;
    f_ticks = clock();
}

void Compiler::post_node_hook(Expr_ptr expr)
{
    if (f_first || f_owner.em().is_type(expr)) {
        return;
    }

    /* assemble memoization key */
    assert( 0 < f_ctx_stack.size() );
    Expr_ptr ctx = f_ctx_stack.back();

    assert( 0 < f_time_stack.size() );
    step_t time = f_time_stack.back();

    FQExpr key(ctx, expr, time);

    assert( 0 < f_type_stack.size() );
    Type_ptr type = f_type_stack.back();

    /* collect dds and memoize */
    DDVector dv;
    unsigned i, width = type -> width();
    assert(width <= f_add_stack.size());

    ADDStack::reverse_iterator ri;
    for (i = 0, ri = f_add_stack.rbegin();
         i < width; ++ i, ++ ri) {
        dv.push_back(*ri);
    }
    assert (dv.size() == width);
    f_map.insert( make_pair <FQExpr,
                  DDVector> ( key, dv ));

    double elapsed = (double) (clock() - f_ticks) / CLOCKS_PER_SEC;
    unsigned nodes = f_enc.dd().SharingSize(dv);
    TRACE
        << key << " took " << elapsed << "s, "
        << nodes << " ADD nodes"
        << endl;
}

#if 0

void Compiler::debug_hook()
{
    activation_record curr = f_recursion_stack.top();
    DEBUG << "compiler debug hook, expr = " << curr.expr << endl;

    DEBUG << "DD Stack" << endl;
    for (ADDStack::reverse_iterator i = f_add_stack.rbegin();
         i != f_add_stack.rend(); ++ i) {
        DdNode* node = (*i).getNode();
        double paths = (*i).CountPath();
        DEBUG << "DD: " << node
              << " [" << paths << "]" << endl;
    }

    DEBUG << "Type Stack" << endl;
    for (TypeStack::reverse_iterator i = f_type_stack.rbegin();
         i != f_type_stack.rend(); ++ i) {
        DEBUG << *i << endl;
    }
    DEBUG << "--------------------" << endl;
}
#endif

/* two operands, both booleans */
bool Compiler::is_binary_boolean(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /* AND, OR, XOR, XNOR, IFF, IMPLIES */
    if (em.is_binary_logical(expr)) {
        return (f_owner.type(expr->lhs(), ctx) -> is_boolean() &&
                f_owner.type(expr->rhs(), ctx) -> is_boolean());
    }

    return false;
}

/* one operand, boolean */
bool Compiler::is_unary_boolean(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /*  NOT, () ? */
    if (em.is_unary_logical(expr)) {
        return f_owner.type(expr->lhs(), ctx) -> is_boolean();
    }

    return false;
}

/* two operands both int consts */
bool Compiler::is_binary_integer(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /* AND (bw), OR(bw), XOR(bw), XNOR(bw), IFF(bw),
       IMPLIES(bw), LT, LE, GT, GE, EQ, NE, PLUS, SUB, DIV, MUL, MOD */
    if ((em.is_binary_logical(expr)) ||
        (em.is_binary_arithmetical(expr)) ||
        (em.is_binary_relational(expr))) {

        return (f_owner.type(expr->lhs(), ctx) -> is_constant() &&
                f_owner.type(expr->rhs(), ctx) -> is_constant());
    }

    return false;
}

/* one operand, int const */
bool Compiler::is_unary_integer(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();

    /* unary : ? (), : (), NEG, NOT(bw) */
    if (em.is_unary_arithmetical(expr)) {
        Type_ptr tp = f_type_stack.back();
        return tp->is_constant();
    }

    return false;
}

/* two operands, both enumeratives */
bool Compiler::is_binary_enumerative(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /* AND (bw), OR(bw), XOR(bw), XNOR(bw), IFF(bw),
       IMPLIES(bw), LT, LE, GT, GE, EQ, NE, PLUS, SUB, DIV, MUL, MOD */
    if ((em.is_binary_arithmetical(expr)) ||
        (em.is_binary_relational(expr))) {

        return (f_owner.type(expr->lhs(), ctx) -> is_enum() &&
                f_owner.type(expr->rhs(), ctx) -> is_enum() );
    }

    return false;
}

/* one operand, enumerative */
bool Compiler::is_unary_enumerative(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /* unary : ? (), : (), NEG, NOT(bw) */
    if (em.is_unary_arithmetical(expr)) {
        return (f_owner.type(expr->lhs(), ctx) -> is_enum());
    }

    return false;
}

/* two operands, both algebraics, at least one non-abstract */
bool Compiler::is_binary_algebraic(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    if ((em.is_binary_logical(expr)) ||
        (em.is_binary_arithmetical(expr)) ||
        (em.is_binary_relational(expr))) {

        return
            f_owner.type(expr->rhs(), ctx) -> is_algebraic() &&
            f_owner.type(expr->lhs(), ctx) -> is_algebraic();
    }

    return false;
}

/* checks lhs is array, and rhs is algebraic */
bool Compiler::is_subscript_algebraic(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /* SUBSCRIPT */
    if (em.is_subscript(expr)) {

        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());
        return (f_owner.type(expr->lhs(), ctx) -> is_array() &&
                f_owner.type(expr->rhs(), ctx) -> is_algebraic()) ;
    }

    return false;
}

/* one operand, algebraic */
bool Compiler::is_unary_algebraic(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    if ((em.is_unary_logical(expr)) ||
        (em.is_unary_arithmetical(expr))) {

        return f_owner.type(expr->lhs(), ctx) -> is_algebraic();
    }

    return false;
}

/* same as is_binary_boolean, checks only lhs and rhs */
bool Compiler::is_ite_boolean(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /* ITE */
    if (em.is_ite(expr)) {
        return (f_owner.type(expr->lhs(), ctx) -> is_boolean() &&
                f_owner.type(expr->rhs(), ctx) -> is_boolean()) ;
    }

    return false;
}

/* same as is_binary_integer, checks only lhs and rhs */
bool Compiler::is_ite_integer(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /* ITE (bw) */
    if (em.is_ite(expr)) {
        return (f_owner.type(expr->lhs(), ctx) -> is_constant() &&
                f_owner.type(expr->rhs(), ctx) -> is_constant()) ;
    }

    return false;
}

/* checks lhs is array, and rhs is integer */
bool Compiler::is_subscript_integer(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /* SUBSCRIPT */
    if (em.is_subscript(expr)) {
        return (f_owner.type(expr->lhs(), ctx) -> is_array() &&
                f_owner.type(expr->rhs(), ctx) -> is_constant()) ;
    }

    return false;
}


/* same as  is_binary_enumerative, checks only lhs and rhs */
bool Compiler::is_ite_enumerative(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    /* ITE (bw) */
    if (em.is_ite(expr)) {

        return (f_owner.type(expr->lhs(), ctx) -> is_enum() &&
                f_owner.type(expr->rhs(), ctx) -> is_enum()) ;
    }

    return false;

}

/* similar to is_binary_algebraic, checks only lhs and rhs */
bool Compiler::is_ite_algebraic(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    Expr_ptr ctx (f_ctx_stack.back());

    if (em.is_ite(expr)) {

        return
            f_owner.type(expr-> rhs(), ctx) -> is_algebraic() &&
            f_owner.type(expr-> lhs(), ctx) -> is_algebraic();
    }

    return false;
}

bool Compiler::cache_miss(const Expr_ptr expr)
{
    Expr_ptr ctx (f_ctx_stack.back());

    FQExpr key(f_ctx_stack.back(), expr, f_time_stack.back());
    ADDMap::iterator eye = f_map.find(key);

    if (eye != f_map.end()) {
        const Type_ptr type = f_owner.type(expr, ctx);
        TRACE << "Cache hit for " << expr
              << ", type is " << type
              << endl;

        /* push cached DDs and type */
        DDVector::reverse_iterator ri;
        for (ri = (*eye).second.rbegin();
             ri != (*eye).second.rend(); ++ ri ) {
            f_add_stack.push_back(*ri);
        }
        f_type_stack.push_back(type);

        /* cache hit */
        return false;
    }

    /* cache miss */
    return true;
}

ADD Compiler::book_and_chain(ADD* dds, unsigned len)
{
    BooleanEncoding_ptr be
        = make_chain_encoding();

    /* add alpha variable */
    ADD ret = be -> bits() [0];

    /* collect dds */
    DDVector dv;
    for (unsigned i = 0; i < len; ++ i) {
        dv.push_back( dds[i]);
    }

    /* saving (1) alias: alpha -> dds and (2) chain root */
    f_chains.insert( make_pair <ADD, DDVector> ( ret, dv ));
    f_roots.push_back( ret );

    return ret;
}

void Compiler::finalize_and_chains()
{
    // Conjunct booked AND chains into result stack
    for (DDVector::iterator i = f_roots.begin(); f_roots.end() != i; ++ i) {
        ADD alpha (*i); ADD not_alpha = alpha.Cmpl();

        ACMap::iterator eye = f_chains.find(alpha);
        assert( f_chains.end() != eye);

        DDVector& Y ((*eye).second);
        for (DDVector::iterator j = Y.begin(); Y.end() != j; ++ j) {
            // a -> Y, that is: (!a v Y1) ^ (!a v Y2) ^ (!a v Y3) ^ ...
            PUSH_ADD (not_alpha.Or(*j));
        }

        // !a -> !Y, that is: (a v !Y1 v !Y2 v !Y3 v ....)
        ADD bigOr = f_enc.zero();
        for (DDVector::iterator j = Y.begin(); Y.end() != j; ++ j) {
            BooleanEncoding_ptr be
                = make_chain_encoding();

            ADD  av = be -> bits() [0];
            bigOr = bigOr.Or( av);

            PUSH_ADD( av.Cmpl(). Or( (*j). Cmpl()). Or( alpha));
        }
        PUSH_ADD(bigOr);
    }
}
