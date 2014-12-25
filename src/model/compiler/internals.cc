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

void Compiler::algebrize_operation(bool ternary, bool relational, unsigned& width, bool& signedness)
{
    width = 0;
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
            width = rhs_type -> width();
            ALGEBRIZE_LHS(width);
            f_type_stack.push_back( (!relational) ? rhs_type : tm.find_boolean());
        }
        else if (rhs_type -> is_constant()) {
            width = lhs_type -> width();
            ALGEBRIZE_RHS(width);
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
        width = rhs_type -> width();
        f_type_stack.push_back( (!relational) ? rhs_type : tm.find_boolean()); // arbitrary
    }

    signedness = rhs_type -> is_signed_algebraic();

    // sanity check
    assert(0 < width && (stack_size - (ternary ? 2 : 1) == f_type_stack.size()));
}

void Compiler::register_microdescriptor( bool signedness, ExprType symb, unsigned width,
                                         DDVector& z, DDVector& x, DDVector &y )
{
    MicroDescriptor md( make_op_triple( signedness, symb, width ), z, x, y);
    f_descriptors.push_back(md);
    DEBUG << "Registered " << md << endl;
}

/* auto id generator */
Expr_ptr Compiler::make_auto_id()
{
    ExprMgr& em = f_owner.em();
    ostringstream oss;
    oss << "__tmp" << f_temp_auto_index ++ ;
    return em.make_identifier(oss.str());
}

/* Builds a temporary expression out of a DD array. This is used by
   some algebraic algorithms. Uses arrays instead of DDVectors due to
   historic reasons. */
Expr_ptr Compiler::make_temporary_expr(ADD dds[], unsigned width)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    Expr_ptr expr(make_auto_id());

    /* Register temporary symbol into resolver (temporaries are global) */
    f_owner.resolver()->add_symbol(em.make_temp(), expr,
                                   new Temporary(expr,
                                                 tm.find_unsigned( width )));

    /* register encoding, using fqexpr */
    const FQExpr& key = FQExpr(expr);
    f_temp_encodings [ key ] = new AlgebraicEncoding(width, false, dds);

    return expr;
}

/* build an auto fresh ADD variable and register its encoding */
ADD Compiler::make_auto_dd()
{
    TypeMgr& tm = f_owner.tm();
    Type_ptr boolean(tm.find_boolean());

    BooleanEncoding_ptr be = reinterpret_cast<BooleanEncoding_ptr>
        (f_enc.make_encoding( boolean ));

    // register encoding, a FQExpr is needed for UCBI booking
    Expr_ptr aid = make_auto_id();
    Expr_ptr ctx = f_ctx_stack.back();
    step_t time = f_time_stack.back();
    FQExpr key (ctx, aid, time);
    f_enc.register_encoding( key, be);

    return be -> bits() [0];
}

/* build an auto DD vector of fresh ADD variables. */
void Compiler::make_auto_ddvect(DDVector& dv, unsigned width)
{
    assert(0 == dv.size());
    for (unsigned i = 0; i < width; ++ i ) {
        dv.push_back(make_auto_dd());
    }
}

void Compiler::pre_node_hook(Expr_ptr expr)
{
    /* assemble memoization key */
    assert( 0 < f_ctx_stack.size() );
    Expr_ptr ctx = f_ctx_stack.back();

    assert( 0 < f_time_stack.size() );
    step_t time = f_time_stack.back();

    FQExpr key(ctx, expr, time);

    DRIVEL << "Processing " << key << "..." << endl;
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
                  pair<DDVector, MicroDescriptors> > ( key,
                                                       make_pair<DDVector, MicroDescriptors> (dv,
                                                                                              f_descriptors) ));

    double elapsed = (double) (clock() - f_ticks) / CLOCKS_PER_SEC;
    unsigned nodes = f_enc.dd().SharingSize(dv);

    DEBUG
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

// -- semantic analysis predicates ---------------------------------------------

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
        DEBUG << "Cache hit for " << expr
              << ", type is " << type
              << endl;

        /* push cached DDs */
        DDVector::reverse_iterator ri;
        for (ri = (*eye).second.first.rbegin();
             ri != (*eye).second.first.rend(); ++ ri ) {
            f_add_stack.push_back(*ri);
        }

        /* push cached type */
        f_type_stack.push_back(type);

        /* push cached microcode */
        MicroDescriptors::iterator mdi;
        for (mdi = (*eye).second.second.begin();
             mdi != (*eye).second.second.end(); ++ mdi) {
            f_descriptors.push_back(*mdi);
        }

        /* cache hit */
        return false;
    }

    /* cache miss */
    return true;
}

void Compiler::clear_internals()
{
    f_add_stack.clear();
    f_type_stack.clear();
    f_rel_type_stack.clear();
    f_ctx_stack.clear();
    f_time_stack.clear();
    f_descriptors.clear();
}
