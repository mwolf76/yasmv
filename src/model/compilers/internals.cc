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

// REMARK: algebrizations makes sense only for binary ops, there is no
// need to algebrize a single operand! (unless casts are introduced,
// but then again a CAST can be thought as a binary op...[ CAST 8 x ])

/* This is slightly complex: it fetches two operands (and
   corresponding types), one of them must be algebraic, possibly
   both. Performs integer to algebraic conversion if needed, aligns
   algebraic operands to the largest size, and return this size,
   leaving type stack in a consistent state.

   Remark: if is_ite is true, an extra type is removed from the type
   stack.  */
unsigned Compiler::algebrize_operands(bool is_ite)
{
    TypeMgr& tm = f_owner.tm();

    unsigned stack_size = f_type_stack.size();
    assert (2 <= stack_size);

    const Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();
    // DRIVEL << "RHS is " << rhs_type << endl;

    const Type_ptr lhs_type = f_type_stack.back(); f_type_stack.pop_back();
    // DRIVEL << "LHS is " << lhs_type << endl;

    // HACK: only for ITEs
    if (is_ite) {
        f_type_stack.pop_back();
    }

    assert( tm.is_algebraic(rhs_type) || tm.is_algebraic(lhs_type) );
    unsigned rhs_width = tm.is_algebraic(rhs_type)
        ? tm.as_algebraic(rhs_type)->width()
        : 0;

    unsigned lhs_width = tm.is_algebraic(lhs_type)
        ? tm.as_algebraic(lhs_type)->width()
        : 0;

    /* max */
    unsigned res = rhs_width < lhs_width
        ? lhs_width
        : rhs_width
        ;

    // Nothing do be done, just ad result type to the type stack and leave
    if ((rhs_width == res) && (lhs_width == res)) {
        // DRIVEL << "Nothing do be done." << endl;
        f_type_stack.push_back(rhs_type); // arbitrary

        assert( stack_size - ( is_ite ? 2 : 1 ) == f_type_stack.size());
        return res;
    }

    /* perform conversion or padding, taking sign bit into account */
    if (rhs_width < res) {
        if (! rhs_width) { // integer, conversion required
            // DRIVEL << "INT -> ALGEBRAIC RHS" << endl;
            algebraic_from_integer_const(res);
        }
        else { // just padding required
            bool is_signed = tm.as_algebraic(rhs_type)->is_signed();
            algebraic_padding(rhs_width, res, is_signed);
        }

        // push other operand's type and return
        f_type_stack.push_back(lhs_type);

        assert( stack_size - ( is_ite ? 2 : 1 ) == f_type_stack.size());
        return res;
    }

    if (lhs_width < res) {
        /* temporary storage to let adjustment for LHS to take place */
        ADD rhs_tmp[res];
        for (unsigned i = 0; i < res; ++ i){
            rhs_tmp[i] = f_add_stack.back(); f_add_stack.pop_back();
        }

        if (! lhs_width) { // integer, conversion required
            // DRIVEL << "INT -> ALGEBRAIC LHS" << endl;
            algebraic_from_integer_const(res);
        }
        else { // just padding required
            bool is_signed = tm.as_algebraic(lhs_type)->is_signed();
            algebraic_padding(lhs_width, res, is_signed);
        }

        // push other operand's type
        f_type_stack.push_back(rhs_type);

        /* restore RHS and continue */
        for (unsigned i = 0; i < res; ++ i){
            f_add_stack.push_back(rhs_tmp[res - i - 1]);
        }

        assert( stack_size - ( is_ite ? 2 : 1 ) == f_type_stack.size());
        return res;
    }

    assert( false ); // unreachable
}

unsigned Compiler::algebrize_binary_predicate()
{
    TypeMgr& tm = f_owner.tm();

    unsigned stack_size = f_type_stack.size();
    assert (2 <= stack_size);

    const Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();
    // DRIVEL << "RHS is " << rhs_type << endl;

    const Type_ptr lhs_type = f_type_stack.back(); f_type_stack.pop_back();
    // DRIVEL << "LHS is " << lhs_type << endl;

    assert( tm.is_algebraic(rhs_type) || tm.is_algebraic(lhs_type) );
    unsigned rhs_width = tm.is_algebraic(rhs_type)
        ? tm.as_algebraic(rhs_type)->width()
        : 0;

    unsigned lhs_width = tm.is_algebraic(lhs_type)
        ? tm.as_algebraic(lhs_type)->width()
        : 0;

    /* max */
    unsigned res = rhs_width < lhs_width
        ? lhs_width
        : rhs_width
        ;

    // Nothing do be done, just add result type to the type stack and leave
    if ((rhs_width == res) && (lhs_width == res)) {
        // DRIVEL << "Nothing do be done." << endl;
        f_type_stack.push_back(tm.find_boolean()); // predicate
        return res;
    }

    /* perform conversion or padding, taking sign bit into account */
    if (rhs_width < res) {
        if (! rhs_width) { // integer, conversion required
            // DRIVEL << "INT -> ALGEBRAIC RHS" << endl;
            algebraic_from_integer_const(res);
        }
        else { // just padding required
            bool is_signed = tm.as_algebraic(rhs_type)->is_signed();
            algebraic_padding(rhs_width, res, is_signed);
        }

        // push boolean type and return
        f_type_stack.push_back(tm.find_boolean());
        return res;
    }

    if (lhs_width < res) {
        /* temporary storage to let adjustment for LHS to take place */
        ADD rhs_tmp[res];
        for (unsigned i = 0; i < res; ++ i){
            rhs_tmp[i] = f_add_stack.back(); f_add_stack.pop_back();
        }

        if (! lhs_width) { // integer, conversion required
            // DRIVEL << "INT -> ALGEBRAIC LHS" << endl;
            algebraic_from_integer_const(res);
        }
        else { // just padding required
            bool is_signed = tm.as_algebraic(lhs_type)->is_signed();
            algebraic_padding(lhs_width, res, is_signed);
        }

        // push boolean type
        f_type_stack.push_back(tm.find_boolean());

        /* restore RHS and continue */
        for (unsigned i = 0; i < res; ++ i){
            f_add_stack.push_back(rhs_tmp[res - i - 1]);
        }

        return res;
    }

    assert( false ); // unreachable
}

/* UPDATE: currently this is used only in array selectors */
unsigned Compiler::algebrize_unary()
{
    TypeMgr& tm = f_owner.tm();

    unsigned stack_size = f_type_stack.size();
    assert (1 <= stack_size);

    unsigned machine_width = 2; // TODO!

    const Type_ptr top_type = f_type_stack.back(); f_type_stack.pop_back();
    // DRIVEL << "TOP is " << top_type << endl;

    unsigned top_width = tm.is_algebraic(top_type)
        ? tm.as_algebraic(top_type)->width()
        : 0;

    /* max */
    unsigned res = top_width < machine_width
        ? machine_width
        : top_width
        ;

    // Nothing do be done, just ad result type to the type stack and leave
    if ((top_width == res)) {
        // DRIVEL << "Nothing do be done." << endl;
        f_type_stack.push_back(top_type); // arbitrary

        assert( stack_size - 1 == f_type_stack.size());
        return res;
    }

    /* perform conversion or padding, taking sign bit into account */
    if (top_width < res) {
        if (! top_width) { // integer, conversion required
            // DRIVEL << "INT -> ALGEBRAIC TOP" << endl;
            algebraic_from_integer_const(res);
        }
        else { // just padding required
            bool is_signed = tm.as_algebraic(top_type)->is_signed();
            algebraic_padding(top_width, res, is_signed);
        }

        // push other operand's type and return
        f_type_stack.push_back(tm.find_unsigned(2)); // TODO machine_size

        assert( stack_size - 1 == f_type_stack.size());
        return res;
    }

    assert( false ); // unreachable
}


static inline value_t pow(unsigned base, unsigned exp)
{
    value_t res = 1;
    for (unsigned i = exp; (i); -- i) {
        res *= base;
    }

    return res;
}

/* basic case: integer constant */
void Compiler::algebraic_from_integer_const(unsigned width)
{
    const ADD top = f_add_stack.back(); f_add_stack.pop_back();
    assert (f_enc.is_constant(top));

    value_t value = f_enc.const_value(top);
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
    // DRIVEL << "ALGEBRAIC " << width << endl;
}

/* extends a DD vector on top of the stack from old_width to
   new_width */
void Compiler::algebraic_padding(unsigned old_width,
                                 unsigned new_width,
                                 bool is_signed)
{
    ADD padding = f_enc.zero();
    ADD zero = f_enc.zero();

    assert (old_width < new_width); // old is smaller than new

    ADD tmp[old_width];
    for (int i = old_width -1; (0 <= i) ; -- i) {
        tmp[i] = f_add_stack.back(); f_add_stack.pop_back();
    }

    // sign extension predicate (0x00 or 0xFF?) only if required.
    if (is_signed) {
        padding += tmp[0].BWTimes(f_enc.msb()).Equals(zero).Ite(zero, f_enc.full());
    }

    for (int i = new_width - old_width /* -1 + 1 */; (0 <= i); -- i) {
        f_add_stack.push_back(padding);
    }
    for (int i = old_width -1; (0 <= i); -- i) {
        f_add_stack.push_back(tmp[i]);
    }
}

/* Discards an operand (and corresponding type). This is needed for
   rewrites. */
void Compiler::algebraic_discard_op()
{
    TypeMgr& tm = f_owner.tm();

    const Type_ptr type = f_type_stack.back(); f_type_stack.pop_back();
    unsigned width = tm.is_algebraic(type)
        ? tm.as_algebraic(type)->width()
        : 1;

    /* discard DDs */
    for (unsigned i = 0; i < width; ++ i) {
        f_add_stack.pop_back();
    }
}

/* Builds a temporary encoding. This is used by some algebraic
   algorithms (e.g. division) */
Expr_ptr Compiler::make_temporary_encoding(ADD dds[], unsigned width)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    ostringstream oss;
    oss << "__tmp" << f_temp_auto_index ++ ;

    Expr_ptr expr = em.make_identifier(oss.str());

    /* Register temporary symbol into resolver (temporaries are global) */
    f_owner.resolver()->register_temporary(expr,
                                           new Temporary(expr,
                                                         tm.find_unsigned( width )));

    /* register encoding, using fqexpr */
    const FQExpr& key = FQExpr(expr);
    f_temp_encodings [ key ] = new AlgebraicEncoding(width, false, dds);

    return expr;
}

void Compiler::debug_hook()
{
#if 0
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
#endif
}

/**
   Booleans:
   . binary: AND, OR, XOR, XNOR, IFF, IMPLIES, EQ, NE
   . unary : NOT, () ?

   Finite Range Integers (aka Monolithes)

   . binary: AND (bw), OR(bw), XOR(bw), XNOR(bw), IFF(bw),
   IMPLIES(bw), LT, LE, GT, GE, EQ, NE, PLUS, SUB, DIV, MUL, MOD

   . unary : ? (), : (), NEG, NOT(bw)

   Enums (strict subset of the above)
   . binary : LT, LE, GT, GE, EQ, NE
   . unary  : ? (), : (),

   Algebraic:

   . binary : AND(bw), OR(bw), XOR(bw), XNOR(bw), IFF(bw),
   IMPLIES(bw), LT, LE, GT, GE, EQ, NE, PLUS, SUB, DIV, MUL, MOD

   . unary  : NOT(bw), ? (), : (), NEG,
*/

bool Compiler::is_binary_boolean(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* AND, OR, XOR, XNOR, IFF, IMPLIES */
    if (em.is_binary_logical(expr)) {
        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());
        return (tm.is_boolean(f_owner.type(lhs)) &&
                tm.is_boolean(f_owner.type(rhs)));
    }

    return false;
}

bool Compiler::is_unary_boolean(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /*  NOT, () ? */
    if (em.is_unary_logical(expr)) {
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());
        return (tm.is_boolean(f_owner.type(lhs)));
    }

    return false;
}

bool Compiler::is_binary_integer(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* AND (bw), OR(bw), XOR(bw), XNOR(bw), IFF(bw),
       IMPLIES(bw), LT, LE, GT, GE, EQ, NE, PLUS, SUB, DIV, MUL, MOD */
    if ((em.is_binary_logical(expr)) ||
        (em.is_binary_arithmetical(expr)) ||
        (em.is_binary_relational(expr))) {

        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());
        return (tm.is_integer(f_owner.type(lhs)) &&
                tm.is_integer(f_owner.type(rhs)));
    }

    return false;
}

bool Compiler::is_unary_integer(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* unary : ? (), : (), NEG, NOT(bw) */
    if (em.is_unary_arithmetical(expr)) {
        Type_ptr tp = f_type_stack.back();
        return (tm.is_integer(tp));
    }

    return false;
}

bool Compiler::is_binary_enumerative(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* AND (bw), OR(bw), XOR(bw), XNOR(bw), IFF(bw),
       IMPLIES(bw), LT, LE, GT, GE, EQ, NE, PLUS, SUB, DIV, MUL, MOD */
    if ((em.is_binary_arithmetical(expr)) ||
        (em.is_binary_relational(expr))) {

        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());
        return (tm.is_enum(f_owner.type(lhs)) &&
                tm.is_enum(f_owner.type(rhs)));
    }

    return false;
}

bool Compiler::is_unary_enumerative(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* unary : ? (), : (), NEG, NOT(bw) */
    if (em.is_unary_arithmetical(expr)) {
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());

        return (tm.is_enum(f_owner.type(lhs)));
    }

    return false;
}

/* following predicates take into account that conversion may be
   needed to "algebrize" an operand, *but not BOTH of them* */
bool Compiler::is_binary_algebraic(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    if ((em.is_binary_logical(expr)) ||
        (em.is_binary_arithmetical(expr)) ||
        (em.is_binary_relational(expr))) {

        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());

        // see comment above
        return ( (tm.is_algebraic(f_owner.type(lhs)) ||
                  tm.is_integer(f_owner.type(lhs))) &&

                 (tm.is_algebraic(f_owner.type(rhs)) ||
                  tm.is_integer(f_owner.type(rhs))));
    }

    return false;
}

bool Compiler::is_unary_algebraic(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    if ((em.is_unary_logical(expr)) ||
        (em.is_unary_arithmetical(expr))) {

        FQExpr lhs(f_ctx_stack.back(), expr->lhs());

        return ( (tm.is_algebraic(f_owner.type(lhs)) ||
                  tm.is_integer(f_owner.type(lhs))));
    }

    return false;
}

bool Compiler::is_ite_boolean(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* ITE */
    if (em.is_ite(expr)) {
        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());
        return (tm.is_boolean(f_owner.type(lhs)) &&
                tm.is_boolean(f_owner.type(rhs)));
    }

    return false;
}

bool Compiler::is_ite_integer(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* ITE (bw) */
    if (em.is_ite(expr)) {

        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());
        return (tm.is_integer(f_owner.type(lhs)) &&
                tm.is_integer(f_owner.type(rhs)));
    }

    return false;
}

bool Compiler::is_ite_enumerative(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* ITE (bw) */
    if (em.is_ite(expr)) {

        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());
        return (tm.is_enum(f_owner.type(lhs)) &&
                tm.is_enum(f_owner.type(rhs)));
    }

    return false;

}

bool Compiler::is_ite_algebraic(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    if (em.is_ite(expr)) {

        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());

        return ( (tm.is_algebraic(f_owner.type(lhs)) ||
                  tm.is_integer(f_owner.type(lhs))) &&

                 (tm.is_algebraic(f_owner.type(rhs)) ||
                  tm.is_integer(f_owner.type(rhs))));
    }

    return false;
}

static inline value_t pow2(unsigned exp)
{
    value_t res = 1;
    for (unsigned i = exp; i; -- i) {
        res *= 2;
    }

        return res;
}

Expr_ptr Compiler::make_bounded_exp2(ADD *dds, unsigned width)
{
    value_t value;

    unsigned base = Cudd_V(f_enc.base().getNode());
    unsigned exp2 = 0;

    ADD mpx[width]; /* multiplex */
    for (unsigned i = 0; i < width; ++ i) {
        unsigned ndx = width - i - 1;
        mpx[ndx] = (! ndx )
            ? f_enc.one()
            : f_enc.zero() ;
    }

    while (exp2 < width) {
        ADD condition = f_enc.one();
        { /* inlined condition */
            value = exp2;

            /* inlined condition */
            for (unsigned i = 0; i < width; ++ i) {
                unsigned ndx = width - i - 1;

                condition *= dds[ndx].
                    Equals(f_enc.constant(value % base));

                value /= base;
            }
            assert (value == 0); // not overflowing
        }

        ADD constant[width];
        {/* inlined power of 2 */
            value = pow2(exp2);
            for (unsigned i = 0; i < width; ++ i) {
                unsigned ndx = width - i - 1;

                constant[ndx] = f_enc.constant(value % base);

                value /= base;
            }
            assert (value == 0); // not overflowing
        }

        for (unsigned i = 0; i < width; ++ i) {
            mpx[i] = condition.Ite( constant[i], mpx[i] );
        }

        ++ exp2;
    }

    return make_temporary_encoding(mpx, width);
}

bool Compiler::cache_miss(const Expr_ptr expr)
{
    FQExpr key(f_ctx_stack.back(), expr, f_time_stack.back());
    ADDMap::iterator eye = f_map.find(key);

    if (eye != f_map.end()) {
        const Type_ptr type = f_owner.type(key);
        TRACE << "Cache hit for " << expr
              << " type is " << type
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

void Compiler::memoize_result(const Expr_ptr expr)
{
    TypeMgr& tm = f_owner.tm();

    assert( 0 < f_type_stack.size() );
    Type_ptr type = f_type_stack.back();

    /* assemble memoization key */
    assert( 0 < f_ctx_stack.size() );
    Expr_ptr ctx = f_ctx_stack.back();

    assert( 0 < f_time_stack.size() );
    step_t time = f_time_stack.back();

    FQExpr key(ctx, expr, time);
    TRACE << "Memoizing result for " << key
          << " type is " << type << endl;

    /* collect dds and memoize */
    DDVector dv;
    unsigned i, width;
    if (tm.is_algebraic(type)) {
        width = tm.as_algebraic(type)->width();
    }

    else if (tm.is_boolean(type)) {
        width = 1;
    }

    else assert (false); /* unreachable */

    assert(width <= f_add_stack.size());
    ADDStack::reverse_iterator ri;
    for (i = 0, ri = f_add_stack.rbegin();
         i < width; ++ i, ++ ri) {
        dv.push_back(*ri);
    }
    assert (dv.size() == width);

    f_map.insert( make_pair <FQExpr,
                  DDVector> ( key, dv ));
}

int double_cmp(double x, double y)
{
    return (x == y)
        ? 0
        : ((x < y)
           ? 1
           : -1);
}

struct DDInfo {
    ADD dd;
    double npaths;

    DDInfo(ADD add)
        : dd(add)
    {
        npaths = dd.CountPath();
    }
};

bool compare_ddinfo( const DDInfo & e1, const DDInfo & e2)
{ return e1.npaths < e2.npaths; }

typedef vector<DDInfo> DDInfoVector;

ADD Compiler::optimize_and_chain(ADD* dds, unsigned len)
{
    DDInfoVector iv;
    for (unsigned i = 0; i < len; ++ i) {
        iv.push_back( DDInfo(dds[i]));
    }

    std::sort( iv.begin(), iv.end(), compare_ddinfo );

    ADD res = f_enc.one();
    for (DDInfoVector::iterator i = iv.begin(); i != iv.end(); ++ i) {
        res *= (*i).dd;
    }

    return res;
}
