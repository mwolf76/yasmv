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

/* Helper macros */
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

#define ALGEBRIZE_ONE(top, width)               \
    {                                           \
        algebrize_operand((top), (width));      \
    }

#define ALGEBRIZE_TWO(rhs, lhs, width)          \
    {                                           \
        ADD tmp[(width)];                       \
        algebrize_operand((rhs), (width));      \
        FETCH_DDS(tmp, (width));                \
        algebrize_operand((lhs), (width));      \
        PUSH_DDS(tmp, (width));                 \
    }


void Compiler::algebrize_operand(Type_ptr type, unsigned final_width)
{
    TypeMgr& tm = f_owner.tm();

    if (tm.is_int_const(type)) {
        algebraic_from_int_const(final_width);
    }
    else if (tm.is_fxd_const(type)) {
        algebraic_from_fxd_const(final_width);
    }

    else {
        unsigned width = tm.calculate_width(type);
        if (width == final_width) return;

        if (width < final_width) {
            // padding required, take sign bit into account.
            bool is_signed = tm.is_signed_algebraic(type) ||
                tm.is_signed_fixed_algebraic(type);

            algebraic_padding(width, final_width, is_signed);
        }
        else {
            assert (width > final_width);
            assert (false); /* unexpected */
        }
    }
}

unsigned Compiler::algebrize_binary_arithmetical()
{
    TypeMgr& tm = f_owner.tm();

    unsigned stack_size = f_type_stack.size();
    assert (2 <= stack_size);

    const Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();
    const Type_ptr lhs_type = f_type_stack.back(); f_type_stack.pop_back();
    assert( tm.is_algebraic(rhs_type) ||
            tm.is_algebraic(lhs_type) );

    unsigned rhs_width = tm.calculate_width(rhs_type);
    unsigned lhs_width = tm.calculate_width(lhs_type);

    unsigned res = rhs_width < lhs_width
        ? lhs_width
        : rhs_width
        ;

    // Nothing do be done, just ad result type to the type stack and leave
    if ((rhs_width == res) && (lhs_width == res)) {
        f_type_stack.push_back(rhs_type); // arbitrary

        assert( stack_size - 1 == f_type_stack.size());
        return res;
    }

    ALGEBRIZE_TWO(rhs_type, lhs_type, res);
    f_type_stack.push_back(rhs_type);

    assert( stack_size - 1 == f_type_stack.size());
    return res;

    assert( false ); // unreachable
}

unsigned Compiler::algebrize_ternary_ite()
{
    TypeMgr& tm = f_owner.tm();

    unsigned stack_size = f_type_stack.size();
    assert (2 <= stack_size);

    const Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();
    const Type_ptr lhs_type = f_type_stack.back(); f_type_stack.pop_back();
    f_type_stack.pop_back(); /* ITEs require an extra pop() */

    assert( tm.is_algebraic(rhs_type) ||
            tm.is_algebraic(lhs_type) );

    unsigned rhs_width = tm.calculate_width(rhs_type);
    unsigned lhs_width = tm.calculate_width(lhs_type);

    unsigned res = rhs_width < lhs_width
        ? lhs_width
        : rhs_width
        ;

    // Nothing do be done, just add result type to the type stack and
    // leave.
    if ((rhs_width == res) &&
        (lhs_width == res)) {
        f_type_stack.push_back(rhs_type); // arbitrary

        /* sanity check */
        assert( stack_size - 2 == f_type_stack.size());
        return res;
    }

    ALGEBRIZE_TWO(rhs_type, lhs_type, res);

    // sanity check
    assert( stack_size - 2 == f_type_stack.size());
    return res;
}

unsigned Compiler::algebrize_binary_relational()
{
    TypeMgr& tm = f_owner.tm();

    unsigned stack_size = f_type_stack.size();
    assert (2 <= stack_size);

    const Type_ptr rhs_type = f_type_stack.back(); f_type_stack.pop_back();
    const Type_ptr lhs_type = f_type_stack.back(); f_type_stack.pop_back();
    assert( tm.is_algebraic(rhs_type) ||
            tm.is_algebraic(lhs_type) );

    unsigned rhs_width = tm.calculate_width(rhs_type);
    unsigned lhs_width = tm.calculate_width(lhs_type);

    unsigned res = rhs_width < lhs_width
        ? lhs_width
        : rhs_width
        ;

    // Nothing do be done, just add result type to the type stack and
    // leave.
    if ((rhs_width == res) &&
        (lhs_width == res)) {
        f_type_stack.push_back(tm.find_boolean()); // predicate

        /* sanity check */
        assert( stack_size - 1 == f_type_stack.size());
        return res;
    }

    ALGEBRIZE_TWO(rhs_type, lhs_type, res);
    f_type_stack.push_back(tm.find_boolean()); // predicate

    /* sanity check */
    assert( stack_size - 1 == f_type_stack.size());
    return res;
}

unsigned Compiler::algebrize_unary_subscript()
{
    TypeMgr& tm = f_owner.tm();

    unsigned stack_size = f_type_stack.size();
    assert (1 <= stack_size);

    unsigned machine_width = 2; // TODO!

    const Type_ptr top_type = f_type_stack.back(); f_type_stack.pop_back();
    unsigned top_width = tm.calculate_width(top_type);

    unsigned res = top_width < machine_width
        ? machine_width
        : top_width
        ;

    // Nothing do be done, just add result type to the type stack and
    // leave.
    if ((top_width == res)) {
        f_type_stack.push_back(top_type);
        assert( stack_size - 1 == f_type_stack.size());
        return res;
    }

    ALGEBRIZE_ONE(top_type, res);
    f_type_stack.push_back(top_type);

    assert( stack_size - 1 == f_type_stack.size());
    return res;

    assert( false ); // unreachable
}

void Compiler::algebraic_from_int_const(unsigned width)
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
        f_tmp_stack.push_back(digit);
        value /= base;
    }

    assert (value == 0); // not overflowing
}


void Compiler::algebraic_from_fxd_const(unsigned width)
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
    unsigned width = tm.calculate_width(type);

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

void Compiler::pre_node_hook(Expr_ptr expr)
{

}

void Compiler::post_node_hook(Expr_ptr expr)
{
    memoize_result(expr);
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

/* one operand, boolean */
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

/* two operands both int consts */
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
        return (tm.is_int_const(f_owner.type(lhs)) &&
                tm.is_int_const(f_owner.type(rhs)));
    }

    return false;
}

/* two operands, both int or fxd consts, *at least one* fxd const */
bool Compiler::is_binary_fixed(const Expr_ptr expr)
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

        if (((! tm.is_fxd_const(f_owner.type(lhs))) &&
             (! tm.is_int_const(f_owner.type(rhs)))) ||
            ((! tm.is_fxd_const(f_owner.type(lhs))) &&
             (! tm.is_int_const(f_owner.type(rhs))))) return false;

        return ( (tm.is_fxd_const(f_owner.type(lhs))) ||
                 (tm.is_fxd_const(f_owner.type(rhs)))) ;
    }

    return false;
}

/* one operand, int const */
bool Compiler::is_unary_integer(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* unary : ? (), : (), NEG, NOT(bw) */
    if (em.is_unary_arithmetical(expr)) {
        Type_ptr tp = f_type_stack.back();
        return (tm.is_int_const(tp));
    }

    return false;
}

/* one operand, fxd const */
bool Compiler::is_unary_fixed(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* unary : ? (), : (), NEG, NOT(bw) */
    if (em.is_unary_arithmetical(expr)) {
        Type_ptr tp = f_type_stack.back();
        return (tm.is_fxd_const(tp));
    }

    return false;
}

/* two operands, both enumeratives */
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

/* one operand, enumerative */
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

/* two operands, both int, fxd or algebraic. At least one algebraic */
bool Compiler::is_binary_algebraic(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    if ((em.is_binary_logical(expr)) ||
        (em.is_binary_arithmetical(expr)) ||
        (em.is_binary_relational(expr))) {

        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());

        if ( (!tm.is_algebraic(f_owner.type(lhs)) &&
              !tm.is_int_const(f_owner.type(lhs)) &&
              !tm.is_fxd_const(f_owner.type(lhs))) ||

             (!tm.is_algebraic(f_owner.type(rhs)) &&
              !tm.is_int_const(f_owner.type(rhs)) &&
              !tm.is_fxd_const(f_owner.type(rhs))) ) return false;

        return (tm.is_algebraic(f_owner.type(lhs)) ||
                tm.is_algebraic(f_owner.type(rhs)));
    }

    return false;
}

/* one operand, algebraic */
bool Compiler::is_unary_algebraic(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    if ((em.is_unary_logical(expr)) ||
        (em.is_unary_arithmetical(expr))) {

        FQExpr lhs(f_ctx_stack.back(), expr->lhs());
        return (tm.is_algebraic(f_owner.type(lhs)));
    }

    return false;
}

/* same as is_binary_boolean, checks only lhs and rhs */
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

/* same as is_binary_integer, checks only lhs and rhs */
bool Compiler::is_ite_integer(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* ITE (bw) */
    if (em.is_ite(expr)) {

        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());
        return (tm.is_int_const(f_owner.type(lhs)) &&
                tm.is_int_const(f_owner.type(rhs)));
    }

    return false;
}

/* same as is_binary_fixed, checks only lhs and rhs */
bool Compiler::is_ite_fixed(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    /* ITE (bw) */
    if (em.is_ite(expr)) {

        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());

        if (((! tm.is_fxd_const(f_owner.type(lhs))) &&
             (! tm.is_int_const(f_owner.type(rhs)))) ||
            ((! tm.is_fxd_const(f_owner.type(lhs))) &&
             (! tm.is_int_const(f_owner.type(rhs))))) return false;

        return ( (tm.is_fxd_const(f_owner.type(lhs))) ||
                 (tm.is_fxd_const(f_owner.type(rhs)))) ;
    }

    return false;
}

/* same as  is_binary_enumerative, checks only lhs and rhs */
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

/* same as is_binary_algebraic, checks only lhs and rhs */
bool Compiler::is_ite_algebraic(const Expr_ptr expr)
{
    ExprMgr& em = f_owner.em();
    TypeMgr& tm = f_owner.tm();

    if (em.is_ite(expr)) {

        FQExpr rhs(f_ctx_stack.back(), expr->rhs());
        FQExpr lhs(f_ctx_stack.back(), expr->lhs());

        if ( (!tm.is_algebraic(f_owner.type(lhs)) &&
              !tm.is_int_const(f_owner.type(lhs)) &&
              !tm.is_fxd_const(f_owner.type(lhs))) ||

             (!tm.is_algebraic(f_owner.type(rhs)) &&
              !tm.is_int_const(f_owner.type(rhs)) &&
              !tm.is_fxd_const(f_owner.type(rhs))) ) return false;

        return (tm.is_algebraic(f_owner.type(lhs)) ||
                tm.is_algebraic(f_owner.type(rhs)));
    }

    return false;
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
    unsigned i, width = tm.calculate_width(type);
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

Type_ptr Compiler::algebraic_make_int_of_fxd_type(Type_ptr type)
{
    TypeMgr& tm = f_owner.tm();
    Type_ptr res = NULL;

    if (tm.is_signed_fixed_algebraic(type)) {
        SignedFixedAlgebraicType_ptr in = tm.as_signed_fixed_algebraic(type);
        res = tm.find_signed(in->width() + in->fract());
    }
    else if (tm.is_unsigned_algebraic(type)) {
        UnsignedFixedAlgebraicType_ptr in = tm.as_unsigned_fixed_algebraic(type);
        res = tm.find_unsigned(in->width() + in->fract());
    }
    else assert( false ); /* unexpected */

    return res;
}

void Compiler::flush_operands()
{
    for (ADDStack::reverse_iterator ri = f_tmp_stack.rbegin();
         f_tmp_stack.rend() != ri; ++ ri) {
        PUSH(*ri);
    }
    f_tmp_stack.clear();
}
