/**
 *  @file expr.hh
 *  @brief Expression management
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
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
#ifndef EXPR_H
#define EXPR_H

#include <common.hh>
#include <atom.hh>

typedef enum {
    // -- primary expressions --------------------------------------------------

    /* temporal ops */
    // INIT,
    NEXT, // AT,

    /* arithmetical operators */
    NEG, PLUS, SUB, DIV, MUL, MOD,

    /* word-related operators */
    // CONCAT, COUNT,

    /* logical/bitwise operators */
    NOT, AND, OR, XOR, XNOR, IMPLIES, IFF, LSHIFT, RSHIFT,

    /* relational operators */
    EQ, NE, GE, GT, LE, LT,

    /* conditionals */
    ITE, COND,

    /* leaves */
    ICONST, UWCONST, SWCONST, IDENT, DOT, NIL,

    // -- temporal logic ops ---------------------------------------------------

    /* LTL ops */
    F, G, X, U, R,

    /* CTL ops */
    AF, EF, AG, EG, AX, EX, AU, EU, AR, ER,

    // -- declarations ---------------------------------------------------------

    // types
    BOOL, SIGNED, UNSIGNED,

    BITS, // reserved for signed(bits) and unsigned(bits)

    /* utils */
    // SUBSCRIPT,
    RANGE,

    COMMA, SET, // reserved for enums

} ExprType;

// system-wide expr
typedef struct Expr_TAG Expr;
typedef Expr* Expr_ptr;

// An Expression consists of an AST symbol, which is the expression
// main operator, operands which depend on the type of operator and a
// context, in which the expression has to evaluated.
struct Expr_TAG {

    // AST symb type
    ExprType f_symb;

    union {
        // identifiers
        Atom_ptr f_atom;

        // operators
        struct  {
            Expr_ptr f_lhs;
            Expr_ptr f_rhs; // NULL for unary ops
        };

        // word and numeric constants
        struct {
            size_t f_size;
            value_t f_value;
        };
    } u;

    // accessors
    inline Atom_ptr atom()
    { return u.f_atom; }

    inline size_t size()
    { return u.f_size; }
    inline value_t value()
    { return u.f_value; }

    inline Expr_ptr lhs()
    { return u.f_lhs; }
    inline Expr_ptr rhs()
    { return u.f_rhs; }

    inline Expr_TAG()
        : f_symb(NIL)
    {}

    // // bool consts
    // inline Expr_TAG(ExprType symb)
    //     : f_symb(symb)
    // {
    //     assert ((symb == FALSE) || (symb == TRUE));
    //     u.f_lhs = NULL;
    //     u.f_rhs = NULL;
    // }

    // identifiers
    inline Expr_TAG(const Atom& atom)
    : f_symb(IDENT)
    { u.f_atom = const_cast<Atom *>(& atom); }

    // word constants
    inline Expr_TAG(ExprType symb, size_t size, value_t value)
        : f_symb(symb)
    {
        assert ((symb == UWCONST) || (symb == SWCONST));

        u.f_size = size;
        u.f_value = value;
    }

    // int constants, are treated as machine size word constants
    inline Expr_TAG(ExprType symb, value_t value)
        : f_symb(symb)
    {
        assert (symb == ICONST);

        u.f_size = sizeof(value_t);
        u.f_value = value;
    }

    // ordinary expr
    inline Expr_TAG(ExprType symb, Expr_TAG* lhs, Expr_TAG* rhs)
        : f_symb(symb)
    {
        u.f_lhs = lhs;
        u.f_rhs = rhs;
    }

}; // Expr_TAG

// Expression pool
struct ExprHash {
    long operator() (const Expr& k) const {
        {
            if (k.f_symb == IDENT) {
                return (long)(k.u.f_atom);
            }

            else {
                long v0, v1, x, res = (long)(k.f_symb);
                if (k.f_symb == ICONST
                    || k.f_symb == SWCONST
                    || k.f_symb == UWCONST) {
                    v0 = (long)(k.u.f_value);
                    v1 = (long)(k.u.f_value >> sizeof(long));
                }
                else {
                    v0 = (long)(k.u.f_lhs);
                    v1 = (long)(k.u.f_rhs);
                }

                res = (res << 4) + v0;
                if ((x = res & 0xF0000000L) != 0)
                    res ^= (x >> 24);
                res &= ~x;

                res = (res << 4) + v1;
                if ((x = res & 0xF0000000L) != 0)
                    res ^= (x >> 24);
                res &= ~x;

                return res;
            }

            assert (0); // unreachable
        }
    }
};

// An equality predicate functor
struct ExprEq {
    bool operator() (const Expr& x, const Expr& y) const
    {
        return
            // both exprs must be the same type and...
            x.f_symb == y.f_symb
            && (
                /* ...either have the same identifier */
                (x.f_symb == IDENT  && *x.u.f_atom == *y.u.f_atom) ||

                /* ...or have the same constant size, value */
                (x.f_symb >= ICONST && x.f_symb <= SWCONST
                 && x.u.f_size == y.u.f_size && x.u.f_size == y.u.f_size) ||

                /* ...or share the same subtrees */
                (x.u.f_lhs == y.u.f_lhs && y.u.f_rhs == y.u.f_rhs));
    }
};

typedef unordered_set<Expr, ExprHash, ExprEq> ExprPool;
typedef pair<ExprPool::iterator, bool> ExprPoolHit;

// system-wide expr
typedef Expr* Expr_ptr;

typedef vector<Expr_ptr> ExprVector;
typedef ExprVector* ExprVector_ptr;

typedef set<Expr_ptr> ExprSet;
typedef ExprSet* ExprSet_ptr;


// for logging purposes
ostream& operator<<(ostream& os, const Expr_ptr t);

class ExprMgr;
typedef ExprMgr* ExprMgr_ptr;

class BadWordConstException : public Exception {
public:
    BadWordConstException(const char* msg)
    : f_msg(msg)
    {}

    virtual const char* what() const throw() {
        return f_msg;
    }

    virtual ~BadWordConstException() throw()
    {}

protected:
    const char* f_msg;
};

class ExprMgr  {
public:
    static ExprMgr& INSTANCE()
    {
        if (! f_instance) {
            f_instance = new ExprMgr();
        }

        return (*f_instance);
    }

    // -- makers ----------------------------------------------------------------

    /* LTL */
    inline Expr_ptr make_F(Expr_ptr expr)
    { return make_expr(F, expr, NULL); }

    inline Expr_ptr make_G(Expr_ptr expr)
    { return make_expr(G, expr, NULL); }

    inline Expr_ptr make_X(Expr_ptr expr)
    { return make_expr(X, expr, NULL); }

    inline Expr_ptr make_U(Expr_ptr lhs, Expr_ptr rhs)
    { return make_expr(U, lhs, rhs); }

    inline Expr_ptr make_R(Expr_ptr lhs, Expr_ptr rhs)
    { return make_expr(R, lhs, rhs); }

    /* CTL (A) */
    inline Expr_ptr make_AF(Expr_ptr expr)
    { return make_expr(AF, expr, NULL); }

    inline Expr_ptr make_AG(Expr_ptr expr)
    { return make_expr(AG, expr, NULL); }

    inline Expr_ptr make_AX(Expr_ptr expr)
    { return make_expr(AX, expr, NULL); }

    inline Expr_ptr make_AU(Expr_ptr lhs, Expr_ptr rhs)
    { return make_expr(AU, lhs, rhs); }

    inline Expr_ptr make_AR(Expr_ptr lhs, Expr_ptr rhs)
    { return make_expr(AR, lhs, rhs); }

    /* CTL (E) */
    inline Expr_ptr make_EF(Expr_ptr expr)
    { return make_expr(EF, expr, NULL); }

    inline Expr_ptr make_EG(Expr_ptr expr)
    { return make_expr(EG, expr, NULL); }

    inline Expr_ptr make_EX(Expr_ptr expr)
    { return make_expr(EX, expr, NULL); }

    inline Expr_ptr make_EU(Expr_ptr lhs, Expr_ptr rhs)
    { return make_expr(EU, lhs, rhs); }

    inline Expr_ptr make_ER(Expr_ptr lhs, Expr_ptr rhs)
    { return make_expr(ER, lhs, rhs); }

    /* temporal ops */
    // inline Expr_ptr make_init(Expr_ptr expr)
    // { return make_expr(INIT, expr, NULL); }

    inline Expr_ptr make_next(Expr_ptr expr)
    { return make_expr(NEXT, expr, NULL); }

    // inline Expr_ptr make_at(time_t time, Expr_ptr expr)
    // { return make_expr(AT, make_iconst(time), expr); }

    /* word-related and casts */
    // inline Expr_ptr make_concat(Expr_ptr a, Expr_ptr b)
    // { return make_expr(CONCAT, a, b); }

    // inline Expr_ptr make_toint(Expr_ptr expr)
    // { return make_expr(CAST_INT, expr, NULL); }

    // inline Expr_ptr make_bool(Expr_ptr expr)
    // { return make_expr(BOOL, expr, NULL); }

    // inline Expr_ptr make_word1(Expr_ptr expr)
    // { throw UnsupportedOperatorException(); }

    inline Expr_ptr make_signed(Expr_ptr expr)
    { return make_expr(SIGNED, expr, NULL); }

    inline Expr_ptr make_unsigned(Expr_ptr expr)
    { return make_expr(UNSIGNED, expr, NULL); }

    // inline Expr_ptr make_count(Expr_ptr expr)
    // { return make_expr(COUNT, expr, NULL); }

    /* arithmetical operators */
    inline Expr_ptr make_neg(Expr_ptr expr)
    { return make_expr(NEG, expr, NULL); }

    inline Expr_ptr make_add(Expr_ptr a, Expr_ptr b)
    { return make_expr(PLUS, a, b); }

    inline Expr_ptr make_sub(Expr_ptr a, Expr_ptr b)
    { return make_expr(SUB, a, b); }

    inline Expr_ptr make_div(Expr_ptr a, Expr_ptr b)
    { return make_expr(DIV, a, b); }

    inline Expr_ptr make_mul(Expr_ptr a, Expr_ptr b)
    { return make_expr(MUL, a, b); }

    inline Expr_ptr make_mod(Expr_ptr a, Expr_ptr b)
    { return make_expr(MOD, a, b); }

    /* logical/bitwise operators */
    inline Expr_ptr make_not(Expr_ptr expr)
    { return make_expr(NOT, expr, NULL); }

    inline Expr_ptr make_and(Expr_ptr a, Expr_ptr b)
    { return make_expr(AND, a, b); }

    inline Expr_ptr make_or(Expr_ptr a, Expr_ptr b)
    { return make_expr(OR, a, b); }

    inline Expr_ptr make_lshift(Expr_ptr a, Expr_ptr b)
    { return make_expr(LSHIFT, a, b); }

    inline Expr_ptr make_rshift(Expr_ptr a, Expr_ptr b)
    { return make_expr(RSHIFT, a, b); }

    inline Expr_ptr make_xor(Expr_ptr a, Expr_ptr b)
    { return make_expr(XOR, a, b); }

    inline Expr_ptr make_xnor(Expr_ptr a, Expr_ptr b)
    { return make_expr(XNOR, a, b); }

    inline Expr_ptr make_implies(Expr_ptr a, Expr_ptr b)
    { return make_expr(IMPLIES, a, b); }

    inline Expr_ptr make_iff(Expr_ptr a, Expr_ptr b)
    { return make_expr(IFF, a, b); }

    /* relational operators */
    inline Expr_ptr make_eq(Expr_ptr a, Expr_ptr b)
    { return make_expr(EQ, a, b); }

    inline Expr_ptr make_ne(Expr_ptr a, Expr_ptr b)
    { return make_expr(NE, a, b); }

    inline Expr_ptr make_ge(Expr_ptr a, Expr_ptr b)
    { return make_expr(GE, a, b); }

    inline Expr_ptr make_gt(Expr_ptr a, Expr_ptr b)
    { return make_expr(GT, a, b); }

    inline Expr_ptr make_le(Expr_ptr a, Expr_ptr b)
    { return make_expr(LE, a, b); }

    inline Expr_ptr make_lt(Expr_ptr a, Expr_ptr b)
    { return make_expr(LT, a, b); }

    inline Expr_ptr make_cond(Expr_ptr a, Expr_ptr b)
    { return make_expr(COND, a, b); }

    inline Expr_ptr make_ite(Expr_ptr a, Expr_ptr b)
    { return make_expr(ITE, a, b); }

    inline Expr_ptr make_iconst(value_t value)
    {
        Expr tmp(ICONST, value); // we need a temp store
        return __make_expr(&tmp);
    }

    inline Expr_ptr make_uwconst(unsigned short wsize, value_t value)
    {
        Expr tmp(UWCONST, wsize, value); // we need a temp store
        return __make_expr(&tmp);
    }

    inline Expr_ptr make_swconst(unsigned short wsize, value_t value)
    {
        Expr tmp(SWCONST, wsize, value); // we need a temp store
        return __make_expr(&tmp);
    }

    inline Expr_ptr make_dot(Expr_ptr a, Expr_ptr b)
    { return make_expr(DOT, a, b); }

    // inline Expr_ptr make_subscript(Expr_ptr a, Expr_ptr b)
    // { return make_expr(SUBSCRIPT, a, b); }

    inline Expr_ptr make_range(Expr_ptr a, Expr_ptr b)
    { return make_expr(RANGE, a, b);  }

    /* -- types ------------------------------------------------------------- */
    inline Expr_ptr make_temporal_type() const
    { return temporal_expr; }

    inline Expr_ptr make_boolean_type() const
    { return bool_expr; }

    // abstract integer type (reserved for inferrer)
    inline Expr_ptr make_integer_type() const
    { return integer_expr; }

    inline Expr_ptr make_bits(Expr_ptr a, Expr_ptr b)
    { return make_expr(BITS, a, b); }

    inline Expr_ptr make_unsigned_type(unsigned bits = DEFAULT_BITS)
    { return make_expr(BITS, unsigned_expr, make_iconst((value_t) bits)); }

    inline Expr_ptr make_signed_type(unsigned bits = DEFAULT_BITS)
    { return make_expr(BITS, signed_expr, make_iconst((value_t) bits)); }

    inline Expr_ptr make_enum_type(ExprSet_ptr literals)
    {
        Expr_ptr res = NULL;

        /* reverse iteration */
        for (ExprSet::reverse_iterator eye = literals->rbegin();
             eye != literals->rend(); eye ++) {
            if (!res) res = (*eye);
            else res = make_expr(COMMA, (*eye), res);
        }

        return make_expr(SET, res, NULL);
    }

    /* -- builtin identifiers ----------------------------------------------- */
    inline Expr_ptr make_main() const
    { return main_expr; }

    inline Expr_ptr make_false()
    { return false_expr; }

    inline Expr_ptr make_true()
    { return true_expr; }

    // TODO: review this comment
    // Here a bit of magic occurs, so it's better to keep a note:
    // this method is used by the parser to build identifier
    // nodes.  The function is fed with a const char* coming from
    // the Lexer, an Atom object (which in current implementation
    // is in fact a std::string) is built on-the-fly and used to
    // search the atom pool. The atom resulting from the search is
    // always the one stored in the pool. The auto atom object,
    // however gets destroyed as it gets out of scope, so no leak
    // occurs.
    inline Expr_ptr make_identifier(Atom atom)
    {
        AtomPoolHit ah = f_atom_pool.insert(atom);
        const Atom& pooled_atom =  (* ah.first);

        if (ah.second) {
            DEBUG << "Added new atom to pool: '"
                  << pooled_atom << "'" << endl;
        }

        // no copy occurs here
        return make_expr(pooled_atom);
    }

    inline Expr_ptr make_wconst(Atom atom)
    {
        regex wconst_rx("0(u|s)(b|d|o|h|)(/d+)_(.+)");
        cmatch match;

        regex_match(atom.c_str(), match, wconst_rx);
        assert (match.size() == 4);

        string sign_flag(match[0]);
        string type_flag(match[1]);
        string size_field(match[2]);
        string wliteral(match[3]);
        bool is_signed = (sign_flag == "s");
        unsigned short wsize = atoi(size_field.c_str());

        value_t value = 0ULL;

        if (match[1] == "b") {
            if (wsize != wliteral.size())
                throw BadWordConstException("Boolean word constants must match the word size.");

            int i;
            for (i = wliteral.size() -1;
                 i >= (is_signed) ? 1 : 0; -- i) {
                value = 2 * value + wliteral[i];
            }

            // MSB is -2^(wsize)
            if ((is_signed) && (wliteral[0] == '1')) {
                value -= pow2(i);
            }

        }

        // NEG not supported here
        else if (match[1] == "d") {
            value = strtoll(wliteral.c_str(), NULL, 10);
        }
        else if (match[1] == "o") {
            value = strtoll(wliteral.c_str(), NULL, 8);
        }
        else if (match[1] == "h") {
            value = strtoll(wliteral.c_str(), NULL, 16);
        }
        else assert(0);

        // range check
        if (value >= pow2(wsize - (is_signed ? 1 : 0))) {
            throw BadWordConstException("Decimal value not representable with this word size.");
        }

        return is_signed
            ? make_swconst(wsize, value)
            : make_uwconst(wsize, value);
    }

    inline Expr_ptr make_hex_const(Atom atom)
    { return make_iconst( strtoll(atom.c_str(), NULL, 16)); }

    inline Expr_ptr make_dec_const(Atom atom)
    { return make_iconst( strtoll(atom.c_str(), NULL, 10)); }

    inline Expr_ptr make_oct_const(Atom atom)
    { return make_iconst( strtoll(atom.c_str(), NULL, 8)); }

    // -- is-a predicates -------------------------------------------------------
    inline bool is_identifier(const Expr_ptr expr) const {
        assert(expr);
        return expr->f_symb == IDENT;
    }

    inline bool is_numeric(const Expr_ptr expr) const {
        assert(expr);
        return (expr->f_symb == ICONST)
            || (expr->f_symb == UWCONST)
            || (expr->f_symb == SWCONST) ;
    }

    // inline Expr_ptr lvalue_varname(const Expr_ptr expr) const {
    //     assert(expr);
    //     if (expr->f_symb == IDENT)
    //         return expr;

    //     if ((expr->f_symb == INIT) ||
    //         (expr->f_symb == NEXT))
    //         return expr->u.f_lhs;

    //     return NULL;
    // }

protected:
    ExprMgr();
    ~ExprMgr();

private:
    static ExprMgr_ptr f_instance;

    /* mid level services */
    Expr_ptr make_expr(ExprType et, Expr_ptr a, Expr_ptr b)
    {
        Expr tmp(et, a, b); // we need a temp store
        return __make_expr(&tmp);
    }

    Expr_ptr make_expr(const Atom& atom)
    {
        Expr tmp(atom); // we need a temp store
        return __make_expr(&tmp);
    }

    // low-level
    inline Expr_ptr __make_expr(Expr_ptr expr) {
        ExprPoolHit eh = f_expr_pool.insert(*expr);
        Expr_ptr pooled_expr = const_cast<Expr_ptr> (& (*eh.first));

        if (eh.second) {
            DEBUG << "Added new expr to pool: '"
                  << pooled_expr << "'" << endl;
        }

        return pooled_expr;
    }

    // utils
    inline value_t pow2(unsigned exp) {
        value_t res = 1;
        for (unsigned i = exp; i; -- i) {
            res *= 2;
        }
        return res;
    }

    /* a few builtin identifiers */

    // temporal exprs type
    Expr_ptr temporal_expr;

    // boolean exprs type and constants
    Expr_ptr bool_expr;
    Expr_ptr false_expr;
    Expr_ptr true_expr;

    // main module
    Expr_ptr main_expr;

    // base for (un-)signed integer
    Expr_ptr unsigned_expr;
    Expr_ptr signed_expr;
    Expr_ptr integer_expr; // reserved for abstract integer-type

    /* shared pools */
    ExprPool f_expr_pool;
    AtomPool f_atom_pool;
};

class FQExpr {
    Expr_ptr f_ctx;
    Expr_ptr f_expr;
    step_t f_time;

public:
    FQExpr(Expr_ptr ctx, Expr_ptr expr, step_t time = 0)
        : f_ctx(ctx)
        , f_expr(expr)
        , f_time(time)
    {}

    FQExpr(Expr_ptr expr)
    : f_ctx(ExprMgr::INSTANCE().make_main()) // default ctx
    , f_expr(expr)
    , f_time(0) // default time
    {}

    FQExpr(const FQExpr& fqexpr)
    : f_ctx(fqexpr.ctx())
    , f_expr(fqexpr.expr())
    , f_time(fqexpr.time())
    {}

    inline const Expr_ptr& ctx() const
    { return f_ctx; }

    inline const Expr_ptr& expr() const
    { return f_expr; }

    inline step_t time() const
    { return f_time; }

    inline bool operator==(const FQExpr& other) const
    {
        return
            this->f_ctx == other.ctx() &&
            this->f_expr == other.expr() &&
            this->f_time == other.time();
    }

    // TODO: hash func
    inline unsigned long hash() const
    { return 0; }

};
typedef FQExpr* FQExpr_ptr;

struct fqexpr_hash {
    inline long operator() (const FQExpr& x) const
    { return x.hash(); }
};

struct fqexpr_eq {
    inline bool operator() (const FQExpr &x,
                            const FQExpr &y) const
    { return x == y; }
};

typedef vector<FQExpr> FQExprVector;

class ISymbol;
typedef ISymbol* ISymbol_ptr;
typedef unordered_map<FQExpr, ISymbol_ptr, fqexpr_hash, fqexpr_eq> Symbols;

class IConstant;
typedef IConstant* IConstant_ptr;
typedef unordered_map<FQExpr, IConstant_ptr, fqexpr_hash, fqexpr_eq> Constants;

class IVariable;
typedef IVariable* IVariable_ptr;
typedef unordered_map<FQExpr, IVariable_ptr, fqexpr_hash, fqexpr_eq> Variables;

class IDefine;
typedef IDefine* IDefine_ptr;
typedef unordered_map<FQExpr, IDefine_ptr, fqexpr_hash, fqexpr_eq> Defines;
typedef unordered_map<FQExpr, IDefine_ptr, fqexpr_hash, fqexpr_eq> Assigns;

class IModule;
typedef IModule* IModule_ptr;
typedef unordered_map<Expr_ptr, IModule_ptr, PtrHash, PtrEq> Modules;

#endif
