/**
 *  @file type_exceptions.cc
 *  @brief Type system classes (Exception classes)
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

#include <type_exceptions.hh>
BadContext::BadContext(Expr_ptr ctx)
    : f_ctx(ctx)
{
    ;
}

const char* BadContext::what() const throw()
{
    ostringstream oss;

    oss << "Bad Context: " << f_ctx;
    return oss.str().c_str();
}

BadParams::BadParams(Expr_ptr module, int params_num, int actual_num)
    : f_moduleName(module)
    , f_modl_params_num(params_num)
    , f_inst_params_num(actual_num)
{}

const char* BadParams::what() const throw()
{
    ostringstream oss;

    oss << "BadParams: " << f_moduleName
        << " expected " << f_modl_params_num
        << " got " << f_inst_params_num;
    return oss.str().c_str();
}

UnresolvedSymbol::UnresolvedSymbol(Expr_ptr ctx, Expr_ptr expr)
    : f_ctx(ctx)
    , f_expr(expr)
{}

const char* UnresolvedSymbol::what() const throw()
{
    ostringstream oss;

    oss << "Unresolved symbol: " << f_ctx << "::" << f_expr;
    return oss.str().c_str();
}

BadType::BadType(Expr_ptr repr, expected_t expected)
    : f_repr(repr)
    , f_expected(expected)
{
    ;
}

BadType::~BadType() throw()
{}

TypeMismatch::TypeMismatch(Expr_ptr repr_a, Expr_ptr repr_b)
    : f_repr_a(repr_a)
    , f_repr_b(repr_b)
{}

TypeMismatch::~TypeMismatch() throw()
{}

// static inline Expr_ptr make_abstract_type(expected_t item)
// {
//     ExprMgr& em = ExprMgr::INSTANCE();
//     Expr_ptr res = NULL;

//     switch (item) {
//     case TP_BOOLEAN:
//         res = em.make_boolean_type();
//         break;

//     case TP_INT_CONST:
//         res = em.make_int_const_type();
//         break;

//     case TP_SIGNED_INT:
//         res = em.make_abstract_signed_int_type();
//         break;

//     case TP_UNSIGNED_INT:
//         res = em.make_abstract_unsigned_int_type();
//         break;

//     case TP_ENUM:
//         res = em.make_abstract_set_type();
//         break;

//     case TP_ARRAY:
//         res = em.make_abstract_array_type();
//         break;
//     }

//     assert (NULL != res); /* unexpected */
//     return res;
// }

const char* BadType::what() const throw()
{
    ostringstream oss;

    oss << "BadType: operand has type " << f_repr
        << ", expected: ";

    ExprVector tmp;

    /* collect expected types representations */
    for (unsigned i = 1; i <= TP_LAST_TYPE; i <<= 1) {
        if (i & f_expected) {
            abort();
            // tmp.push_back( make_abstract_type(i));
        }
    }

    /* at least one type is expected, right? */
    assert (0 < tmp.size());

    ExprVector::iterator eye = tmp.begin();
    oss << (*eye);

    if (1 < tmp.size()) {
        ExprVector::iterator last = ( ++ tmp.rbegin()).base();
        while (++ eye != last) {
            oss << ", " << (*eye);
        }

        oss << " or " << (*last);
    }
    oss << ".";

    return oss.str().c_str();
}

const char* TypeMismatch::what() const throw()
{
    ostringstream oss;
    oss << "Type mismatch: "
        << f_repr_a << " and "
        << f_repr_b;

    return oss.str().c_str();
}


ResolutionException::ResolutionException(Expr_ptr expr)
    : f_expr(expr)
{}

const char* ResolutionException::what() const throw()
{
    ostringstream oss;

    oss << "UnresolvedSymbol: " << f_expr;
    return oss.str().c_str();
}
