/**
 * @file typedefs.hh
 * @brief Propositional logic compiler - module shared typedefs
 *
 * This header file contains the declarations required to implement
 * the compilation of propositional logic expressions.
 *
 * Copyright (C) 2011-2015 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2.1 of
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

#ifndef COMPILER_TYPEDEFS_H
#define COMPILER_TYPEDEFS_H

#include <boost/unordered_map.hpp>

#include <dd/dd.hh>

#include <expr/expr.hh>
#include <expr/time/timed_expr.hh>

#include <utils/pool.hh>

namespace compiler {

using BinarySelectionUnionFindMap =
    boost::unordered_map<expr::Expr_ptr, expr::Expr_ptr,
                         utils::PtrHash, utils::PtrEq> ;

enum ECompilerStatus {
    READY,
    ENCODING,
    COMPILING,
    CHECKING,
    ACTIVATING_ITE_MUXES,
    ACTIVATING_ARRAY_MUXES
};

/* decl only */
ECompilerStatus& operator++(ECompilerStatus& status);

/* <symb, is_signed?, width> */
using InlinedOperatorSignature =
    boost::tuple<bool, expr::ExprType, unsigned>;

inline const InlinedOperatorSignature make_ios (bool is_signed, expr::ExprType exprType, unsigned width)
{
    return boost::make_tuple <bool, expr::ExprType, unsigned>
        (is_signed, exprType, width);
}

/* ios helper getters */
inline bool ios_issigned( const InlinedOperatorSignature& ios )
{ return ios.get<0>(); }
inline expr::ExprType ios_optype( const InlinedOperatorSignature& ios )
{ return ios.get<1>(); }
inline unsigned ios_width( const InlinedOperatorSignature& ios )
{ return ios.get<2>(); }

struct InlinedOperatorSignatureHash {
    long operator() (const InlinedOperatorSignature& k) const ;
};

struct InlinedOperatorSignatureEq {
    bool operator() (const InlinedOperatorSignature& x,
                     const InlinedOperatorSignature& y) const ;
};

class BinarySelectionDescriptor {
public:
    BinarySelectionDescriptor(unsigned width, dd::DDVector& z, ADD cnd,
                              ADD aux, dd::DDVector& x, dd::DDVector& y);

    inline unsigned width() const
    { return f_width; }

    inline const dd::DDVector& z() const
    { return f_z; }

    inline ADD cnd() const
    { return f_cnd; }

    inline ADD aux() const
    { return f_aux; }

    inline const dd::DDVector& x() const
    { return f_x; }

    inline const dd::DDVector& y() const
    { return f_y; }

private:
    unsigned f_width;
    dd::DDVector f_z;
    ADD f_cnd;
    ADD f_aux;
    dd::DDVector f_x;
    dd::DDVector f_y;
};

class MultiwaySelectionDescriptor {
public:
    MultiwaySelectionDescriptor(unsigned elem_width, unsigned elem_count,
                                dd::DDVector& z, dd::DDVector& cnds,
                                dd::DDVector& acts, dd::DDVector& x);

    inline unsigned elem_width() const
    { return f_elem_width; }

    inline unsigned elem_count() const
    { return f_elem_count; }

    inline const dd::DDVector& z() const
    { return f_z; }

    inline const dd::DDVector& cnds() const
    { return f_cnds; }

    inline const dd::DDVector& acts() const
    { return f_acts; }

    inline const dd::DDVector& x() const
    { return f_x; }

private:
    unsigned f_elem_width;
    unsigned f_elem_count;
    dd::DDVector f_z;
    dd::DDVector f_cnds;
    dd::DDVector f_acts;
    dd::DDVector f_x;
};

class InlinedOperatorDescriptor {

public:
    InlinedOperatorDescriptor(InlinedOperatorSignature ios,
                              dd::DDVector& z, dd::DDVector &x);
    InlinedOperatorDescriptor(InlinedOperatorSignature ios,
                              dd::DDVector& z, dd::DDVector &x, dd::DDVector &y);

    inline const InlinedOperatorSignature& ios() const
    { return f_ios; }

    inline const dd::DDVector& z() const
    { return f_z; }

    inline const dd::DDVector& x() const
    { return f_x; }

    inline const dd::DDVector& y() const
    { return f_y; }


    inline bool is_relational() const
    { return f_z.size() == 1; }

    inline bool is_binary() const
    { return f_z.size() == f_x.size() && f_z.size() == f_y.size(); }

    inline bool is_unary() const
    { return f_y.size() == 0; }

private:
    InlinedOperatorSignature f_ios;

    dd::DDVector f_z;
    dd::DDVector f_x;
    dd::DDVector f_y;
};

using InlinedOperatorDescriptors =
    std::vector<InlinedOperatorDescriptor> ;

using BinarySelectionDescriptors =
    std::vector<BinarySelectionDescriptor> ;

using MultiwaySelectionDescriptors =
    std::vector<MultiwaySelectionDescriptor> ;

using Expr2BinarySelectionDescriptorsMap =
    boost::unordered_map<expr::Expr_ptr, BinarySelectionDescriptors> ;

class CompilationUnit {
public:
    CompilationUnit( expr::Expr_ptr expr, dd::DDVector& dds,
                     InlinedOperatorDescriptors& inlined_operator_descriptors,
                     Expr2BinarySelectionDescriptorsMap& binary_selection_descriptors_map,
                     MultiwaySelectionDescriptors& array_mux_descriptors)
        : f_expr(expr)
        , f_dds(dds)
        , f_inlined_operator_descriptors( inlined_operator_descriptors )
        , f_binary_selection_descriptors_map( binary_selection_descriptors_map )
        , f_array_mux_descriptors( array_mux_descriptors )
    {}

    inline const expr::Expr_ptr expr() const
    { return f_expr; }

    inline const dd::DDVector& dds() const
    { return f_dds; }

    inline const InlinedOperatorDescriptors& inlined_operator_descriptors() const
    { return f_inlined_operator_descriptors; }

    inline const Expr2BinarySelectionDescriptorsMap& binary_selection_descriptors_map() const
    { return f_binary_selection_descriptors_map; }

    inline const MultiwaySelectionDescriptors& array_mux_descriptors() const
    { return f_array_mux_descriptors; }

private:
    expr::Expr_ptr f_expr;
    dd::DDVector f_dds;
    InlinedOperatorDescriptors f_inlined_operator_descriptors;
    Expr2BinarySelectionDescriptorsMap f_binary_selection_descriptors_map;
    MultiwaySelectionDescriptors f_array_mux_descriptors;
};

using CompilationUnit_ptr =
    CompilationUnit* ;

using CompilationUnits =
    std::vector<CompilationUnit> ;

} // namespace compiler

#endif /* COMPILER_TYPEDEFS_H */
