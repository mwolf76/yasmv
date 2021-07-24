/**
 * @file unit.hh
 * @brief Basic expressions compiler - Output type definition
 *
 * This header file contains the declarations required by the
 * compilation unit.
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

#ifndef COMPILATION_UNIT_H
#define COMPILATION_UNIT_H

#include <vector>

#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_comparison.hpp>

#include <boost/unordered_map.hpp>

#include <expr/expr.hh>

#include <dd/dd.hh>

/** Exception classes */
class UnitException : public Exception {
public:
    const char* what() const throw();
    UnitException(const char *msg);

private:
    const char* f_msg;
};

/* <symb, is_signed?, width> */
typedef boost::tuple<bool, ExprType, unsigned> InlinedOperatorSignature;
inline const InlinedOperatorSignature make_ios (bool is_signed,
                                                ExprType exprType,
                                                unsigned width)
{
    return boost::make_tuple <bool, ExprType, unsigned>
        (is_signed, exprType, width);
}

/* ios helper getters */
inline bool ios_issigned( const InlinedOperatorSignature& ios )
{ return ios.get<0>(); }
inline ExprType ios_optype( const InlinedOperatorSignature& ios )
{ return ios.get<1>(); }
inline unsigned ios_width( const InlinedOperatorSignature& ios )
{ return ios.get<2>(); }

struct InlinedOperatorSignatureHash {
    long operator() (const InlinedOperatorSignature& k) const
    {
        const long prime = 31;

        long res = 1;
        res = prime * res + (k.get<0>() ? 1231 : 1237);
        res = prime * res + k.get<1>();
        res = prime * res + k.get<2>();
        return res;
    }
};

struct InlinedOperatorSignatureEq {
    bool operator() (const InlinedOperatorSignature& x,
                     const InlinedOperatorSignature& y) const
    {
        return
            x.get<0>() == y.get<0>() &&
            x.get<1>() == y.get<1>() &&
            x.get<2>() == y.get<2>() ;
    }
};

class BinarySelectionDescriptor {
public:
    BinarySelectionDescriptor(unsigned width, DDVector& z, ADD cnd,
                              ADD aux, DDVector& x, DDVector& y);

    inline unsigned width() const
    { return f_width; }
    inline const DDVector& z() const
    { return f_z; }
    inline ADD cnd() const
    { return f_cnd; }
    inline ADD aux() const
    { return f_aux; }
    inline const DDVector& x() const
    { return f_x; }
    inline const DDVector& y() const
    { return f_y; }

private:
    unsigned f_width;
    DDVector f_z;
    ADD f_cnd;
    ADD f_aux;
    DDVector f_x;
    DDVector f_y;
};

class MultiwaySelectionDescriptor {
public:
    MultiwaySelectionDescriptor(unsigned elem_width, unsigned elem_count,
                                DDVector& z, DDVector& cnds,
                                DDVector& acts, DDVector& x);

    inline unsigned elem_width() const
    { return f_elem_width; }
    inline unsigned elem_count() const
    { return f_elem_count; }
    inline const DDVector& z() const
    { return f_z; }
    inline const DDVector& cnds() const
    { return f_cnds; }
    inline const DDVector& acts() const
    { return f_acts; }
    inline const DDVector& x() const
    { return f_x; }

private:
    unsigned f_elem_width;
    unsigned f_elem_count;
    DDVector f_z;
    DDVector f_cnds;
    DDVector f_acts;
    DDVector f_x;
};

class InlinedOperatorDescriptor {

public:
    InlinedOperatorDescriptor(InlinedOperatorSignature ios,
                              DDVector& z, DDVector &x);
    InlinedOperatorDescriptor(InlinedOperatorSignature ios,
                              DDVector& z, DDVector &x, DDVector &y);

    inline const InlinedOperatorSignature& ios() const
    { return f_ios; }

    inline const DDVector& z() const
    { return f_z; }
    inline const DDVector& x() const
    { return f_x; }
    inline const DDVector& y() const
    { return f_y; }

    inline bool is_relational() const
    { return f_z.size() == 1; }

    inline bool is_binary() const
    {
        return f_z.size() == f_x.size() &&
            f_z.size() == f_y.size();
    }

    inline bool is_unary() const
    { return f_y.size() == 0; }

private:
    InlinedOperatorSignature f_ios;

    DDVector f_z;
    DDVector f_x;
    DDVector f_y;
};

typedef std::vector<InlinedOperatorDescriptor> InlinedOperatorDescriptors;
typedef std::vector<BinarySelectionDescriptor> BinarySelectionDescriptors;
typedef std::vector<MultiwaySelectionDescriptor> MultiwaySelectionDescriptors;

typedef boost::unordered_map<Expr_ptr,
                             BinarySelectionDescriptors> Expr2BinarySelectionDescriptorsMap;

enum ECompilerTimePolarity {
    UNDECIDED,
    POSITIVE,
    NEGATIVE
};

class CompilationUnit {
public:
    CompilationUnit( Expr_ptr expr, DDVector& dds,
                     InlinedOperatorDescriptors& inlined_operator_descriptors,
                     Expr2BinarySelectionDescriptorsMap& binary_selection_descriptors_map,
                     MultiwaySelectionDescriptors& array_mux_descriptors)
        : f_expr(expr)
        , f_dds(dds)
        , f_inlined_operator_descriptors( inlined_operator_descriptors )
        , f_binary_selection_descriptors_map( binary_selection_descriptors_map )
        , f_array_mux_descriptors( array_mux_descriptors )
    {}

    const Expr_ptr expr() const
    { return f_expr; }

    const DDVector& dds() const
    { return f_dds; }

    const InlinedOperatorDescriptors& inlined_operator_descriptors() const
    { return f_inlined_operator_descriptors; }

    const Expr2BinarySelectionDescriptorsMap& binary_selection_descriptors_map() const
    { return f_binary_selection_descriptors_map; }

    const MultiwaySelectionDescriptors& array_mux_descriptors() const
    { return f_array_mux_descriptors; }

private:
    Expr_ptr f_expr;
    DDVector f_dds;
    InlinedOperatorDescriptors f_inlined_operator_descriptors;
    Expr2BinarySelectionDescriptorsMap f_binary_selection_descriptors_map;
    MultiwaySelectionDescriptors f_array_mux_descriptors;
};
typedef CompilationUnit* CompilationUnit_ptr;
typedef std::vector<CompilationUnit> CompilationUnits;

/* helpers */
std::ostream& operator<<(std::ostream& os, CompilationUnit& cu);

std::ostream& operator<<(std::ostream& os, InlinedOperatorSignature ios);
std::string ios2string(InlinedOperatorSignature ios);

std::ostream& operator<<(std::ostream& os, InlinedOperatorDescriptor& iod);
std::string iod2string(InlinedOperatorSignature& ios);

std::ostream& operator<<(std::ostream& os, BinarySelectionDescriptor& md);
std::string bsd2string(InlinedOperatorSignature& ios);

std::ostream& operator<<(std::ostream& os, MultiwaySelectionDescriptor& md);
std::string msd2string(InlinedOperatorSignature& ios);

#endif /* COMPILATION_UNIT_H */

