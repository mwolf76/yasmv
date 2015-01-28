/**
 *  @file unit.hh
 *  @brief Basic expressions compiler - Output type definition
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

#ifndef COMPILATION_UNIT_H
#define COMPILATION_UNIT_H

#include <vector>

#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_comparison.hpp>

#include <boost/unordered_map.hpp>

#include <dd/dd.hh>
#include <sat/satdefs.hh>

/* <symb, is_signed?, width> */
typedef boost::tuple<bool, ExprType, int> InlinedOperatorSignature;
inline const InlinedOperatorSignature make_ios (bool is_signed, ExprType exprType, int width) {
    return boost::make_tuple <bool, ExprType, int> (is_signed, exprType, width);
}

/* triple helper getters */
inline bool triple_issigned( const InlinedOperatorSignature& triple )
{ return triple.get<0>(); }
inline ExprType triple_optype( const InlinedOperatorSignature& triple )
{ return triple.get<1>(); }
inline int triple_width( const InlinedOperatorSignature& triple )
{ return triple.get<2>(); }

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
    bool operator() (const InlinedOperatorSignature& x, const InlinedOperatorSignature& y) const
    {
        return
            x.get<0>() == y.get<0>() &&
            x.get<1>() == y.get<1>() &&
            x.get<2>() == y.get<2>()  ;
    }
};

class BinarySelectionDescriptor {
public:
    BinarySelectionDescriptor(unsigned width, DDVector& z, ADD cnd, ADD aux, DDVector& x, DDVector& y);

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
                       DDVector& z, DDVector& cnds, DDVector& acts, DDVector& x);

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
    InlinedOperatorDescriptor(InlinedOperatorSignature triple, DDVector& z, DDVector &x);
    InlinedOperatorDescriptor(InlinedOperatorSignature triple, DDVector& z, DDVector &x, DDVector &y);

    inline const InlinedOperatorSignature& triple() const
    { return f_triple; }

    inline const DDVector& z() const
    { return f_z; }
    inline const DDVector& x() const
    { return f_x; }
    inline const DDVector& y() const
    { return f_y; }

    inline bool is_relational() const
    { return f_z.size() == 1; }

    inline bool is_binary() const
    { return f_z.size() == f_x.size() &&
             f_z.size() == f_y.size(); }

    inline bool is_unary() const
    { return f_y.size() == 0; }

private:
    InlinedOperatorSignature f_triple;

    DDVector f_z;
    DDVector f_x;
    DDVector f_y;
};

// helpers
std::ostream& operator<<(std::ostream& os, InlinedOperatorSignature triple);
std::ostream& operator<<(std::ostream& os, InlinedOperatorDescriptor& md);

std::ostream& operator<<(std::ostream& os, BinarySelectionDescriptor& md);
std::ostream& operator<<(std::ostream& os, MultiwaySelectionDescriptor& md);

typedef std::vector<InlinedOperatorDescriptor> InlinedOperatorDescriptors;
typedef std::vector<BinarySelectionDescriptor> BinarySelectionDescriptors;
typedef std::vector<MultiwaySelectionDescriptor> MultiwaySelectionDescriptors;

typedef boost::unordered_map<Expr_ptr, BinarySelectionDescriptors> Expr2BSDMap;

class CompilationUnit {
public:
    CompilationUnit( DDVector& dds,
                     InlinedOperatorDescriptors& micro_descriptors,
                     Expr2BSDMap& mux_map,
                     MultiwaySelectionDescriptors& array_mux_descriptors)
        : f_dds( dds )
        , f_micro_descriptors( micro_descriptors )
        , f_mux_map( mux_map )
        , f_array_mux_descriptors (array_mux_descriptors)
    {}

    const DDVector& dds() const
    { return f_dds; }

    const InlinedOperatorDescriptors& micro_descriptors() const
    { return f_micro_descriptors; }

    const Expr2BSDMap& mux_map() const
    { return f_mux_map; }

    const MultiwaySelectionDescriptors& array_mux_descriptors() const
    { return f_array_mux_descriptors; }

private:
    DDVector f_dds;
    InlinedOperatorDescriptors f_micro_descriptors;
    Expr2BSDMap f_mux_map;
    MultiwaySelectionDescriptors f_array_mux_descriptors;
};
typedef std::vector<CompilationUnit> CompilationUnits;
#endif
