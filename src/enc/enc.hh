/**
 * @file enc.hh
 * @brief Encoding subsystem declarations.
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

#ifndef ENCODER_H
#define ENCODER_H

#include <vector>

#include <boost/unordered_map.hpp>

#include <common/common.hh>
#include <opts/opts_mgr.hh>

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <type/type.hh>

#include <dd/cudd_mgr.hh>
#include <dd/dd.hh>
#include <enc/enc_mgr.hh>

namespace enc {

    /**
 * For each symbol a boolean encoding is maintained, the encoder takes
 * care of ADD variables definitions and provides mapback services as
 * well.
 **/

    // -- primary decls  --------------------------------------------------------------
    class Encoding {

    public:
        /* Full-Digit DDs (roots), used in manipulation of algebraics
       (e.g.. compiler) */
        inline dd::DDVector& dv()
        {
            return f_dv;
        }

        /* Bit-level DDs (leaves), used in bitlevel operations (e.g. SAT
       solver) */
        inline dd::DDVector& bits()
        {
            return f_bits;
        }

        /* vector of DD leaves (consts) -> expr */
        virtual expr::Expr_ptr expr(int* assignment) = 0;

    protected:
        Encoding()
            : f_mgr(EncodingMgr::INSTANCE())
        {}

        virtual ~Encoding() = 0;

        EncodingMgr& f_mgr;

        dd::DDVector f_dv;   // digit vector
        dd::DDVector f_bits; // all bits

        // low level services
        ADD make_bit();
        ADD make_monolithic_encoding(unsigned nbits);
    };

    typedef Encoding* Encoding_ptr;

    // 1-bit boolean var (identity encoding)
    typedef class BooleanEncoding* BooleanEncoding_ptr;

    class BooleanEncoding: public Encoding {

        friend class EncodingMgr; // expose ctors only to mgr

    public:
        // here assignment *must* have size 1
        expr::Expr_ptr expr(int* assignment);

        ADD bit();

    protected:
        virtual ~BooleanEncoding()
        {
            assert(0);
        }

        // boolean 1(1 bit) var
        BooleanEncoding();
    };

    typedef class AlgebraicEncoding* AlgebraicEncoding_ptr;

    class AlgebraicEncoding: public Encoding {

        friend class EncodingMgr; // expose ctors only to mgr
        friend class Compiler;    // for temporaries

    public:
        // here assignment *must* have size 1
        virtual expr::Expr_ptr expr(int* assignment);

        inline bool is_signed() const
        {
            return f_signed;
        }

        inline bool is_temporary() const
        {
            return f_temporary;
        }

        inline unsigned width() const
        {
            return f_width;
        }

    protected:
        virtual ~AlgebraicEncoding()
        {
            assert(0);
        }

        // width is number of *digits* here, dds is reserved for temporary encodings
        AlgebraicEncoding(unsigned width, bool is_signed, ADD* dds = NULL);

        unsigned f_width;
        bool f_signed;
        bool f_temporary;
    };


    // base class for finite int based
    typedef class MonolithicEncoding* MonolithicEncoding_ptr;

    class MonolithicEncoding: public Encoding {

    protected:
        virtual ~MonolithicEncoding()
        {
            assert(0);
        }

        MonolithicEncoding();

        unsigned range_repr_bits(value_t range);
    };

    typedef boost::unordered_map<value_t, expr::Expr_ptr, utils::ValueHash, utils::ValueEq> ValueExprMap;
    typedef boost::unordered_map<expr::Expr_ptr, value_t, utils::PtrHash, utils::PtrEq> ExprValueMap;

    typedef class EnumEncoding* EnumEncoding_ptr;

    class EnumEncoding: public MonolithicEncoding {

        friend class EncodingMgr; // expose ctors only to mgr

    public:
        // here assignment *must* have size 1
        virtual expr::Expr_ptr expr(int* assignment);

        virtual value_t value(expr::Expr_ptr literal);

    protected:
        virtual ~EnumEncoding()
        {
            assert(0);
        }

        EnumEncoding(const expr::ExprSet& lits);

        ValueExprMap f_v2e_map;
        ExprValueMap f_e2v_map;
    };

    typedef std::vector<Encoding_ptr> Encodings;
    typedef class ArrayEncoding* ArrayEncoding_ptr;

    class ArrayEncoding: public Encoding {

        friend class EncodingMgr; // expose ctors only to mgr

    public:
        virtual expr::Expr_ptr expr(int* assignment);

    protected:
        ArrayEncoding(Encodings elements);

        virtual ~ArrayEncoding()
        {
            assert(0);
        }

        Encodings f_elements;
    };

}; // namespace enc

#endif /* ENCODER_H */
