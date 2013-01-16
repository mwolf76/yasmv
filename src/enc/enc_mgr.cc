/**
 *  @file enc_mgr.cc
 *  @brief Encoder module (EncMgr class)
 *
 *  This module contains definitions and services that implement an
 *  encoder for symbols. For each symbol a boolean encoding is
 *  maintained, the encoder takes care of ADD variables definitions
 *  and is provides mapback services as well.
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

#include <enc.hh>
#include <enc_mgr.hh>

// static initialization
EncodingMgr_ptr EncodingMgr::f_instance = NULL;

IEncoding_ptr EncodingMgr::make_encoding(Type_ptr tp)
{
    IEncoding_ptr res = NULL;

    BooleanType_ptr btype;
    SignedAlgebraicType_ptr sa_type;
    UnsignedAlgebraicType_ptr ua_type;
    SignedFixedAlgebraicType_ptr sfa_type;
    UnsignedFixedAlgebraicType_ptr ufa_type;
    EnumType_ptr etype;
    ArrayType_ptr vtype;

    assert(NULL != tp);

    if (NULL != (btype = dynamic_cast<BooleanType_ptr>(tp))) {
        DEBUG << "Encoding boolean " << btype << endl;
        res = new BooleanEncoding();
    }
    else if (NULL != (sa_type = dynamic_cast<SignedAlgebraicType_ptr>(tp))) {
        DEBUG << "Encoding signed algebraic " << sa_type << endl;
        res = new AlgebraicEncoding(sa_type->width(), 0, true, sa_type->dds());
    }
    else if (NULL != (ua_type = dynamic_cast<UnsignedAlgebraicType_ptr>(tp))) {
        DEBUG << "Encoding unsigned algebraic " << ua_type << endl;
        res = new AlgebraicEncoding(ua_type->width(), 0, false, ua_type->dds());
    }
    else if (NULL != (sfa_type = dynamic_cast<SignedFixedAlgebraicType_ptr>(tp))) {
        DEBUG << "Encoding signed fixed-point algebraic " << sfa_type << endl;
        res = new AlgebraicEncoding(sfa_type->width(), sfa_type->fract(),
                                    true, sfa_type->dds());
    }
    else if (NULL != (ufa_type = dynamic_cast<UnsignedFixedAlgebraicType_ptr>(tp))) {
        DEBUG << "Encoding unsigned fixed-point algebraic " << ufa_type << endl;
        res = new AlgebraicEncoding(ufa_type->width(), ufa_type->fract(),
                                    false, sfa_type->dds());
    }
    else if (NULL != (etype = dynamic_cast<EnumType_ptr>(tp))) {
        DEBUG << "Encoding enum " << etype << endl;
        res = new EnumEncoding(etype->literals());
    }
    else if (NULL != (vtype = dynamic_cast<ArrayType_ptr>(tp))) {
        DEBUG << "Encoding array " << vtype << endl;
        Encodings encs;
        for (unsigned i =0; i < vtype->size(); ++ i) {
            encs.push_back(make_encoding(vtype->of()));
        }
        res = new ArrayEncoding(encs);
    }

    else assert(0); /* unexpected or unsupported */

    assert (NULL != res);
    return res;
}

void EncodingMgr::register_encoding(const FQExpr& fqexpr, IEncoding_ptr enc)
{
    f_fqexpr2enc_map [ fqexpr ] = enc;

    /* keep CBI as well */
    DDVector& bits = enc->bits();

    unsigned i;
    DDVector::iterator di;

    for (i = 0, di = bits.begin(); i < bits.size(); ++ i, ++ di) {
        f_index2ucbi_map.
            insert(pair<int, UCBI> ((*di).getNode()->index,
                                    UCBI(fqexpr.ctx(), fqexpr.expr(),
                                         fqexpr.time(), i)));
    }
    assert (di == bits.end());
}

EncodingMgr::EncodingMgr()
    : f_cudd(CuddMgr::INSTANCE().dd()) // this is a fresh instance
    , f_em(ExprMgr::INSTANCE())
{
    // f_width = 8; // experimental, 8 nibbles (=32 bits)

    f_base = f_cudd.constant(0x10); // 0x10 = nibble size
    f_full = f_cudd.constant(0xF);
    f_msb  = f_cudd.constant(0x8);

    DRIVEL << "Initialized EncodingMgr @ " << this << endl;
}

EncodingMgr::~EncodingMgr()
{
    DRIVEL << "Deinitialized EncodingMgr @ " << this << endl;
}
