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

// #define DEBUG_ENC

// static initialization
EncodingMgr_ptr EncodingMgr::f_instance = NULL;

IEncoding_ptr EncodingMgr::make_encoding(Type_ptr tp)
{
    IEncoding_ptr res = NULL;

    BooleanType_ptr btype;
    UnsignedAlgebraicType_ptr ua_type;
    SignedAlgebraicType_ptr sa_type;
    EnumType_ptr etype;
    ArrayType_ptr vtype;

    assert(NULL != tp);

    // disable reordering
    f_cudd.AutodynDisable();

    if (NULL != (btype = dynamic_cast<BooleanType_ptr>(tp))) {
        #ifdef DEBUG_ENC
        DEBUG << "Encoding " << btype << endl;
        #endif
        res = new BooleanEncoding();
    }
    else if (NULL != (sa_type = dynamic_cast<SignedAlgebraicType_ptr>(tp))) {
        #ifdef DEBUG_ENC
        DEBUG << "Encoding " << sa_type << endl;
        #endif
        res = new AlgebraicEncoding(sa_type->width(), 0, true, sa_type->dds());
    }
    else if (NULL != (ua_type = dynamic_cast<UnsignedAlgebraicType_ptr>(tp))) {
        #ifdef DEBUG_ENC
        DEBUG << "Encoding " << ua_type << endl;
        #endif
        res = new AlgebraicEncoding(ua_type->width(), 0, false, ua_type->dds());
    }
    else if (NULL != (etype = dynamic_cast<EnumType_ptr>(tp))) {
        #ifdef DEBUG_ENC
        DEBUG << "Encoding " << etype << endl;
        #endif
        res = new EnumEncoding(etype->literals());
    }
    else if (NULL != (vtype = dynamic_cast<ArrayType_ptr>(tp))) {
        #ifdef DEBUG_ENC
        DEBUG << "Encoding " << vtype << endl;
        #endif
        Encodings encs;

        assert( 0 == ( vtype->width() % vtype->of()->width()));
        for (unsigned i = 0; i < vtype->width() / vtype->of()->width(); ++ i) {
            encs.push_back( make_encoding(vtype->of()));
        }
        res = new ArrayEncoding(encs);
    }
    else assert(false); /* unexpected or unsupported */

    // reenable reordering
    f_cudd.AutodynEnable(CUDD_REORDER_SAME);

    assert (NULL != res);
    return res;
}

void EncodingMgr::register_encoding(const FQExpr& fqexpr, IEncoding_ptr enc)
{
    f_fqexpr2enc_map [ fqexpr ] = enc;

    DDVector& bits = enc->bits();

    unsigned i;
    DDVector::iterator di;

    for (i = 0, di = bits.begin(); i < bits.size(); ++ i, ++ di) {
        f_index2ucbi_map.
            insert(pair<int, UCBI> ((*di).getNode()->index,
                                    UCBI(fqexpr.ctx(), fqexpr.expr(), fqexpr.time(), i)));
    }
    assert (di == bits.end());
}

EncodingMgr::EncodingMgr()
    : f_cudd(CuddMgr::INSTANCE().dd()) // this is a fresh instance
    , f_em(ExprMgr::INSTANCE())
    , f_word_width ((OptsMgr::INSTANCE().word_width()))
{
    unsigned base = 2;

    f_base = f_cudd.constant( base );
    f_msb  = f_cudd.constant( ::msb (base - 1));

    DRIVEL << "Initialized EncodingMgr @ " << this
           << ", array " << f_word_width << " bits indexes"
           << endl;
}

EncodingMgr::~EncodingMgr()
{
    DRIVEL << "Deinitialized EncodingMgr @ " << this << endl;
}
