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
#include <sstream>

#include <enc.hh>
#include <enc_mgr.hh>

EncodingMgr_ptr EncodingMgr::f_instance = NULL;

Encoding_ptr EncodingMgr::make_encoding(Type_ptr tp)
{
    assert(NULL != tp);

    Encoding_ptr res = NULL;

    BooleanType_ptr btype;
    UnsignedAlgebraicType_ptr ua_type;
    SignedAlgebraicType_ptr sa_type;
    EnumType_ptr etype;
    ArrayType_ptr vtype;

    /* disable DD reordering */
    f_cudd.AutodynDisable();

    if ((btype = dynamic_cast<BooleanType_ptr>(tp)))
        res = new BooleanEncoding();
    else if ((sa_type = dynamic_cast<SignedAlgebraicType_ptr>(tp)))
        res = new AlgebraicEncoding(sa_type->width(), sa_type->is_fxd(), true, sa_type->dds());
    else if ((ua_type = dynamic_cast<UnsignedAlgebraicType_ptr>(tp)))
        res = new AlgebraicEncoding(ua_type->width(), ua_type->is_fxd(), false, ua_type->dds());
    else if ((etype = dynamic_cast<EnumType_ptr>(tp)))
        res = new EnumEncoding(etype->literals());
    else if ((vtype = dynamic_cast<ArrayType_ptr>(tp))) {
        Encodings encodings;

        assert( 0 == ( vtype->width() % vtype->of()->width()));
        for (unsigned i = 0; i < vtype->width() / vtype->of()->width(); ++ i) {
            encodings.push_back( make_encoding(vtype->of()));
        }
        res = new ArrayEncoding(encodings);
    }
    else assert(false); /* unexpected or unsupported */

    /* enable DD reordering */
    f_cudd.AutodynEnable(CUDD_REORDER_SAME);

    assert (NULL != res);
    return res;
}

Encoding_ptr EncodingMgr::find_encoding(const TimedExpr& key)
{
    const TimedExpr2EncMap::iterator eye
        (f_timed_expr2enc_map.find(key));

    if (eye != f_timed_expr2enc_map.end()) {
        return (*eye).second;
    }

    return NULL;
}


void EncodingMgr::register_encoding(const TimedExpr& key, Encoding_ptr enc)
{
    std::ostringstream oss;
    f_timed_expr2enc_map [ key ] = enc;

    DDVector& bits = enc->bits();

    unsigned i;
    DDVector::iterator di;

    oss << key << " := [" ;
    for (i = 0, di = bits.begin(); i < bits.size(); ) {
        int index ((*di).getNode()->index);
        oss << index;

        f_index2ucbi_map.
            insert( std::pair<int, UCBI>
                    (index, UCBI(key.expr(), key.time(), i)));

        if ( ++ i < bits.size())
            oss << ", ";

        ++ di;
    }
    assert (di == bits.end());
    oss << "]";

    std::string tmp (oss.str());
    DEBUG
        << "Registered encoding: "
        << tmp
        << std::endl;
}

EncodingMgr::EncodingMgr()
    : f_cudd(CuddMgr::INSTANCE().dd()) // this is a fresh instance
    , f_em(ExprMgr::INSTANCE())
    , f_word_width ((OptsMgr::INSTANCE().word_width()))
{
    DRIVEL
        << "Initialized EncodingMgr @ " << this
        << ", native word size is " << f_word_width
        << std::endl;
}

EncodingMgr::~EncodingMgr()
{
    DRIVEL
        << "Deinitialized EncodingMgr @ " << this
        << std::endl;
}
