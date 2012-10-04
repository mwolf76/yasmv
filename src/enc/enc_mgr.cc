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
    assert(NULL != tp);
    IEncoding_ptr res = NULL;
    IntegerType_ptr itype;
    IntRangeType_ptr rtype;

    if (NULL != dynamic_cast<BooleanType_ptr>(tp)) {
        res = new BooleanEncoding();
    }
    else if (NULL != (itype = dynamic_cast<IntegerType_ptr>(tp))) {
        res = new IntEncoding(itype->size(), itype->is_signed());
    }
    else if (NULL != (rtype = dynamic_cast<IntRangeType_ptr>(tp))) {
        res = new RangeEncoding(rtype->min(), rtype->max());
    }
    // tODO: more here...

    else assert(0); /* unexpected or unsupported */

    assert (NULL != res);
    return res;
}

IEncoding_ptr EncodingMgr::find_encoding(ADD add)
{
    // const ADD2Enc::iterator eye = f_add2enc_map.find(add);
    // if (eye != f_groups_map.end()) {
    //     return (*eye).second;
    // }

    // assert(0);
}

// TODO: review...
// this is a private member of Encoding to allow for inplace ADD building
ADD Encoding::make_integer_encoding(unsigned nbits, bool is_signed)
{
    bool msb = true;

    // in place
    ADD& add_res = f_add;

    assert(0 < nbits);
    unsigned i = 0;

    while (i < nbits) {
        ADD two = f_mgr.dd().constant(2);
        if (msb && is_signed) {
            msb = false;
            two = two.Negate(); // MSB is -2^N in 2's complement
        }
        add_res *= two;

        // create var and book it
        ADD add_var = f_mgr.dd().addVar();
        f_bits.push_back(add_var);

        // add it to the encoding
        add_res += add_var;

        ++ i;
    }
}

EncodingMgr::EncodingMgr()
    : f_cudd(CuddMgr::INSTANCE().dd())
{
    DRIVEL << "Initialized EncodingMgr @ " << this << endl;
}

EncodingMgr::~EncodingMgr()
{
    DRIVEL << "Deinitialized EncodingMgr @ " << this << endl;
}
