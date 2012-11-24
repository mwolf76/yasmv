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
    // Expr_ptr repr = tp->repr();

    IEncoding_ptr res = NULL;

    BooleanType_ptr btype;
    AlgebraicType_ptr atype;
    EnumType_ptr etype;

    if (NULL != (btype = dynamic_cast<BooleanType_ptr>(tp))) {
        // DEBUG << "Encoding Boolean " << repr << endl;
        res = new BooleanEncoding();
    }
    else if (NULL != (atype = dynamic_cast<AlgebraicType_ptr>(tp))) {
        // DEBUG << "Encoding Algebraic " << repr << endl;
        res = new AlgebraicEncoding(atype->width(), atype->is_signed(), atype->dds());
    }
    else if (NULL != (etype = dynamic_cast<EnumType_ptr>(tp))) {
        // DEBUG << "Encoding Enum " << repr << endl;
        res = new EnumEncoding(etype->literals());
    }

    else assert(0); /* unexpected or unsupported */

    assert (NULL != res);
    return res;
}

EncodingMgr::EncodingMgr()
    : f_cudd(CuddMgr::INSTANCE().dd())
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
