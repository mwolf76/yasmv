/**
 *  @file array.cc
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

ArrayEncoding::ArrayEncoding(Encodings elements)
    : f_elements(elements)
{
    assert(0 < elements.size());
    for (Encodings::iterator i = elements.begin(); i != elements.end(); ++ i) {

        /* digits */
        DDVector& dv = (*i)->dv();
        f_dv.insert( f_dv.end(), dv.begin(), dv.end() );

        /* bits */
        DDVector& bits = (*i)->bits();
        f_bits.insert( f_bits.end(), bits.begin(), bits.end() );
    }
}

Expr_ptr ArrayEncoding::expr(int* assignment)
{
    ExprMgr& em(ExprMgr::INSTANCE());
    Expr_ptr acc(NULL);

    for (Encodings::const_iterator i = f_elements.begin();
         f_elements.end() != i; ++ i) {

        Encoding_ptr enc(*i);
        Expr_ptr value (enc->expr(assignment));
        acc = (NULL == acc)
            ? value
            : em.make_array_comma(acc, value)
        ;
    }
    assert(NULL != acc);
    return em.make_array( acc );
}
