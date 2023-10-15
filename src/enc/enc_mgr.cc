/**
 * @file enc_mgr.cc
 * @brief Encoding subsystem, Encoding Manager class implementation.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/

#include <sstream>

#include <enc.hh>
#include <enc_mgr.hh>

#include <common/logging.hh>

namespace enc {

    EncodingMgr_ptr EncodingMgr::f_instance = NULL;

    Encoding_ptr EncodingMgr::make_encoding(type::Type_ptr tp)
    {
        assert(NULL != tp);

        Encoding_ptr res { NULL };

        type::BooleanType_ptr btype;
        type::UnsignedAlgebraicType_ptr ua_type;
        type::SignedAlgebraicType_ptr sa_type;
        type::EnumType_ptr etype;
        type::ArrayType_ptr vtype;

        /* disable DD reordering */
        f_cudd.AutodynDisable();

        if ((btype = dynamic_cast<type::BooleanType_ptr>(tp))) {
            res = new BooleanEncoding();
        }

        else if ((sa_type = dynamic_cast<type::SignedAlgebraicType_ptr>(tp))) {
            res = new AlgebraicEncoding(sa_type->width(), true, sa_type->dds());
        }

        else if ((ua_type = dynamic_cast<type::UnsignedAlgebraicType_ptr>(tp))) {
            res = new AlgebraicEncoding(ua_type->width(), false, ua_type->dds());
        }

        else if ((etype = dynamic_cast<type::EnumType_ptr>(tp))) {
            res = new EnumEncoding(etype->literals());
        }

        else if ((vtype = dynamic_cast<type::ArrayType_ptr>(tp))) {
            Encodings encodings;

            assert(0 == (vtype->width() % vtype->of()->width()));
            for (unsigned i = 0; i < vtype->width() / vtype->of()->width(); ++i) {
                encodings.push_back(make_encoding(vtype->of()));
            }
            res = new ArrayEncoding(encodings);
        }

        else {
            assert(false);
        }

        /* enable DD reordering */
        f_cudd.AutodynEnable(CUDD_REORDER_SAME);

        assert(NULL != res);
        return res;
    }

    Encoding_ptr EncodingMgr::find_encoding(const expr::TimedExpr& key)
    {
        const TimedExpr2EncMap::iterator eye { f_timed_expr2enc_map.find(key) };

        if (eye != f_timed_expr2enc_map.end()) {
            return (*eye).second;
        }

        return NULL;
    }


    void EncodingMgr::register_encoding(const expr::TimedExpr& key, Encoding_ptr enc)
    {
        std::ostringstream oss;
        f_timed_expr2enc_map[key] = enc;

        dd::DDVector& bits { enc->bits() };

        unsigned i;
        dd::DDVector::iterator di;

        oss << key << " := [";
        for (i = 0, di = bits.begin(); i < bits.size();) {
            auto index { (*di).getNode()->index };
            oss
                << index;

            f_index2ucbi_map.insert(
                std::pair<int, UCBI>(index, UCBI(key.expr(), key.time(), i)));

            if (++i < bits.size()) {
                oss << ", ";
            }

            ++di;
        }
        assert(di == bits.end());
        oss << "]";

        std::string tmp(oss.str());
        DRIVEL
            << "Registered encoding: "
            << tmp
            << std::endl;
    }

    EncodingMgr::EncodingMgr()
        : f_cudd { dd::CuddMgr::INSTANCE().dd() }
        , f_em { expr::ExprMgr::INSTANCE() }
        , f_word_width { opts::OptsMgr::INSTANCE().word_width() }
    {
        const void* instance { this };

        DRIVEL
            << "Initialized EncodingMgr @ " << instance
            << ", native word size is " << f_word_width
            << std::endl;
    }

    EncodingMgr::~EncodingMgr()
    {
        const void* instance { this };

        DRIVEL
            << "Destroyed EncodingMgr @ " << instance
            << std::endl;
    }

}; // namespace enc
