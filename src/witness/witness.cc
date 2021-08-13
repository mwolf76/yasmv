/**
 * @file witness.cc
 * @brief Base witness class implementation.
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

#include <witness.hh>

#include <utils/misc.hh>

#include <cstring>
#include <sstream>

namespace witness {

    TimeFrame::TimeFrame(Witness& owner)
        : f_owner(owner)
    {}

    TimeFrame::~TimeFrame()
    {}

    TimeFrame& Witness::operator[](step_t i)
    {
        if (i < f_j) {
            throw IllegalTime(i);
        }

        i -= f_j;
        assert(0 <= i);

        if (f_frames.size() - 1 < i) {
            throw IllegalTime(f_j + i);
        }

        return *f_frames[i];
    }

    /* Retrieves value for expr, throws an exception if no value exists. */
    expr::Expr_ptr TimeFrame::value(expr::Expr_ptr expr)
    {
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };

        // symbol is defined in witness' language
        expr::ExprVector& lang(f_owner.lang());

        assert(find(lang.begin(), lang.end(), expr) != lang.end());

        Expr2ExprMap::iterator eye;

        eye = f_map.find(expr);
        if (f_map.end() == eye) {
            throw NoValue(expr);
        }

        expr::Expr_ptr vexpr { (*eye).second };
        Expr2FormatMap::iterator format_eye { f_format_map.find(expr) };

        if (f_format_map.end() == format_eye) {
            assert(false); /* unreachable */
        }

        /* got value format */
        value_format_t fmt { (*format_eye).second };

        /* force conversion of constants to required format.
         * TODO: extend this to sets */
        if (em.is_bool_const(vexpr)) {
            return vexpr;
        }

        else if (em.is_int_const(vexpr)) {
            switch (fmt) {
                case FORMAT_BINARY:
                    vexpr = em.make_bconst(vexpr->value());
                    break;

                case FORMAT_OCTAL:
                    vexpr = em.make_oconst(vexpr->value());
                    break;

                case FORMAT_HEXADECIMAL:
                    vexpr = em.make_hconst(vexpr->value());
                    break;

                default:
                    //case FORMAT_DECIMAL:
                    vexpr = em.make_const(vexpr->value());
            }
        }

        return vexpr;
    }

    /* Returns true iff expr has an assigned value within this time frame. */
    bool TimeFrame::has_value(expr::Expr_ptr expr)
    {
        // symbol is defined in witness' language
        expr::ExprVector& lang { f_owner.lang() };

        // FIXME: proper exception
        if (lang.end() == std::find(lang.begin(), lang.end(), expr)) {
            std::cerr << expr << std::endl;
            assert(false);
        }

        Expr2ExprMap::iterator eye;

        eye = f_map.find(expr);
        return (f_map.end() != eye);
    }

    /* Sets value for expr */
    void TimeFrame::set_value(expr::Expr_ptr expr, expr::Expr_ptr value, value_format_t format)
    {
        assert(value);

        DEBUG
            << expr
            << " := "
            << value
            << std::endl;

        // symbol is defined in witness' language
        expr::ExprVector& lang { f_owner.lang() };

        if (find(lang.begin(), lang.end(), expr) == lang.end()) {
            throw UnknownIdentifier(expr);
        }

        /* populate both maps at the same time. This ensures consistency. */
        f_map.insert(std::pair<expr::Expr_ptr, expr::Expr_ptr>(expr, value));
        f_format_map.insert(std::pair<expr::Expr_ptr, value_format_t>(expr, format));
    }

    expr::ExprVector TimeFrame::assignments()
    {
        expr::ExprMgr& em { expr::ExprMgr::INSTANCE() };
        expr::ExprVector res;

        expr::ExprVector& lang { f_owner.lang() };
        expr::ExprVector::const_iterator i { lang.begin() };

        while (i != lang.end()) {
            expr::Expr_ptr symb { *i };

            ++i;
            try {
                res.push_back(em.make_eq(symb, value(symb)));
            }

            catch (NoValue& nv) {
            }
        }

        return res;
    }

    Witness::Witness(sat::Engine_ptr pe, expr::Atom id, expr::Atom desc, step_t j)
        : f_id(id)
        , f_desc(desc)
        , f_j(j)
        , p_engine(pe)
    {
        DEBUG
            << "Created new witness: "
            << f_id
            << ", starting at time "
            << f_j
            << std::endl;
    }

    TimeFrame& Witness::extend(Witness& w)
    {
        // seizing ownership of the TimeFrames from w
        TimeFrame_ptr last { NULL };

        for (TimeFrames::iterator i = w.frames().begin(); i != w.frames().end(); ++i) {
            f_frames.push_back(*i);
            last = (*i);
        }
        w.f_frames.clear();

        assert(last);
        return *last;
    }

    TimeFrame& Witness::extend()
    {
        TimeFrame_ptr tf { new TimeFrame(*this) };
        f_frames.push_back(tf);

        step_t last { 1 + last_time() };
        DEBUG << "Added empty TimeFrame " << last
              << " to witness " << id()
              << " @" << tf
              << std::endl;

        assert(tf);
        return *tf;
    }

    /* Retrieves value for expr, throws an exception if no such value exists. */
    expr::Expr_ptr Witness::value(expr::Expr_ptr expr, step_t time)
    {
        if (time < first_time() || time > last_time()) {
            throw IllegalTime(time);
        }

        expr::Expr_ptr vexpr { f_frames[time]->value(expr) };
        return vexpr;
    }

    /* Returns true iff expr has an assigned value within this time frame. */
    bool Witness::has_value(expr::Expr_ptr expr, step_t time)
    {
        if (time < first_time() ||
            time > last_time()) {
            return false;
        }

        return f_frames[time]->has_value(expr);
    }

    /* Engine registration can be done only once */
    void Witness::register_engine(sat::Engine& e)
    {
        assert(!p_engine);
        p_engine = &e;
    }

} // namespace witness
