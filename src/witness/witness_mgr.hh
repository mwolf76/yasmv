/**
 * @file witness_mgr.hh
 * @brief Witness module (WitnessMgr class)
 *
 * This header file contains the declarations required by the Witness
 * Manager class.
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

#ifndef WITNESS_MGR_H
#define WITNESS_MGR_H

#include <map>
#include <vector>

#include <expr/expr.hh>

#include <model/model.hh>
#include <model/model_mgr.hh>

#include <witness/evaluator.hh>
#include <witness/witness.hh>

namespace witness {

    typedef class WitnessMgr* WitnessMgr_ptr;
    typedef std::map<expr::Atom, Witness_ptr> WitnessMap;
    typedef std::vector<Witness_ptr> WitnessList;

    class WitnessMgr {
    public:
        static WitnessMgr& INSTANCE()
        {
            if (!f_instance) {
                f_instance = new WitnessMgr();
            }
            return (*f_instance);
        }

        inline expr::ExprMgr& em() const
        {
            return f_em;
        }

        inline type::TypeMgr& tm() const
        {
            return f_tm;
        }

        inline const WitnessList& witnesses() const
        {
            return f_list;
        }

        // selects current witness
        void set_current(Witness& witness);
        void set_current(expr::Atom witness_id);

        // get currently selected witness
        Witness& current();

        // get a registered witness by id
        Witness& witness(expr::Atom id);

        // record a new witness
        void record(Witness& witness);

        // get a unique autoincrement index
        unsigned autoincrement();

        expr::Expr_ptr eval(Witness& w, expr::Expr_ptr ctx, expr::Expr_ptr body, step_t k);

    protected:
        WitnessMgr();
        ~WitnessMgr();

    private:
        static WitnessMgr_ptr f_instance;

        // Witness register internal map: id -> witness
        WitnessMap f_map;
        WitnessList f_list;

        // ref to expr manager
        expr::ExprMgr& f_em;

        // ref to type manager
        type::TypeMgr& f_tm;

        // currently selected witness uid
        expr::Atom f_curr_uid;

        Evaluator f_evaluator;

        // reserved for autoincrement index
        unsigned f_autoincrement;

        Witness f_empty_witness;
    };

}; // namespace witness

#endif
