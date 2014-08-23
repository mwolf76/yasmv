/**
 *  @file witness_mgr.hh
 *  @brief Witness module (WitnessMgr class)
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

#ifndef WITNESS_MGR_H
#define WITNESS_MGR_H

#include <expr.hh>

#include <model.hh>
#include <model_mgr.hh>

#include <evaluator.hh>
#include <witness.hh>

typedef class WitnessMgr *WitnessMgr_ptr;
typedef map<Atom, Witness_ptr> WitnessMap;

class WitnessMgr  {
public:
    static WitnessMgr& INSTANCE() {
        if (! f_instance) f_instance = new WitnessMgr();
        return (*f_instance);
    }

    inline ExprMgr& em() const
    { return f_em; }

    inline TypeMgr& tm() const
    { return f_tm; }

    // delegated method to the Evaluator functor
    inline const Expr_ptr eval( Witness&w, Expr_ptr ctx, Expr_ptr formula, step_t k)
    {
        value_t value = f_evaluator.process( w, ctx, formula, k);
        return ExprMgr::INSTANCE().make_const( value );
    }

    inline const WitnessMap& witnesses() const
    { return f_map; }

    // get a registered witness
    Witness& witness( Atom id );

    // register a new witness
    void register_witness( Witness& w );

protected:
    WitnessMgr();
    ~WitnessMgr();

private:
    static WitnessMgr_ptr f_instance;

    // Witness register internal map: id -> witness
    WitnessMap f_map;

    // ref to expr manager
    ExprMgr& f_em;

    // ref to type manager
    TypeMgr& f_tm;

    Evaluator f_evaluator;
};

#endif
