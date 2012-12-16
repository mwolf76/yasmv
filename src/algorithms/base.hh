/**
 *  @file Base Algorithm.hh
 *  @brief Base Algorithm
 *
 *  This module contains definitions and services that implement an
 *  abstract algorithm.
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

#ifndef BASE_ALGORITHM_H
#define BASE_ALGORITHM_H

#include <model.hh>
#include <model_mgr.hh>

#include <enc.hh>
#include <enc_mgr.hh>

#include <witness.hh>
#include <variant.hh>

/* SAT interface */
#include <sat.hh>

/* Model compiler */
#include <compilers/compiler.hh>

typedef unordered_map<string, Variant> ParametersMap;

using Minisat::group_t;
using Minisat::MAINGROUP;

using Minisat::color_t;
using Minisat::BACKGROUND;

using Minisat::SAT;
using Minisat::STATUS_SAT;
using Minisat::STATUS_UNSAT;

class Algorithm {
public:
    Algorithm(IModel& model);
    virtual ~Algorithm();

    // actual algorithm
    virtual void process() =0;

    IModel& model() const
    { return f_model; }

    // alg abstract param iface (key -> value map)
    void set_param(string key, Variant value);
    Variant& get_param(const string key);

protected:
    void assert_fsm_init (step_t time,
                          group_t group = MAINGROUP,
                          color_t color = BACKGROUND);

    void assert_fsm_trans(step_t time,
                          group_t group = MAINGROUP,
                          color_t color = BACKGROUND);

    inline ModelMgr& mm()
    { return f_mm; }

    inline ExprMgr& em()
    { return f_em; }

    inline TypeMgr& tm()
    { return f_tm; }

    inline IModel& model()
    { return f_model; }

    inline SAT& engine()
    { return f_engine; }

    inline Compiler& compiler()
    { return f_compiler; }

private:
    // managers
    ModelMgr& f_mm;
    ExprMgr& f_em;
    TypeMgr& f_tm;

    IModel& f_model;
    ADDVector f_init_adds;
    ADDVector f_trans_adds;

    // services
    void prepare();

    /* Model Compiler */
    Compiler f_compiler;

    /* The Engine */
    SAT& f_engine;

    /* Parameters */
    ParametersMap f_params;
};

#endif
