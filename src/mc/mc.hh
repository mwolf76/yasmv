/**
 *  @file MC Algorithm.hh
 *  @brief MC Algorithm
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
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

#ifndef MCALGORITHM_H
#define MCALGORITHM_H

#include <model.hh>
#include <model_mgr.hh>

#include <enc.hh>
#include <enc_mgr.hh>

#include <trace.hh>
#include <variant.hh>

typedef unordered_map<string, Variant> ParametersMap;

typedef enum {
    MC_FALSE,
    MC_TRUE,
    MC_UNKNOWN,
} mc_status_t;

class MCAlgorithm {
public:
    MCAlgorithm(IModel& model, Expr_ptr property);
    virtual ~MCAlgorithm();

    // actual algorithm
    virtual void process() =0;

    IModel& model() const
    { return f_model; }

    // Witness iface
    inline mc_status_t status() const
    { return f_status; }

    inline bool has_witness() const
    { return NULL != f_witness; }

    inline Trace& get_witness() const
    {
        assert (has_witness());
        return *f_witness;
    }

    // alg abstract param iface (key -> value map)
    void set_param(string key, Variant value);
    Variant& get_param(const string key);

protected:
    // managers
    ModelMgr& f_mm;
    ExprMgr& f_em;
    TypeMgr& f_tm;

    // model and property
    IModel& f_model;
    Expr_ptr f_property;

    // ctx witness
    Trace_ptr f_witness;
    mc_status_t f_status;

    // algorithm specific params
    ParametersMap f_params;
};

#endif
