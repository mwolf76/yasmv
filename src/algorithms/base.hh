/**
 *  @file Base Algorithm.hh
 *  @brief Base Algorithm
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

#include <sat.hh>

#include <model.hh>
#include <model_mgr.hh>

#include <enc.hh>
#include <enc_mgr.hh>

#include <witness.hh>
#include <variant.hh>

/* Model compiler */
#include <compiler/compiler.hh>

typedef unordered_map<string, Variant> ParametersMap;

typedef enum {
    MC_FALSE,
    MC_TRUE,
    MC_UNKNOWN,
} mc_status_t;

class Algorithm {

public:
    Algorithm(IModel& model, ostream& os = std::cout);
    virtual ~Algorithm();

    /* Build encodings */
    virtual void prepare();

    /* Perform compilation */
    virtual void compile();

    /* Actual MC algorithm (abstract) */
    virtual void process() =0;

    // algorithm abstract param interface (key -> value map)
    void set_param(string key, Variant value);
    Variant& get_param(const string key);

    inline Compiler& compiler()
    { return f_compiler; }

    mc_status_t status() const;

    inline bool has_witness() const
    { return NULL != f_witness; }

    inline void set_witness(Witness &witness)
    {
        assert(NULL != &witness);
        f_witness = &witness;
    }

    inline Witness& witness() const
    { assert (NULL != f_witness); return *f_witness; }

    inline IModel& model()
    { return f_model; }

protected:
    inline ModelMgr& mm()
    { return f_mm; }

    inline ExprMgr& em()
    { return f_em; }

    inline TypeMgr& tm()
    { return f_tm; }

    inline SAT& engine()
    { return f_engine; }

    inline ostream& os()
    { return f_os; }

    /* FSM */
    void assert_fsm_init(step_t time,
                         group_t group = MAINGROUP,
                         color_t color = BACKGROUND);

    void assert_fsm_invar(step_t time,
                          group_t group = MAINGROUP,
                          color_t color = BACKGROUND);

    void assert_fsm_trans(step_t time,
                          group_t group = MAINGROUP,
                          color_t color = BACKGROUND);

    /* Generic formulas */
    void assert_formula(step_t time, ADDVector& adds,
                        group_t group = MAINGROUP,
                        color_t color = BACKGROUND);

private:
    /* Model */
    IModel& f_model;

    // output
    ostream& f_os;

    // managers
    ModelMgr& f_mm;
    ExprMgr& f_em;
    TypeMgr& f_tm;

    /* Model Compiler */
    Compiler f_compiler;

    /* The Engine */
    SAT& f_engine;

    /* Parameters */
    ParametersMap f_params;

    ADDVector f_init_adds;
    ADDVector f_invar_adds;
    ADDVector f_trans_adds;

    Witness_ptr f_witness;
};

#endif
