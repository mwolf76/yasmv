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

#include <boost/unordered_map.hpp>

#include <sat.hh>

#include <model.hh>
#include <model_mgr.hh>

#include <enc.hh>
#include <enc_mgr.hh>

#include <witness.hh>
#include <variant.hh>

#include <cmd/command.hh>

/* Model compiler */
#include <compiler/compiler.hh>

typedef boost::unordered_map<std::string, Variant> ParametersMap;

typedef enum {
    MC_FALSE,
    MC_TRUE,
    MC_UNKNOWN,
} mc_status_t;

// Engine-less algorithm base class. Engine instances are provided by strategies.
class Algorithm {

public:
    Algorithm(Command& command, Model& model);
    virtual ~Algorithm();

    /* Build encodings are perform model compilation */
    virtual void setup();

    /* Actual MC algorithm (abstract) */
    virtual void process() =0;

    // algorithm abstract param interface (key -> value map)
    void set_param(std::string key, Variant value);
    Variant& get_param(const std::string key);

    inline Compiler& compiler()
    { return f_compiler; }

    inline mc_status_t status() const;

    inline bool has_witness() const
    { return NULL != f_witness; }

    inline void set_witness(Witness &witness)
    {
        assert(NULL != &witness);
        f_witness = &witness;
    }

    inline Witness& witness() const
    { assert (NULL != f_witness); return *f_witness; }

    inline Model& model()
    { return f_model; }

    inline ModelMgr& mm()
    { return f_mm; }

    inline ExprMgr& em()
    { return f_em; }

    inline TypeMgr& tm()
    { return f_tm; }

    /* FSM */
    void assert_fsm_init(Engine& engine, step_t time,
                         group_t group = MAINGROUP);

    void assert_fsm_invar(Engine& engine, step_t time,
                          group_t group = MAINGROUP);

    void assert_fsm_trans(Engine& engine, step_t time,
                          group_t group = MAINGROUP);

    /* Generate uniqueness constraints between j-th and k-th state */
    void assert_fsm_uniqueness(Engine& engine, step_t j, step_t k,
                               group_t group = MAINGROUP);

    /* Generic formulas */
    void assert_formula(Engine& engine, step_t time, CompilationUnit& term,
                        group_t group = MAINGROUP);

private:
    /* Command */
    Command& f_command;

    /* Model */
    Model& f_model;

    // managers
    ModelMgr& f_mm;
    EncodingMgr& f_bm;
    ExprMgr& f_em;
    TypeMgr& f_tm;

    /* Model Compiler */
    Compiler f_compiler;

    /* Parameters */
    ParametersMap f_params;

    /* Formulas */
    CompilationUnits f_init;
    CompilationUnits f_invar;
    CompilationUnits f_trans;

    /* Witness */
    Witness_ptr f_witness;
};

#endif
