/**
 * @file Base Algorithm.hh
 * @brief Base Algorithm definitions
 *
 * This header file contains definitions and services that provide the
 * foundations for all the SAT-based algorithms (i.e. reachability,
 * simulation, ltl property checking).
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

#ifndef BASE_ALGORITHM_H
#define BASE_ALGORITHM_H

#include <boost/unordered_map.hpp>

#include <sat/sat.hh>

#include <model/model.hh>
#include <model/module.hh>
#include <model/model_mgr.hh>
#include <model/compiler/compiler.hh>

#include <enc/enc.hh>
#include <enc/enc_mgr.hh>

#include <witness/witness.hh>

#include <utils/variant.hh>
#include <algorithms/exceptions.hh>

class Command;

/* Engine-less algorithm base class. Engine instances are provided by
   strategies. */
class Algorithm {

public:
    Algorithm(Command& command, Model& model);
    virtual ~Algorithm();

    /* Build encodings to perform model compilation */
    virtual void setup();

    inline Compiler& compiler()
    { return f_compiler; }

    inline bool has_witness() const
    { return NULL != f_witness; }

    inline void set_witness(witness::Witness &witness)
    { f_witness = &witness; }

    inline witness::Witness& witness() const
    { assert (NULL != f_witness); return *f_witness; }

    inline Model& model()
    { return f_model; }

    inline ModelMgr& mm()
    { return f_mm; }

    inline ExprMgr& em()
    { return f_em; }

    inline TypeMgr& tm()
    { return f_tm; }

    inline bool ok() const
    { return f_ok; }

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

    /* TimeFrame from a witness */
    void assert_time_frame(Engine& engine, step_t time, witness::TimeFrame& tf,
                           group_t group = MAINGROUP);

private:
    /* internals */
    void process_init (Expr_ptr ctx, const ExprVector& init);
    void process_invar(Expr_ptr ctx, const ExprVector& invar);
    void process_trans(Expr_ptr ctx, const ExprVector& trans);

    /* all good? */
    bool f_ok;

    /* Command */
    Command& f_command;

    /* Model */
    Model& f_model;

    /* Managers */
    ModelMgr& f_mm;
    enc::EncodingMgr& f_bm;
    ExprMgr& f_em;
    TypeMgr& f_tm;

    /* Model Compiler */
    Compiler f_compiler;

    /* Formulas */
    CompilationUnits f_init;
    CompilationUnits f_invar;
    CompilationUnits f_trans;

    /* Witness */
    witness::Witness_ptr f_witness;
};

#endif /* BASE_ALGORITHM_H */
