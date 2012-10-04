/**
 *  @file model_mgr.hh
 *  @brief Model module (ModelMgr class)
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

#ifndef MODEL_MGR_H
#define MODEL_MGR_H

#include <model.hh>
#include <inferrer.hh>

#include <expr_mgr.hh>
#include <type_mgr.hh>

typedef class ModelMgr *ModelMgr_ptr;
class ModelMgr  {

public:
    inline IModel_ptr model()
    { return &f_model; }

    void analyze();

    static ModelMgr& INSTANCE() {
        if (! f_instance) f_instance = new ModelMgr();
        return (*f_instance);
    }

    inline ExprMgr& em() const
    { return f_em; }

    inline TypeMgr& tm() const
    { return f_tm; }

protected:
    ModelMgr();
    ~ModelMgr();

private:
    static ModelMgr_ptr f_instance;

    /* local data */
    Model f_model;

    // ref to expr manager
    ExprMgr& f_em;

    // ref to type manager
    TypeMgr& f_tm;

    // ref to inferrer (used for model analysis)
    Inferrer& f_inferrer;
};

#endif
