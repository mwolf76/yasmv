/*
Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

 */

/**
 * @file MCAlgorithm.hh
 *
 * @brief Expression MCAlgorithm
 *
 */

#ifndef MCALGORITHM_H
#define MCALGORITHM_H
#include <expr_walker.hh>
#include <types.hh>
#include <model.hh>
#include <inferrer.hh>

class Trace {};
typedef Trace* Trace_ptr;

// class Variant {};
typedef vector <Trace_ptr> Traces;

class MCAlgorithm {
public:
  MCAlgorithm(Model& model);
  ~MCAlgorithm();

  // actual algorithm
  void run();

  // Trace iface
  inline bool has_witness() const
  { return ! f_traces.empty(); }

  inline Traces get_traces() const
  { return f_traces; }

  // alg abtract param iface (key -> value map)
  void set_param(string& key, string& value);
  string& get_param(string& key);

protected:
  // managers
  ModelMgr& f_mm;
  ExprMgr& f_em;
  TypeMgr& f_tm;

  Model& f_model;
  Traces  f_traces;
};

#endif
