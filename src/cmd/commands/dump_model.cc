/**
 * @file dump_model.cc
 * @brief Command `dump-model` class implementation.
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
#include <algorithm>

#include <cstdlib>
#include <cstring>

#include <cmd/commands/commands.hh>
#include <cmd/commands/dump_model.hh>

#include <model/model_mgr.hh>
#include <model/model.hh>
#include <model/module.hh>

#include <type/type.hh>

DumpModel::DumpModel(Interpreter& owner)
    : Command(owner)
    , f_output(NULL)
    , f_state(false)
    , f_init(false)
    , f_trans(false)
{}

DumpModel::~DumpModel()
{
    free(f_output);
    f_output = NULL;
}

void DumpModel::set_output(pconst_char output)
{
    if (output) {
        free(f_output);
        f_output = strdup(output);
    }
}

void DumpModel::select_state()
{
    f_state = true;
}

void DumpModel::select_init()
{
    f_init = true;
}

void DumpModel::select_trans()
{
    f_trans = true;
}

void DumpModel::dump_heading(std::ostream& os, Module& module)
{
    os
        << "MODULE "
        << module.name()
        << std::endl;
}

void DumpModel::dump_variables(std::ostream& os, Module& module)
{
    /* Variables */
    Variables variables = module.vars();
    std::for_each(std::begin(variables),
                  std::end(variables),
                  [&](std::pair<Expr_ptr, Variable_ptr> pair) {
                      auto id = pair.first;
                      auto pvar = pair.second;

                      if (pvar->is_frozen()) {
                          os
                              << "@frozen"
                              << std::endl;
                      }
                      if (pvar->is_hidden()) {
                          os
                              << "@hidden"
                              << std::endl;

                      }
                      if (pvar->is_inertial()) {
                          os
                              << "@inertial"
                              << std::endl;
                      }
                      if (pvar->is_input()) {
                          os
                              << "@input"
                              << std::endl;
                      }

                      os
                          << "VAR "
                          << id
                          << ": "
                          << pvar->type()
                          << ";"
                          << std::endl;
                  });
}

void DumpModel::dump_inits(std::ostream& os, Module& module)
{
    const ExprVector init  { module.init() };
    if (init.begin() != init.end())
        os
            << std::endl;

    for (ExprVector::const_iterator init_eye = init.begin();
         init_eye != init.end(); ++ init_eye) {

        Expr_ptr body { *init_eye };
        os
            << "INIT "
            << body
            << ";"
            << std::endl;
    }
}

void DumpModel::dump_invars(std::ostream& os, Module& module)
{
    const ExprVector invar { module.invar() };
    if (invar.begin() != invar.end())
        os
            << std::endl;

    for (ExprVector::const_iterator invar_eye = invar.begin();
         invar_eye != invar.end(); ++ invar_eye) {

        Expr_ptr body { *invar_eye };
        os
            << "INVAR "
            << body
            << ";"
            << std::endl;
    }
}

void DumpModel::dump_transes(std::ostream& os, Module& module)
{
    const ExprVector trans { module.trans() };
    if (trans.begin() != trans.end())
        os
            << std::endl;

    for (ExprVector::const_iterator trans_eye = trans.begin();
         trans_eye != trans.end(); ++ trans_eye) {

        Expr_ptr body (*trans_eye);
        os
            << "TRANS "
            << body << ";"
            << std::endl;
    }
}

std::ostream& DumpModel::get_output_stream()
{
    std::ostream* res
        (&std::cout);

    if (f_output) {
        if (f_outfile == NULL) {
            DEBUG
                << "Writing output to file `"
                << f_output
                << "`"
                << std::endl;

            f_outfile = new std::ofstream(f_output, std::ofstream::binary);
        }
        res = f_outfile;
    }

    return *res;
}

Variant DumpModel::operator()()
{
    Model& model
        (ModelMgr::INSTANCE().model());

    const Modules& modules
        (model.modules());

    std::ostream& out
        (get_output_stream());

    bool dump_all { ! f_state && ! f_init && ! f_trans };

    std::for_each(begin(modules), end(modules),
                  [this, dump_all, &out] (std::pair<Expr_ptr,
                                          Module_ptr> descriptor) {

                      Module& module
                          (*descriptor.second);

                      if (dump_all)
                          dump_heading(out, module);

                      if (dump_all || f_state)
                          dump_variables(out, module);

                      if (dump_all || f_init)
                          dump_inits(out, module);

                      if (dump_all || f_trans) {
                          dump_invars(out, module);
                          dump_transes(out, module);
                      }
                  });

    return Variant(okMessage);
}

DumpModelTopic::DumpModelTopic(Interpreter& owner)
  : CommandTopic(owner)
{}

DumpModelTopic::~DumpModelTopic()
{
  TRACE
    << "Destroyed dump-model topic"
    << std::endl;
}

void DumpModelTopic::usage()
{ display_manpage("dump-model"); }
