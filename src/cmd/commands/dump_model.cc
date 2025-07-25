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

#include <model/model.hh>
#include <model/model_mgr.hh>
#include <model/module.hh>

#include <type/type.hh>

#include <utils/logging.hh>

namespace cmd {

    DumpModel::DumpModel(Interpreter& owner)
        : Command(owner)
        , f_output(nullptr)
        , f_state(false)
        , f_init(false)
        , f_trans(false)
    {}

    DumpModel::~DumpModel()
    {
        free(f_output);
        f_output = nullptr;
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

    void DumpModel::dump_heading(std::ostream& os, const model::Module& module)
    {
        os
                << "#word-width"
                << opts::OptsMgr::INSTANCE().word_width()
                << std::endl;

        os
            << "MODULE "
            << module.name()
            << std::endl;
    }

    void DumpModel::dump_variables(std::ostream& os, const model::Module& module)
    {
        /* Variables */
        symb::Variables variables { module.vars() };
        std::for_each(variables.begin(), variables.end(),
                      [&](const std::pair<expr::Expr_ptr, symb::Variable_ptr> &pair) {
                                  const auto id { pair.first };
                                  const auto var_ptr { pair.second };

                                  if (var_ptr->is_frozen()) {
                                      os
                                              << "#frozen"
                                              << std::endl;
                                  }
                                  if (var_ptr->is_hidden()) {
                                      os
                                              << "#hidden"
                                              << std::endl;
                                  }
                                  if (var_ptr->is_inertial()) {
                                      os
                                              << "#inertial"
                                              << std::endl;
                                  }
                                  if (var_ptr->is_input()) {
                                      os
                                              << "#input"
                                              << std::endl;
                                  }

                                  os
                                          << "VAR "
                                          << id
                                          << ": "
                                          << var_ptr->type()
                                          << ";"
                                          << std::endl;
                              });
    }

    void DumpModel::dump_init(std::ostream& os, const model::Module& module)
    {
        const expr::ExprVector init { module.init() };
        if (init.begin() != init.end()) {
            os
                << std::endl;
        }

        for (expr::ExprVector::const_iterator init_eye = init.begin();
             init_eye != init.end(); ++init_eye) {

            expr::Expr_ptr body { *init_eye };
            os
                << "INIT "
                << body
                << ";"
                << std::endl;
        }
    }

    void DumpModel::dump_invar(std::ostream& os, const model::Module& module)
    {
        const expr::ExprVector invar { module.invar() };
        if (invar.begin() != invar.end()) {
            os
                << std::endl;
        }

        for (expr::ExprVector::const_iterator invar_eye = invar.begin();
             invar_eye != invar.end(); ++invar_eye) {

            expr::Expr_ptr body { *invar_eye };
            os
                << "INVAR "
                << body
                << ";"
                << std::endl;
        }
    }

    void DumpModel::dump_trans(std::ostream& os, const model::Module& module)
    {
        const expr::ExprVector trans { module.trans() };
        if (trans.begin() != trans.end()) {
            os
                << std::endl;
        }

        for (expr::ExprVector::const_iterator trans_eye = trans.begin();
             trans_eye != trans.end(); ++trans_eye) {

            expr::Expr_ptr body { *trans_eye };
            os
                << "TRANS "
                << body << ";"
                << std::endl;
        }
    }

    std::ostream& DumpModel::get_output_stream()
    {
        std::ostream* res { &std::cout };

        if (f_output) {
            if (f_outfile == nullptr) {
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

    utils::Variant DumpModel::operator()()
    {
        model::ModelMgr& mm { model::ModelMgr::INSTANCE() };
        model::Model& model { mm.model() };
        const model::Modules& modules { model.modules() };

        std::ostream& out(get_output_stream());
        bool dump_all { !f_state && !f_init && !f_trans };

        std::for_each(modules.begin(), modules.end(),
                      [this, dump_all, &out](const std::pair<expr::Expr_ptr,
                                                              model::Module_ptr>
                                             &descriptor) {
                                  model::Module& module { *descriptor.second };

                                  if (dump_all) {
                                      dump_heading(out, module);
                                  }

                                  if (dump_all || f_state) {
                                      dump_variables(out, module);
                                  }

                                  if (dump_all || f_init) {
                                      dump_init(out, module);
                                  }

                                  if (dump_all || f_trans) {
                                      dump_invar(out, module);
                                      dump_trans(out, module);
                                  }
                              });

        return utils::Variant(okMessage);
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
    {
        display_manpage("dump-model");
    }

}; // namespace cmd
