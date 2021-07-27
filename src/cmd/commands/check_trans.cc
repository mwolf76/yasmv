/**
 * @file check_trans.cc
 * @brief Command `check-trans` class implementation.
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

#include <cstdlib>
#include <cstring>

#include <cmd/commands/commands.hh>
#include <cmd/commands/check_trans.hh>

#include <algorithms/fsm/fsm.hh>

namespace cmd {

CheckTrans::CheckTrans(Interpreter& owner)
    : Command(owner)
    , f_out(std::cout)
{}

CheckTrans::~CheckTrans()
{}

void CheckTrans::add_constraint(expr::Expr_ptr constraint)
{
    f_constraints.push_back(constraint);
}

bool CheckTrans::check_requirements()
{
    ModelMgr& mm
        (ModelMgr::INSTANCE());

    Model& model
        (mm.model());

    if (0 == model.modules().size()) {
        f_out
            << wrnPrefix
            << "Model not loaded."
            << std::endl;

        return false;
    }

    return true;
}

utils::Variant CheckTrans::operator()()
{
    opts::OptsMgr& om
        (opts::OptsMgr::INSTANCE());

    utils::Variant res { false };

    if (check_requirements()) {
        fsm::CheckTransConsistency check_trans
            { *this, ModelMgr::INSTANCE().model() } ;
        check_trans.process(f_constraints);

        switch (check_trans.status()) {
        case fsm::fsm_consistency_t::FSM_CONSISTENCY_OK:
            if (! om.quiet())
                f_out
                    << outPrefix;
            f_out
                << "Transition relation consistency check ok."
                << std::endl;

            res = true;
            break;

        case fsm::fsm_consistency_t::FSM_CONSISTENCY_KO:
            if (! om.quiet())
                f_out
                    << outPrefix;
            f_out
                << "Transition relation consistency check failed."
                << std::endl;
            break;

        case fsm::fsm_consistency_t::FSM_CONSISTENCY_UNDECIDED:
            if (! om.quiet())
                f_out
                    << outPrefix;
            f_out
                << "Could not decide transition relation consistency check."
                << std::endl;
            break;

        default: assert( false ); /* unreachable */
        } /* switch */
    }

    return res;
}

CheckTransTopic::CheckTransTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

CheckTransTopic::~CheckTransTopic()
{
    TRACE
        << "Destroyed check-trans topic"
        << std::endl;
}

void CheckTransTopic::usage()
{ display_manpage("check-trans"); }

};
