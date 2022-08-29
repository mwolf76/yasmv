/**
 * @file diameter.cc
 * @brief Command `diameter` class implementation.
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
#include <cmd/commands/diameter.hh>

#include <algorithms/fsm/fsm.hh>

namespace cmd {

    Diameter::Diameter(Interpreter& owner)
        : Command(owner)
        , f_out(std::cout)
    {}

    Diameter::~Diameter()
    {}

    bool Diameter::check_requirements()
    {
        model::ModelMgr& mm { model::ModelMgr::INSTANCE() };
        model::Model& model { mm.model() };

        if (0 == model.modules().size()) {
            f_out
                << wrnPrefix
                << "Model not loaded."
                << std::endl;

            return false;
        }

        return true;
    }

    utils::Variant Diameter::operator()()
    {
        bool res { false };

        if (check_requirements()) {
            fsm::ComputeDiameter computeDiameter {
                *this, model::ModelMgr::INSTANCE().model()
            };

            computeDiameter.process();
            step_t value = computeDiameter.diameter();

            f_out
                << "FSM diameter is "
                << std::dec
                << value
                << std::endl;

            res = (value != UINT_MAX);
        }

        return utils::Variant { res ? okMessage : errMessage };
    }

    DiameterTopic::DiameterTopic(Interpreter& owner)
        : CommandTopic(owner)
    {}

    DiameterTopic::~DiameterTopic()
    {}

    void DiameterTopic::usage()
    {
        display_manpage("diameter");
    }

}; // namespace cmd
