#include <query/query.hh>
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

    bool Diameter::check_requirements() const
    {
        model::ModelMgr& mm { model::ModelMgr::INSTANCE() };
        mm.require_valid();
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
        opts::OptsMgr& om { opts::OptsMgr::INSTANCE() };
        bool res { false };

        if (check_requirements()) {
            query::QuerySpec spec; spec.operation = query::Operation::diameter;
            const auto result = query::checked(spec);
            const step_t value = result.status == query::ExecutionStatus::completed ? result.value : UINT_MAX;
            if (value == UINT_MAX) {
                f_out << "FSM diameter could not be decided." << std::endl;
                return utils::Variant(unknownMessage);
            }

            if (!om.quiet()) {
                f_out
                    << outPrefix;
            }

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
