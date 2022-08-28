/**
 * @file sat/engine_mgr.cc
 * @brief SAT interface subsystem implementation. Engine Mgr class implementation.
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

#include <sat/engine.hh>
#include <sat/engine_mgr.hh>

#include <csignal>

namespace sat {

    EngineMgr_ptr EngineMgr::f_instance { NULL };

    EngineMgr::EngineMgr()
    {
        const void* instance { this };

        DRIVEL
            << "Initialized EngineMgr @ " << instance
            << std::endl;
    }

    EngineMgr::~EngineMgr()
    {
        const void* instance { this };

        DRIVEL
            << "Destroyed EngineMgr @ "
            << instance
            << std::endl;
    }

    void EngineMgr::register_instance(Engine_ptr engine)
    {
        boost::mutex::scoped_lock lock { f_mutex };

        /* this engine is not yet registered */
        assert(f_engines.find(engine) == f_engines.end());

        DEBUG
            << "Registered engine instance"
            << "@"
            << engine
            << std::endl;

        f_engines.insert(engine);
    }

    void EngineMgr::unregister_instance(Engine_ptr engine)
    {
        boost::mutex::scoped_lock lock { f_mutex };

        /* this engine is registered */
        assert(f_engines.find(engine) != f_engines.end());

        DEBUG
            << "Unregistered engine instance"
            << "@"
            << engine
            << std::endl;

        f_engines.erase(engine);
    }

    void EngineMgr::interrupt()
    {
        boost::mutex::scoped_lock lock { f_mutex };

        EngineSet::iterator esi;
        for (esi = begin(f_engines); end(f_engines) != esi; ++esi) {
            Engine_ptr pe { *esi };
            pe->interrupt();
        }
    }

    void EngineMgr::dump_stats(std::ostream& os)
    {
        boost::mutex::scoped_lock lock { f_mutex };

        if (f_engines.empty()) {
            /* nop */
        } else {
            EngineSet::iterator esi;
            for (esi = f_engines.begin(); f_engines.end() != esi; ++esi) {
                Engine_ptr pe { *esi };

                os
                    << (*pe)
                    << std::endl;
            }

            os
                << std::endl;
        }
    }

}; // namespace sat
