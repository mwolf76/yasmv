/**
 * @file sat/engine_mgr.hh
 * @brief SAT interface, Engine Mgr class declaration.
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

#ifndef SAT_ENGINE_MGR_H
#define SAT_ENGINE_MGR_H

#include <boost/thread/mutex.hpp>
#include <sat/typedefs.hh>

namespace sat {

    class EngineMgr {

    public:
        /**
     * @brief Signals an interrupt to all running instances
     */
        void interrupt();

        /**
     * @brief Requires a stats printout from all existing instances
     */
        void dump_stats(std::ostream& os);

        static EngineMgr& INSTANCE()
        {
            if (!f_instance) {
                f_instance = new EngineMgr();
            }
            return (*f_instance);
        }

    protected:
        EngineMgr();
        ~EngineMgr();

    private: /* private interface, reserved to Engine instances. */
        friend class Engine;

        /**
     * @brief Registers a new engine instance. Used by Engine ctor
     */
        void register_instance(Engine_ptr engine);

        /**
     * @brief Unregisters an existing engine instance. Used by Engine dctor.
     */
        void unregister_instance(Engine_ptr engine);

        static EngineMgr_ptr f_instance;
        EngineSet f_engines;

        boost::mutex f_mutex;
    };

}; // namespace sat

#endif /* SAT_ENGINE_MGR_H */
