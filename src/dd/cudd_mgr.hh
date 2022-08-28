/**
 * @file cudd_mgr.hh
 * @brief Cudd module (CuddMgr class)
 *
 * This header contains declarations required by the Cudd Manager
 * class.
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

#ifndef CUDD_MGR_H
#define CUDD_MGR_H

#include <vector>

#include <common/common.hh>
#include <cuddObj.hh>

namespace dd {

    typedef class CuddMgr* CuddMgr_ptr;
    typedef Cudd* Cudd_ptr;

    typedef std::vector<Cudd_ptr> CuddVector;

    class CuddMgr {

    public:
        /* Generate a *new* Cudd instance */
        Cudd& dd();

        static CuddMgr& INSTANCE()
        {
            if (!f_instance) {
                f_instance = new CuddMgr();
            }
            return (*f_instance);
        }

    protected:
        CuddMgr();
        ~CuddMgr();

    private:
        static CuddMgr_ptr f_instance;
        CuddVector f_cudd_instances;
    };

}; // namespace dd

#endif
