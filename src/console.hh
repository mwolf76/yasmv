/**
 * @file console.hh
 * @brief Command line options management
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 **/

#ifndef CONSOLE_H
#define CONSOLE_H

/* logging support using ezlogger (cfr. http://axter.com/ezlogger/) */
#include <logging.hh>

class ConsoleMgr;
typedef ConsoleMgr* ConsoleMgr_ptr;

// system-wide loggers
#define ERR  ConsoleMgr::INSTANCE().err()
#define WARN ConsoleMgr::INSTANCE().warn()
#define TRACE ConsoleMgr::INSTANCE().trace()
#define INFO ConsoleMgr::INSTANCE().info()
#define DEBUG  ConsoleMgr::INSTANCE().debug()
#define DRIVEL ConsoleMgr::INSTANCE().drivel()

class ConsoleMgr {

public:
    static ConsoleMgr& INSTANCE() {
        if (! f_instance)
            f_instance = new ConsoleMgr();
        return (*f_instance);
    }

    axter::ezlogger<>& err();
    axter::ezlogger<>& warn();
    axter::ezlogger<>& trace();
    axter::ezlogger<>& info();
    axter::ezlogger<>& debug();
    axter::ezlogger<>& drivel();

protected:
    ConsoleMgr();

private:
    static ConsoleMgr_ptr f_instance;

    axter::ezlogger<> f_err;
    axter::ezlogger<> f_warn;
    axter::ezlogger<> f_trace;
    axter::ezlogger<> f_info;
    axter::ezlogger<> f_debug;
    axter::ezlogger<> f_drivel;
};

#endif
