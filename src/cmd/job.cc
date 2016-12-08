/*
 * @file job.cc
 * @brief Command interpreter subsystem implementation.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
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

#include <sstream>

#include <command.hh>
#include <job.hh>

static uint32_t f_job_index = 0;

Job::Job( Command& command )
    : f_command(command)
    , f_thread(&Job::run, this)
    , f_t0(clock())
{
    std::ostringstream oss;

    oss
        << "J"
        << ++ f_job_index;

    f_id = oss.str();
}

void Job::join()
{
    if (f_status != FINISHED)
        f_thread.join();
}

void Job::kill()
{
    if (f_status != FINISHED)
        f_command.kill();
}

Variant Job::run()
{
    Variant res;
    f_status = RUNNING;

    res = f_command();

    f_status = FINISHED;
    return res;
}

