/*
 * @file job.hh
 * @brief Command interpreter subsystem, Job class declaration.
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

#ifndef JOB_H
#define JOB_H

#include <boost/thread.hpp>
#include <vector>

#include <common.hh>
#include <opts_mgr.hh>

#include <cmd/command.hh>

typedef enum {
    RUNNING,
    FINISHED,
} job_status_t;

class Command;
class Job {
public:
    Job( Command& command );
    ~Job();

    Variant run();

    inline std::string id() const
    { return f_id; }

    inline job_status_t status() const
    { return f_status; }

    inline double elapsed() const
    { return (double) (clock() - f_t0) / CLOCKS_PER_SEC; }

    void join();
    void kill();

private:
    Command& f_command;
    boost::thread f_thread;

    std::string f_id;
    clock_t f_t0;

    job_status_t f_status;
};

typedef class Job* Job_ptr;
typedef std::vector<Job_ptr> Jobs;

#endif /* JOB_H */
