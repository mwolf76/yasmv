/*
 * @file job.hh
 * @brief Command interpreter subsystem related classes and definitions.
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
 *  Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/
#ifndef JOB_H
#define JOB_H

#include <common.hh>
#include <opts.hh>

#include <cmd/icommand.hh>

typedef enum {
    RUNNING,
    FINISHED,
} job_status_t;

class Job {
public:
    Job( ICommand& command );
    ~Job();

    Variant run();

    inline Atom id() const
    { return f_id; }

    inline void join()
    {
        if (f_status != FINISHED)
            f_thread.join();
    }

    inline void kill()
    {
        if (f_status != FINISHED)
            f_command.kill();
    }

    inline job_status_t status() const
    { return f_status; }

    inline double elapsed() const
    { return (double) (clock() - f_t0) / CLOCKS_PER_SEC; }

private:
    ICommand& f_command;
    thread f_thread;

    Atom f_id;
    clock_t f_t0;

    job_status_t f_status;
};
typedef class Job* Job_ptr;
typedef vector<Job_ptr> Jobs;

#endif
