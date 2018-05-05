/**
 * @file time.cc
 * @brief Command `time` class implementation.
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

#include <cmd/interpreter.hh>
#include <cmd/commands/time.hh>

#include <iomanip>

Time::Time(Interpreter& owner)
    : Command(owner)
{}

Time::~Time()
{}

struct timespec timespec_diff(struct timespec from, struct timespec to)
{
    const uint64_t BILLION { 1000000000L };

    uint64_t t_from {from.tv_sec * BILLION + from.tv_nsec};
    uint64_t t_to {to.tv_sec * BILLION + to.tv_nsec};
    uint64_t t_diff {t_to - t_from};

    uint64_t tv_sec { t_diff / BILLION };
    uint64_t tv_nsec { t_diff % BILLION };

    return { (time_t) tv_sec, (long) tv_nsec };

}

Variant Time::operator()()
{
    std::ostringstream oss;

    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);

    struct timespec epoch { Interpreter::INSTANCE().epoch() };
    struct timespec diff { timespec_diff(epoch, now) };

    time_t uptime { diff.tv_sec };
    unsigned secs = uptime % 60;
    unsigned mins = uptime / 60;
    unsigned hrs = 0;

    if (60 < mins) {
        mins = mins % 60;
        hrs  = mins / 60;
    }

    oss
        << "Session time: " ;

    bool a
        (false);
    if (0 < hrs) {
        oss
            << hrs
            << "h";
        a = true;
    }

    bool b
        (a);
    if (0 < mins) {
        if (a)
            oss
                << " ";
        oss
            << mins
            << "m";
        b = true;
    }

    if (b)
        oss
            << " ";

    oss
        << std::setprecision(3)
        << secs + (double) diff.tv_nsec / 1000000000L
        << "s";

    return Variant(oss.str());
}

TimeTopic::TimeTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

TimeTopic::~TimeTopic()
{
    TRACE
        << "Destroyed time topic"
        << std::endl;
}

void TimeTopic::usage()
{
    std::cout
        << "time - retrieves current running time in seconds" ;
}
