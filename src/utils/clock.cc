/**
 * @file clock.cc
 * @brief Generic utils module
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

#include <cstdint>
#include <iomanip>
#include <sstream>
#include <clock.hh>

struct stopclock_t {
    time_t tv_sec;
    double tv_msecs;
};

const uint64_t ONE_BILLION { 1000000000L };
struct stopclock_t timespec_diff(struct timespec from, struct timespec to)
{
    uint64_t t_from {from.tv_sec * ONE_BILLION + from.tv_nsec};
    uint64_t t_to {to.tv_sec * ONE_BILLION + to.tv_nsec};
    uint64_t t_diff {t_to - t_from};

    uint64_t tv_sec { t_diff / ONE_BILLION };
    uint64_t tv_nsec { t_diff % ONE_BILLION };

    return { (time_t) tv_sec, (double) tv_nsec / ONE_BILLION };
}

std::string elapsed_repr(struct timespec from, struct timespec to)
{
    struct stopclock_t diff { timespec_diff(from, to) };
    time_t uptime { diff.tv_sec };
    unsigned secs = uptime % 60;
    unsigned mins = uptime / 60;
    unsigned hrs = 0;

    if (60 < mins) {
        mins = mins % 60;
        hrs  = mins / 60;
    }

    std::ostringstream ss;

    bool a
        (false);
    if (0 < hrs) {
        ss
            << hrs
            << "h";
        a = true;
    }

    bool b
        (a);
    if (0 < mins) {
        if (a)
            ss
                << " ";
        ss
            << mins
            << "m";
        b = true;
    }

    if (b)
        ss
            << " ";

    ss
        << std::setprecision(3)
        << secs + diff.tv_msecs
        << "s" ;

    return ss.str();
}
