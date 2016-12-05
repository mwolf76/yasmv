/**
 * @file witness/exceptions.cc
 * @brief Witness module header file, exception classes implementation.
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

#include <common/common.hh>
#include <expr/expr.hh>

#include <witness/exceptions.hh>

#include <string>
#include <sstream>

static std::string build_duplicate_witness_id_error_message(Atom id)
{
    std::ostringstream oss;

    oss
        << "`"
        << id
        << "` is already registered." ;

    return oss.str();
}

DuplicateWitnessId::DuplicateWitnessId(Atom id)
    : WitnessException("DuplicateWitnessId",
                       build_duplicate_witness_id_error_message(id))
{}

/** Raised when a given ID is registered more than once */
NoCurrentlySelectedWitness::NoCurrentlySelectedWitness()
    : WitnessException("NoCurrentlySelectedWitness")
{}

static std::string build_unknown_witness_error_message(Atom id)
{
    std::ostringstream oss;

    oss
        << "`"
        << id
        << "` is not registered." ;


    return oss.str();
}

/** Raised when a given ID is searched for and was not registered */
UnknownWitnessId::UnknownWitnessId(Atom id)
    : WitnessException("UnknownWitnessId",
                       build_unknown_witness_error_message(id))
{}

static std::string build_illegal_time_error_message(step_t time)
{
    std::ostringstream oss;

    oss
        << time ;

    return oss.str();
}

/** Raised when TimeFrame for requested time does not exist. */
IllegalTime::IllegalTime(step_t time)
    : WitnessException("IllegalTime",
                       build_illegal_time_error_message(time))
{}

static std::string build_no_value_error_message(Expr_ptr id)
{
    std::ostringstream oss;

    oss
        << "No value for `"
        << id
        << "`";

    return oss.str();
}

NoValue::NoValue(Expr_ptr id)
    : WitnessException("NoValue",
                       build_no_value_error_message(id))
{}
