/**
 * @file witness.hh
 * @brief Witness module header file, exception classes
 *
 * This module contains definitions and services that implement the
 * abstract interface for the witness subsystem.
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

#ifndef WITNESS_EXCEPTIONS_H
#define WITNESS_EXCEPTIONS_H

#include <common/common.hh>

class WitnessException : public Exception {
public:
    virtual const char* what() const throw() =0;
};

/** Raised when a given ID is registered more than once */
class DuplicateWitnessId : public WitnessException {
public:
    DuplicateWitnessId(Atom id)
        : f_id(id)
    {}

    ~DuplicateWitnessId() throw()
    {}

    const char* what() const throw();

private:
    Atom f_id;
};

/** Raised when a given ID is registered more than once */
class NoCurrentlySelectedWitness : public WitnessException {
public:
    NoCurrentlySelectedWitness()
    {}

    ~NoCurrentlySelectedWitness() throw()
    {}

    const char* what() const throw();

private:
};

/** Raised when a given ID is searched for and was not registered */
class UnknownWitnessId : public WitnessException {
public:
    UnknownWitnessId(Atom id)
        : f_id(id)
    {}

    ~UnknownWitnessId() throw()
    {}

    const char* what() const throw();

private:
    Atom f_id;
};

/** Raised when TimeFrame for requested time does not exist. */
class IllegalTime : public WitnessException {
public:
    IllegalTime(step_t time)
        : f_time(time)
    {}

    ~IllegalTime() throw()
    {}

    const char* what() const throw();

private:
    step_t f_time;
};

class NoValue : public WitnessException {
public:
    NoValue(Expr_ptr id)
        : f_id(id)
    {}

    ~NoValue() throw()
    {}

    const char* what() const throw();

private:
    Expr_ptr f_id;
};



#endif /* WITNESS_EXCEPTIONS_H */