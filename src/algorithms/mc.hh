/**
 *  @file MC Algorithm.hh
 *  @brief MC Algorithm
 *
 *  This module contains definitions and services that implement an
 *  optimized storage for expressions. Expressions are stored in a
 *  Directed Acyclic Graph (DAG) for data sharing.
 *
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2.1 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/

#ifndef MC_ALGORITHM_H
#define MC_ALGORITHM_H

#include <base.hh>

typedef enum {
    MC_FALSE,
    MC_TRUE,
    MC_UNKNOWN,
} mc_status_t;

class MCAlgorithm : public Algorithm {
public:
    MCAlgorithm(IModel& model, Expr_ptr property);
    virtual ~MCAlgorithm();

    mc_status_t status() const;

    bool has_witness() const;

    Witness& get_witness() const;

protected:
    inline ADD& invariant()
    { return f_invariant_add; }

    inline ADD& violation()
    { return f_violation_add; }

    inline Expr_ptr property()
    { return f_property; }

    void assert_violation(step_t time,
                          group_t group = MAINGROUP,
                          color_t color = BACKGROUND);

    void assert_invariant(step_t time,
                          group_t group = MAINGROUP,
                          color_t color = BACKGROUND);

    void set_status(mc_status_t status);

private:
    // services
    void prepare();

    ADD       f_invariant_add;
    ADD       f_violation_add;

    Expr_ptr f_property;

    // ctx witness
    Witness_ptr f_witness;
    mc_status_t f_status;
};

#endif
