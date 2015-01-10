/**
 *  @file bmc.hh
 *  @brief SAT-based BMC Algorithms for property checking
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

#ifndef BMC_ALGORITHM_H
#define BMC_ALGORITHM_H

#include <base.hh>
#include <expr.hh>
#include <witness.hh>

#include <bmc/normalizer.hh>

class BMC : public Algorithm {

public:
    BMC(ICommand& command, Model& model, Expr_ptr formula, ExprVector& constraints);
    ~BMC();

    void process();

    inline mc_status_t status() const
    { return f_status; }

    inline void set_status(mc_status_t status)
    { f_status = status; }

    Expr_ptr property() const
    { return f_property; }

    const ExprVector& constraints() const
    { return f_constraints; }

private:
    Expr_ptr f_property;

    ExprVector f_constraints;
    mc_status_t f_status;

    /* strategies */
    void falsification( Expr_ptr phi );
    void kinduction( Expr_ptr phi );

    /* synchronization */

};

/* Specialized for BMC CEX */
class BMCCounterExample : public Witness {
public:
    BMCCounterExample(Expr_ptr property, Model& model,
                      Engine& engine, unsigned k, bool use_coi);
};

#endif
