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
#include <witness.hh>

#include <bmc/analyzer.hh>

class BMC : public Algorithm {

public:
    BMC(IModel& model, Expr_ptr formula);
    ~BMC();

    void process();

    mc_status_t status() const
    { return f_status; }

    Expr_ptr property() const
    { return f_property; }

private:
    Expr_ptr  f_property;
    formula_t f_strategy;
    mc_status_t f_status;

    ADDVector f_violation_adds;
    MicroDescriptors f_violation_micros;

    ADDVector f_invariant_adds;
    MicroDescriptors f_invariant_micros;

    /* pure booleans, just initial states */
    void bmc_propositional_check();

    /* invariant checking */
    void bmc_invarspec_check();

    /* full LTL checking */
    void bmc_ltlspec_check();

    // overrides
    void prepare();
    void compile();
};

/* Specialized for BMC ctx */
class BMCCounterExample : public Witness {
public:
    BMCCounterExample(Expr_ptr property, IModel& model,
                      SAT& engine, unsigned k, bool use_coi);
};

#endif
