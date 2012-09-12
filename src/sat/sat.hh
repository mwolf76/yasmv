/**
 *  @file sat.hh
 *  @brief SAT interface
 *
 *  This module contains the interface for services that implement an
 *  CNF clauses generation in a form that is suitable for direct
 *  injection into the SAT solver.
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
#ifndef SAT_H
#define SAT_H

// general purpose decls
#include "satdefs.hh"
#include "terms/bdd_terms.hh"

// sub-components decls
#include "cnf/cnf.hh"
#include "proof/proof.hh"
#include "proof/interpolator.hh"
#include "model/model.hh"

// the glorious Minisat SAT solver
#include "core/Solver.hh"

namespace Minisat {

    template <class Term>
    class SAT : public IObject {
    public:
        virtual Group& new_group() =0;
        virtual Groups& groups() =0;

        virtual Color& new_color() =0;
        virtual Colors& colors() =0;

        virtual void push(Term t,
                          Group& group = MAINGROUP,
                          Color& color = BACKGROUND) =0;

        virtual void solve() =0; // all groups
        virtual void solve(const Groups& groups) =0;
        virtual status_t status() =0;

        virtual Term model(); // only if status() == SAT
        virtual Term interpolate(Colors& a); // only if status() == UNSAT

        virtual TermFactory<Term>& factory() const =0;
        virtual CNFizer<Term>& cnf() const =0;
        virtual Interpolator<Term>& interpolator() const =0;
        virtual ModelExtractor<Term>& model_extractor() const =0;
        virtual Solver& solver() const =0;
    };

};

#endif
