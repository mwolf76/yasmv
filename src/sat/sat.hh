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

#include "core/Solver.hh"
#include "terms/bdd_terms.hh" // imports cuddObj.hh
#include "proof/interpolator.hh"
#include "cnf/cnf.hh"
#include "model/model.hh"
#include "defs.hh"

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
    };

    class BDDSAT : public SAT<BDD> {
    public:
        virtual Group& new_group();
        virtual Groups& groups();

        virtual Color& new_color();
        virtual Colors& colors();

        virtual void push(BDD phi,
                          Group& group = MAINGROUP,
                          Color& color = BACKGROUND) =0;

        virtual void solve();
        virtual void solve(const Groups& groups);
        virtual status_t status();

        virtual BDD model(); // only if status() == SAT
        virtual BDD interpolate(const Colors& a); // only if status() == UNSAT

        BDDSAT(BDDTermFactory& factory);

    protected:
        inline BDDTermFactory& factory() const
        { return f_factory; }

        friend class CNFizer<BDD>;
        inline const CNFizer<BDD>& cnf() const
        { return f_cnfizer; }

        friend class Interpolator<BDD>;
        inline const Interpolator<BDD>& interpolator() const
        { return f_interpolator; }

        friend class ModelExtractor<BDD>;
        inline const ModelExtractor<BDD>& model_extractor() const
        { return f_model_extractor; }

    private:
        Groups f_groups;
        id_t f_next_group;

        Colors f_colors;
        id_t f_next_color;

        // -- sub-components -------------------------------------------------------

        // the glorious Minisat SAT solver
        Solver f_solver;

        // The term factory used to build the interpolant formula
        BDDTermFactory &f_factory;

        // Conversion to CNF using BDD (cfr. Cabodi et al...) ADD ref
        CNFizer<BDD> f_cnfizer;

        // Interpolator component (cfr. McMillan et al... ) ADD ref
        Interpolator<BDD> f_interpolator;

        // Model extractor
        ModelExtractor<BDD> f_model_extractor;
    };

};

#endif
