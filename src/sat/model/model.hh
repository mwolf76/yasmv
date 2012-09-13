/**
 *  @file model.hh
 *  @brief SAT model extraction
 *
 *  This module contains the definitions for SAT
 *  model extraction.
 *
 *  Authors: Marco Pensallorto
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the addterms of the GNU Lesser General Public
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
#ifndef MODEL_H_INCLUDED
#define MODEL_H_INCLUDED
#include "sat.hh"

namespace Minisat {

    template <class Term>
    class ModelExtractor {
    protected:
        SAT<Term>& f_owner; // the SAT instance

    public:
        ModelExtractor(SAT<Term>& owner)
            : f_owner(owner)
        { TRACE << "Initialized CNFizer instance @" << this << endl; }

        virtual ~ModelExtractor()
        {}

        /**
         * @brief Retrieve a model from the SAT instance. Remark:
         * current status must be STATUS_SAT. An exception will be
         * raised otherwise.
         */
        virtual Term model() =0;
    };
}

#endif // MODEL_H_INCLUDED
