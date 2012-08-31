// -*- C++ -*-

/**************************************************************************************************

terms.h

Generic term support (abstract interface)

  This file is part of NuSMV version 2.
  Copyright (C) 2007 by FBK-irst.
  Author: Marco Pensallorto <pensallorto@fbk.eu>

  NuSMV version 2 is free software; you can redistribute it and/or
  modify it under the terms of the GNU Lesser General Public
  License as published by the Free Software Foundation; either
  version 2 of the License, or (at your option) any later version.

  NuSMV version 2 is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public
  License along with this library; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307  USA.

  For more information on NuSMV see <http://nusmv.fbk.eu>
  or email to <nusmv-users@fbk.eu>.
  Please report bugs to <nusmv-users@fbk.eu>.

  To contact the NuSMV development board, email to <nusmv@fbk.eu>. ]

**************************************************************************************************/
#ifndef TERMS_H_INCLUDED
#define TERMS_H_INCLUDED

#include <SolverTypes.h>

// Generic term (void* is standard to interact with underlying C code)
typedef void* Term;

namespace Minisat {

  class TermFactory {

  public:
    virtual ~TermFactory() {};

    // constants
    virtual Term make_true() =0;
    virtual Term make_false() =0;

    // variables
    virtual Term make_var(Var v) =0;

    // operators
    virtual Term make_and(Term t1, Term t2) =0;
    virtual Term make_or(Term t1, Term t2) =0;
    virtual Term make_not(Term t) =0;
  };

  class TermReader {

  public:
    virtual ~TermReader() {}
    virtual TermReader& operator>> (Term& t) =0;
  };
  
  class TermWriter {

  public:
    virtual ~TermWriter() {}
    virtual TermWriter& operator<< (Term t) =0;
  };

} // namespace Minisat

#endif // TERMS_H_INCLUDED
