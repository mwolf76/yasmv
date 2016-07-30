#if 0

// -*- C++ -*-

#ifndef SIMPLETERMS_H_INCLUDED
#define SIMPLETERMS_H_INCLUDED

#include "SolverTypes.h"
#include <iostream>
#include <sstream>

namespace Minisat {

  enum SimpleTermKind { FALSE, TRUE, VAR, NOT, OR, AND };

  class SimpleTerm {

    // term kind
    SimpleTermKind f_kind;

    union {
      Var f_variable;

      struct {
        SimpleTerm* f_car;
        SimpleTerm* f_cdr;
      } f_children;

    } f_data;

    // private constructors prevent direct calling, only friend
    // factory class is intended to make/delete terms.
    SimpleTerm(SimpleTermKind kind)
      : f_kind(kind) {}

  public:
    ~SimpleTerm() {}

    friend class SimpleTermFactory;
    friend std::ostream& operator<<(std::ostream& os, SimpleTerm& term);

    inline bool is_var() const
    { return f_kind == VAR; }

    inline bool is_true() const
    { return f_kind == TRUE; }

    inline bool is_false() const
    { return f_kind == FALSE; }

    inline bool is_and() const
    { return f_kind == AND; }

    inline bool is_or() const
    { return f_kind == OR;  }

    inline bool is_not() const
    { return f_kind == NOT; }

    inline Var var() const
    { assert (is_var()); return f_data.f_variable; }

    inline Term car() const
    { assert( is_and() || is_or() || is_not() ); return (Term) (f_data.f_children.f_car); }

    inline Term cdr() const
    { assert( is_and() || is_or() ) ; return (Term) (f_data.f_children.f_cdr); }

  };

  class SimpleTermWriter : public TermWriter {
    ostream& f_os;

  public:

    SimpleTermWriter(ostream& os)
      : f_os(os)
    {}

    ~SimpleTermWriter() {};

    SimpleTermWriter& operator<<(const std::string& s)
    { f_os << s; return *this; }

    SimpleTermWriter& operator<<(Term t)
    {
      SimpleTerm& term = * (reinterpret_cast<SimpleTerm *> (t) );

      if (term.is_true()) {
        (*this) << "TRUE";
      }

      else if (term.is_false()) {
        (*this) << "FALSE";
      }

      else if (term.is_var()) {
        std::stringstream tmp;

        tmp << term.var();
        (*this) << "V" << tmp.str();
      }

      else if (term.is_and()) {
        (*this) << "(" << term.car() << " & " << term.cdr() << ")";
      }

      else if (term.is_or()) {
        (*this) << "(" << term.car() << " | " << term.cdr() << ")";
      }

      else if (term.is_not()) {
        (*this) << "(! " << term.car() << ")";
      }

      else assert (false); // wtf ?

      return *this;
    }
  };

  class SimpleTermFactory : public TermFactory {
  public:
    SimpleTermFactory() {}
    ~SimpleTermFactory() {}

    // term makers, unsafe casts for minimum fuss
    inline Term make_true()
    { return (Term) (new SimpleTerm(TRUE)); }

    inline Term make_false()
    { return (Term) (new SimpleTerm(FALSE)); }

    inline Term make_var(Var v)
    {
      SimpleTerm* res = new SimpleTerm(VAR);
      res->f_data.f_variable = v;
      return (Term)(res);
    }

    inline Term make_and(Term t1, Term t2)
    {
      SimpleTerm* res = new SimpleTerm(AND);
      res->f_data.f_children.f_car = (SimpleTerm*)(t1);
      res->f_data.f_children.f_cdr = (SimpleTerm*)(t2);
      return (Term)(res);
    }

    Term make_or(Term t1, Term t2)
    {
      SimpleTerm* res = new SimpleTerm(OR);
      res->f_data.f_children.f_car = (SimpleTerm*)(t1);
      res->f_data.f_children.f_cdr = (SimpleTerm*)(t2);
      return (Term)(res);
    }

    Term make_not(Term t)
    {
      SimpleTerm* res = new SimpleTerm(NOT);
      res->f_data.f_children.f_car = (SimpleTerm*)(t);
      return (Term)(res);
    }

    // std::ostream &operator<<(std::ostream &out, const Term *t);
  };

} // namespace Minisat

#endif // TERMBANK_H_INCLUDED

#endif
