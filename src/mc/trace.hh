/*
Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

 */

/**
 * @file variant.hh
 *
 * @brief Traces management
 *
 */

#ifndef TRACE_H
#define TRACE_H
#include <common.hh>

typedef enum {
  BMC_CTX,
} TraceType;

// Trace iface
class ITrace {
public:
  virtual string get_desc() =0;
  virtual void set_desc(const string& desc) =0;

  virtual unsigned size() =0;
  virtual bool empty() =0;
};


// Trace implementation
class Trace : public ITrace {
public:
  // trace constructors
  Trace() {}

private:
};

typedef ITrace* ITrace_ptr;
typedef vector <ITrace_ptr> Traces;

#endif
