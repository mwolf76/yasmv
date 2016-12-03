/**
 * @file sat.cc
 * @brief Engine interface implementation, CNFization algorithm #1 (No cut) implementation.
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
#define  DEBUG_CNF_LITERALS

#include <sat/sat.hh>
#include <dd/dd_walker.hh>

class CNFBuilderNoCut : public ADDWalker {
public:
  CNFBuilderNoCut(Engine& sat, step_t time,
                  group_t group = MAINGROUP)
    : f_sat(sat)
    , f_time(time)
    , f_group(group)
  {}

  ~CNFBuilderNoCut()
  {}

  bool condition(const DdNode *node)
  {
    /* if it's a zero leaf */
    return (node == f_sat.enc().dd().getManager() -> zero);
  }

  void zero()
  { assert(false); /* unused */ }

  void one()
  { assert(false); /* unused* */ }

  void pre_hook()
  {}

  void post_hook()
  {}

  void action(const DdNode *node)
  {
    DdManager* dd_mgr
      (f_sat.enc().dd().getManager());

    value_t value
      (Cudd_V(node));

    vec<Lit> ps;
    ps.push( mkLit( f_group, true));

    unsigned i, size = dd_mgr -> size;
    for (i = 0; i < size; ++ i) {
      Lit lit
        (mkLit( f_sat.find_dd_var(i, f_time), value != 0));

      ps.push(lit);
    }

    f_sat.add_clause(ps);

    DEBUG
      << ps
      << std::endl;
  }

private:
  Engine& f_sat;

  step_t f_time;
  group_t f_group;
};

void Engine::cnf_push_no_cut(ADD add, step_t time, const group_t group)
{
  CNFBuilderNoCut worker
    (*this, time, group);

  worker(add);
}

