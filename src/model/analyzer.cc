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
 * @file analyzer.cc
 *
 * @brief Model analyzer
 *
 */
#include <common.hh>

#include <expr.hh>
#include <analyzer.hh>

Analyzer::Analyzer(bool eager)
  : f_map()
  , f_stack()
  , f_ctx(NULL)
  , f_id_depth(0)
  , f_mm(ModelMgr::INSTANCE())
  , f_em(ExprMgr::INSTANCE())
  , f_tm(TypeMgr::INSTANCE())
{
  logger << "Created Analyzer instance at @" << this << endl;

  // let's get started
  if (eager) process();
}

Analyzer::~Analyzer()
{
  logger << "Destroying analyzer..." << endl;
}

void Analyzer::process()
{
  Model& model = dynamic_cast <Model&> (*f_mm.get_model());

  try {
    const Modules& modules = model.get_modules();

    logger << "-- first pass (binding)" << endl;

    // (binding) For each module m in M, A goes deep in the module
    // defs. Every variable decl is resolved either to a native type
    // (boolean, ranged int, ...) or to an instance. Due to (1) all
    // modules are defined so any unresolved symbol at this point is a
    // fatal. Native types are taken care of as well.
    for (Modules::const_iterator mod_eye = modules.begin();
         mod_eye != modules.end(); mod_eye ++ ) {

      Module& module = dynamic_cast <Module&> (*mod_eye->second);

      // Remark: ctx name is MODULE name, not instance's
      // rationale: you may have several instances but they
      // all should refer to the same entry on the type map.
      const Expr_ptr ctx = module.get_name();

      const Variables vars = module.get_localVars();
      for (Variables::const_iterator var_eye = vars.begin();
           var_eye != vars.end(); var_eye ++) {

        IVariable_ptr const var = var_eye->second;

        const Expr_ptr varname = var->get_name();
        const Type_ptr vartype = var->get_type();

        // eager binding for module instances
        if (f_tm.is_instance(vartype)) {
          Instance& instance = dynamic_cast <Instance&> (*vartype);

          const Expr_ptr module_name = instance.get_module_name();
          IModule& resolved = model.get_module(module_name);

          // match number of params
          int inst_params_num = instance.get_params().size();
          int modl_params_num = resolved.get_formalParams().size();
          if ( inst_params_num != modl_params_num ) {
            // throw BadInstance(module_name);
          }
        }

        f_tm.set_type( FQExpr(ctx, varname), vartype);
      }
    }

    // (typechecking) For each module m in M, A inspects FSM exprs:
    // INVAR, TRANS, FAIRNESS have all to be boolean formulae; ASSIGNs
    // have to match lvalue type. The type for every expression is
    // inferred using the lazy walker strategy.
    for (Modules::const_iterator mod_eye = modules.begin();
         mod_eye != modules.end(); mod_eye ++ ) {

      Module& module = dynamic_cast <Module&> (*mod_eye->second);

      // Remark: ctx name is MODULE name, not instance's
      // rationale: you may have several instances but they
      // all should refer to the same entry on the type map.
      Expr_ptr ctx = module.get_name();

      // const Exprs params = module.get_formalParams();
      // for (Exprs::const_iterator param_eye = params.begin();
      //      param_eye != params.end(); param_eye ++) {

      //   Expr_ptr pname = *param_eye;
      //   tm.reset_type(FQExpr(ctx, pname));
      // }

      // TODO: isa decls currently not supported
      const Exprs isadecls = module.get_isaDecls();
      assert (isadecls.size() == 0);

      // type inference: defines
      const Defines defines = module.get_localDefs();
      for (Defines::const_iterator define_eye = defines.begin();
           define_eye != defines.end(); define_eye ++) {

        Define& define = dynamic_cast <Define&> (*define_eye->second);

        Expr_ptr dname = define.get_name();
        FQExpr fqdn(ctx, dname);

        Expr_ptr dbody = define.get_body();
        Type_ptr dtype = infer_expr_type(ctx, dbody);

        Type_ptr _type = f_tm.get_type(fqdn); // previously determined type
        if (_type) {
          if (_type != dtype) {
            throw BadType(_type->get_repr(),
                                   dtype->get_repr(),
                                   dbody);
          }
        } else f_tm.set_type(fqdn, dtype);
      } // for defines

      // type inference: FSM
      const Exprs init = module.get_init();
      for (Exprs::const_iterator init_eye = init.begin();
           init_eye != init.end(); init_eye ++) {

        Expr_ptr body = (*init_eye);
        Type_ptr tp = infer_expr_type(ctx, body);
        if (tp != f_tm.find_boolean())
          throw BadType(f_tm.find_boolean()->get_repr(),
                        tp->get_repr(), body);
      } // for init

      const Exprs invar = module.get_invar();
      for (Exprs::const_iterator invar_eye = invar.begin();
           invar_eye != invar.end(); invar_eye ++) {

        Expr_ptr body = (*invar_eye);
        Type_ptr tp = infer_expr_type(ctx, body);
        if (tp != f_tm.find_boolean()) {
          throw BadType(f_tm.find_boolean()->get_repr(),
                                 tp->get_repr(), body);
        }
      } // for invar

      const Exprs trans = module.get_trans();
      for (Exprs::const_iterator trans_eye = trans.begin();
           trans_eye != trans.end(); trans_eye ++) {

        Expr_ptr body = (*trans_eye);
        Type_ptr tp = infer_expr_type(ctx, body);
        if (tp != f_tm.find_boolean()) {
          throw BadType(f_tm.find_boolean()->get_repr(),
                                 tp->get_repr(), body);
        }
      } // for trans

      const Exprs fair = module.get_fairness();
      for (Exprs::const_iterator fair_eye = fair.begin();
           fair_eye != fair.end(); fair_eye ++) {

        Expr_ptr body = (*fair_eye);
        Type_ptr tp = infer_expr_type(ctx, body);
        if (tp != f_tm.find_boolean()) {
          throw BadType(f_tm.find_boolean()->get_repr(),
                                 tp->get_repr(), body);
        }
      } // for fair

      const Assigns assign = module.get_assign();
      for (Assigns::const_iterator assign_eye = assign.begin();
           assign_eye != assign.end(); assign_eye ++) {

        Expr_ptr lvalue = (*assign_eye)->get_name();
        if (!lvalue)
          throw NotAnLvalue(lvalue);
        Type_ptr lvalue_type = infer_expr_type(ctx, lvalue);

        Expr_ptr body = (*assign_eye)->get_body();
        Type_ptr body_type = infer_expr_type(ctx, body);

        if (lvalue_type != body_type) {
          // throw BadType(lvalue_type, body_type, body);
        }
      } // for assign

      const Exprs ltlspecs = module.get_ltlspecs();
      for (Exprs::const_iterator ltl_eye = ltlspecs.begin();
           ltl_eye != ltlspecs.end(); ltl_eye ++) {

        Expr_ptr body = (*ltl_eye);
        Type_ptr tp = infer_expr_type(ctx, body);
        if (tp != f_tm.find_temporal()) {
          // throw BadType(LTL_TEMPORAL, tp, body);
        }
      } // for ltlspecs

      const Exprs ctlspecs = module.get_ctlspecs();
      for (Exprs::const_iterator ctl_eye = ctlspecs.begin();
           ctl_eye != ctlspecs.end(); ctl_eye ++) {

        Expr_ptr body = (*ctl_eye);
        Type_ptr tp = infer_expr_type(ctx, body);
        if (tp != f_tm.find_temporal()) {
          // throw BadType(CTL_TEMPORAL, tp, body);
        }

      } // for ctlspecs

    } // for modules

  }

  catch (AnalyzerException ae) {
    // report error
  }
}


// local ctx variant
Type_ptr Analyzer::infer_expr_type(Expr_ptr body)
{
  Type_ptr res = NULL;

  // invoke walker on the body of the expr to be processed
  (*this)(body);

  assert(1 == f_stack.size());
  res = f_stack.top();

  return res;
}

// infers expr 'body' type in ctx. ctx is the name of the
// module the expression is evaluated in.
Type_ptr Analyzer::infer_expr_type(Expr_ptr ctx, Expr_ptr body)
{
  // walk body in given ctx
  f_ctx = ctx; f_id_depth = 0;

  return infer_expr_type(body);
}

void Analyzer::pre_hook()
{}
void Analyzer::post_hook()
{}

// walker interface implementation: the type inference engine follows
// a simple pattern: on preorder, return true if the node has not yet
// been visited; always do in-order (for binary nodes); proper type
// checking is performed by post-order hooks.

bool Analyzer::walk_F_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_F_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Analyzer::walk_G_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_G_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Analyzer::walk_X_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_X_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Analyzer::walk_U_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_U_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_U_postorder(const Expr_ptr expr)
{ walk_binary_temporal_postorder(expr); }

bool Analyzer::walk_R_preorder(const Expr_ptr expr)
{ return cache_miss(expr);  }
bool Analyzer::walk_R_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_R_postorder(const Expr_ptr expr)
{ walk_binary_temporal_postorder(expr); }

bool Analyzer::walk_AF_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_AF_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Analyzer::walk_AG_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_AG_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Analyzer::walk_AX_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_AX_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Analyzer::walk_AU_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_AU_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_AU_postorder(const Expr_ptr expr)
{ walk_binary_temporal_postorder(expr); }

bool Analyzer::walk_AR_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_AR_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_AR_postorder(const Expr_ptr expr)
{ walk_binary_temporal_postorder(expr); }

bool Analyzer::walk_EF_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_EF_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Analyzer::walk_EG_preorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_EG_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Analyzer::walk_EX_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_EX_postorder(const Expr_ptr expr)
{ walk_unary_temporal_postorder(expr); }

bool Analyzer::walk_EU_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_EU_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_EU_postorder(const Expr_ptr expr)
{ walk_binary_temporal_postorder(expr); }

bool Analyzer::walk_ER_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_ER_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_ER_postorder(const Expr_ptr expr)
{ walk_binary_temporal_postorder(expr); }

bool Analyzer::walk_init_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_init_postorder(const Expr_ptr expr)
{ walk_unary_fsm_postorder(expr); }

bool Analyzer::walk_next_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_next_postorder(const Expr_ptr expr)
{ walk_unary_fsm_postorder(expr); }

bool Analyzer::walk_neg_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_neg_postorder(const Expr_ptr expr)
{ walk_unary_arithmetical_postorder(expr); }

bool Analyzer::walk_not_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_not_postorder(const Expr_ptr expr)
{ walk_unary_logical_postorder(expr); }

bool Analyzer::walk_add_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_add_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_add_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool Analyzer::walk_sub_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_sub_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_sub_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool Analyzer::walk_div_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_div_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_div_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool Analyzer::walk_mul_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_mul_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_mul_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool Analyzer::walk_mod_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_mod_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_mod_postorder(const Expr_ptr expr)
{ walk_binary_arithmetical_postorder(expr); }

bool Analyzer::walk_and_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_and_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_and_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool Analyzer::walk_or_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_or_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_or_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool Analyzer::walk_xor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_xor_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_xor_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool Analyzer::walk_xnor_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_xnor_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_xnor_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool Analyzer::walk_implies_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_implies_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_implies_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool Analyzer::walk_iff_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_iff_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_iff_postorder(const Expr_ptr expr)
{ walk_binary_logical_postorder(expr); }

bool Analyzer::walk_lshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_lshift_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_lshift_postorder(const Expr_ptr expr)
{ walk_binary_bitwise_postorder(expr); }

bool Analyzer::walk_rshift_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_rshift_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_rshift_postorder(const Expr_ptr expr)
{ walk_binary_bitwise_postorder(expr); }

bool Analyzer::walk_eq_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_eq_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_eq_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool Analyzer::walk_ne_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_ne_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_ne_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool Analyzer::walk_gt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_gt_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_gt_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool Analyzer::walk_ge_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_ge_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_ge_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool Analyzer::walk_lt_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_lt_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_lt_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool Analyzer::walk_le_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_le_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_le_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool Analyzer::walk_ite_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_ite_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_ite_postorder(const Expr_ptr expr)
{ walk_binary_relational_postorder(expr); }

bool Analyzer::walk_cond_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_cond_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_cond_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_set_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
void Analyzer::walk_set_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_comma_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_comma_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_comma_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_dot_preorder(const Expr_ptr expr)
{
  Type_ptr res = lookup(expr);
  if (res != NULL) {
    f_stack.push(res);
    return false;
  }

  ++ f_id_depth;
  return true;
}

bool Analyzer::walk_dot_inorder(const Expr_ptr expr)
{ return true; }

void Analyzer::walk_dot_postorder(const Expr_ptr expr)
{
  const TypeMgr& tm = TypeMgr::INSTANCE();

  assert(0 < f_id_depth);
  assert(0 < f_id_fragments.size());

  if (! (-- f_id_depth)) {

    // perform chain resolution
    Expr_ptr local_ctx = f_ctx;

    Exprs::iterator eye;
    int steps = f_id_fragments.size();
    for (eye = f_id_fragments.begin();
         steps --; eye ++ ) {

      Expr_ptr frag = (*eye);
      ISymbol_ptr symb = resolve(local_ctx, frag);

      IVariable_ptr var = dynamic_cast<IVariable_ptr>(symb);
      if (var != NULL && tm.is_instance(var->get_type())) {
        Instance_ptr instance = dynamic_cast <Instance_ptr> (var->get_type());
        assert(instance);

        IModule_ptr module = instance->get_module();
        assert(module);

        local_ctx = module->get_name();
      } else break; // no further chaining possible
    }

    if (0 != steps)
      throw ResolutionException(expr);
    //                                f_id_fragments.size() - steps);

    // // here we have symb (const, variable)
    // assert(symb->is_const() || symb->is_variable());

    // if (symb->is_const()) {
    //   tm.
    // }

  }
}

// one step of resolution returns a const or variable
ISymbol_ptr Analyzer::resolve(const Expr_ptr ctx, const Expr_ptr frag)
{
  ExprMgr& em = ExprMgr::INSTANCE();

  ModelMgr& mm = ModelMgr::INSTANCE();
  Model& model = static_cast <Model&> (*mm.get_model());

  ISymbol_ptr symb = model.fetch_symbol(FQExpr(ctx, frag));

  // is this a variable?
  if (symb->is_variable()) {
    return symb;
  }

  // ... or a define?
  else if (symb->is_define()) {

    while (symb->is_define()) {
      Expr_ptr body = symb->as_define().get_body();
      if (!em.is_identifier(body)) {
        // throw BadDefine(); // TODO
      }
      symb = model.fetch_symbol(FQExpr(ctx, body));
    }

    return symb;
  }

  // .. or a constant?
  else if (symb->is_const()) {
    return symb;
  }

  // or what?!?
  else assert(0);
}

bool Analyzer::walk_member_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_member_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_member_postorder(const Expr_ptr expr)
{}

bool Analyzer::walk_union_preorder(const Expr_ptr expr)
{ return cache_miss(expr); }
bool Analyzer::walk_union_inorder(const Expr_ptr expr)
{ return true; }
void Analyzer::walk_union_postorder(const Expr_ptr expr)
{}

void Analyzer::walk_leaf(const Expr_ptr expr)
{
  TypeMgr& tm = TypeMgr::INSTANCE();
  ExprMgr& em = ExprMgr::INSTANCE();

  ExprType symb = expr->f_symb;
  Type_ptr tp;

  if (cache_miss(expr)) {

    if (symb == ICONST) {
      tp = tm.find_integer();
    }
    else if (symb == UWCONST) {
      tp = tm.find_uword(em.make_iconst(expr->f_wsize));
    }
    else if (symb == SWCONST) {
      tp = tm.find_sword(em.make_iconst(expr->f_wsize));
    }
    else if (symb == IDENT) {
      tp = infer_expr_type(expr);
      if (! f_id_depth) {
        assert(f_id_fragments.empty());
        f_stack.push(tp);
      }
      else {
        f_id_fragments.push_back(expr);
      }
    }
    else assert(0);
  }

  f_stack.push(tp);
}

// -- internal services -------------------------------------------------------

// fun: temporal -> temporal
void Analyzer::walk_unary_temporal_postorder(const Expr_ptr expr)
{
  const Type_ptr top = f_stack.top(); f_stack.pop();

  if (!f_tm.is_boolean(top) &&
      !f_tm.is_temporal(top)) {

    throw BadType(top->get_repr(),
                  f_em.make_boolean(), expr);
  }

  f_stack.push(f_tm.find_temporal());
}

// fun: temporal x temporal -> temporal
void Analyzer::walk_binary_temporal_postorder(const Expr_ptr expr)
{
  { // RHS
    const Type_ptr top = f_stack.top(); f_stack.pop();
    if (!f_tm.is_boolean(top))
      throw BadType(top->get_repr(), f_em.make_boolean(), expr);
  }

  { // LHS
    const Type_ptr top = f_stack.top(); f_stack.pop();
    if (!f_tm.is_boolean(top))
      throw BadType(top->get_repr(), f_em.make_boolean(), expr);
  }

  f_stack.push(f_tm.find_temporal());
}

// fun: boolean -> boolean
void Analyzer::walk_unary_fsm_postorder(const Expr_ptr expr)
{
  const Type_ptr top = f_stack.top(); f_stack.pop();

  if (!f_tm.is_boolean(top) &&
      !f_tm.is_integer(top) &&
      !f_tm.is_word(top)) {

    throw BadType(top->get_repr(), f_em.make_boolean(), expr);
  }

  f_stack.push(top); // propagate
}

// fun: arithm -> arithm
void Analyzer::walk_unary_arithmetical_postorder(const Expr_ptr expr)
{
  const Type_ptr top = f_stack.top(); f_stack.pop();

  if (!f_tm.is_integer(top) &&
      !f_tm.is_word(top)) {
    throw BadType(top->get_repr(), f_em.make_boolean(), expr);
  }

  f_stack.push(top); // propagate
}

// fun: logical -> logical
void Analyzer::walk_unary_logical_postorder(const Expr_ptr expr)
{
  const Type_ptr top = f_stack.top(); f_stack.pop();

  if (!f_tm.is_boolean(top)) {
    throw BadType(top->get_repr(), f_em.make_boolean(), expr);
  }

  f_stack.push(top); // propagate
}

// fun: arithm x arithm -> arithm
void Analyzer::walk_binary_arithmetical_postorder(const Expr_ptr expr)
{
  Type_ptr exp_type;

  { // RHS
    const Type_ptr top = f_stack.top(); f_stack.pop();
    if (!f_tm.is_integer(top)) {
      throw BadType(top->get_repr(), f_em.make_integer(), expr);
    }
    exp_type = top;
  }

  { // LHS
    const Type_ptr top = f_stack.top(); f_stack.pop();
    if (!f_tm.is_integer(top)) {
      throw BadType(top->get_repr(), f_em.make_integer(), expr);
    }

    // type matching is mandatory here
    if (top != exp_type) {
      throw BadType(exp_type->get_repr(), top->get_repr(), expr);
    }
  }

  f_stack.push(f_tm.find_integer());
}


// fun: logical x logical -> logical
void Analyzer::walk_binary_logical_postorder(const Expr_ptr expr)
{
  Type_ptr exp_type;

  { // RHS
      const Type_ptr top = f_stack.top(); f_stack.pop();
      if (!f_tm.is_boolean(top) &&
          !f_tm.is_word(top)) {
        throw BadType(top->get_repr(), f_em.make_boolean(), expr);
      }
      exp_type = top;
  }

  { // LHS
    const Type_ptr top = f_stack.top(); f_stack.pop();
    if (!f_tm.is_boolean(top) &&
        !f_tm.is_word(top)) {
      throw BadType(top->get_repr(), f_em.make_integer(), expr);
    }

    // type matching is mandatory here
    if (top != exp_type) {
      throw BadType(exp_type->get_repr(), top->get_repr(), expr);
    }
  }

  // by design propagate lhs type it should really matter
  f_stack.push(exp_type);
}

// fun: bitwise x bitwise -> bitwise
void Analyzer::walk_binary_bitwise_postorder(const Expr_ptr expr)
{
  Type_ptr exp_type;

  { // RHS
      const Type_ptr top = f_stack.top(); f_stack.pop();
      if (!f_tm.is_boolean(top) &&
          !f_tm.is_word(top)) {
        throw BadType(top->get_repr(), f_em.make_boolean(), expr);
      }
      exp_type = top;
  }

  { // LHS
    const Type_ptr top = f_stack.top(); f_stack.pop();
    if (!f_tm.is_boolean(top) &&
        !f_tm.is_word(top)) {
      throw BadType(top->get_repr(), f_em.make_integer(), expr);
    }

    // type matching is mandatory here
    if (top != exp_type) {
      throw BadType(exp_type->get_repr(), top->get_repr(), expr);
    }
  }

  // by design propagate lhs type it should really matter
  f_stack.push(exp_type);
}

// fun: arithmetical x arithmetical -> boolean
void Analyzer::walk_binary_relational_postorder(const Expr_ptr expr)
{
  Type_ptr exp_type;

  { // RHS
      const Type_ptr top = f_stack.top(); f_stack.pop();
      if (!f_tm.is_boolean(top) &&
          !f_tm.is_word(top)) {
        throw BadType(top->get_repr(), f_em.make_boolean(), expr);
      }
      exp_type = top;
  }

  { // LHS
    const Type_ptr top = f_stack.top(); f_stack.pop();
    if (!f_tm.is_boolean(top) &&
        !f_tm.is_word(top)) {
      throw BadType(top->get_repr(), f_em.make_integer(), expr);
    }

    // type matching is mandatory here
    if (top != exp_type) {
      throw BadType(exp_type->get_repr(), top->get_repr(), expr);
    }
  }

  f_stack.push(f_tm.find_boolean());
}
