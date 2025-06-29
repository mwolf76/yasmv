/**
   Copyright (C) 2011-2018 Marco Pensallorto

   This file is part of yasmv.

   yasmv is free software: you can redistribute it and/or modify it
   under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   yasmv is distributed in the hope that it will be useful, but WITHOUT ANY
   WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
   A PARTICULAR PURPOSE. See the GNU General Public License for more details.

   You should have received a copy of the GNU General Public License this
   program. If not, see <http://www.gnu.org/licenses/>.
*/
grammar smv;

@header {
  #include <common/common.hh>

  /* cmd subsystem */
  #include <cmd/cmd.hh>

  #include <expr/expr.hh>
  #include <expr/expr_mgr.hh>

  #include <type/type.hh>
  #include <type/type_mgr.hh>

  #include <model/model.hh>
  #include <model/model_mgr.hh>

  #include <parser/grammars/grammar.hh>
}

@members {
    /* singleton managers */
    expr::ExprMgr& em
        (expr::ExprMgr::INSTANCE());

    model::ModelMgr& mm
        (model::ModelMgr::INSTANCE());

    type::TypeMgr& tm
        (type::TypeMgr::INSTANCE());

    opts::OptsMgr& om
        (opts::OptsMgr::INSTANCE());

    cmd::CommandMgr& cm
        (cmd::CommandMgr::INSTANCE());

    /* the model instance */
    model::Model& smv_model
        (mm.model());
}

// --- Model Description Language  ---------------------------------------------
smv
locals [
    model::Module_ptr current_module;
]
    : model_directives modules
    ;

model_directives
    : model_directive*
    ;

model_directive
    : model_word_width_directive
    ;

model_word_width_directive
    : '#word-width' width=constant
    { om.set_word_width( $width.res->value()); }
    ;

modules
    : module_def *
    ;

module_def
    : 'MODULE' module_id=identifier
      { smv_model.add_module(* ($ctx->current_module = new model::Module($module_id.res))); }

      fsm_param_decl? module_body ';'
    ;

module_body
    :   module_decl ( ';' module_decl )*
    ;

module_decl
locals [
    int hidden;
    int input;
    int frozen;
    int inertial;

    value_format_t format;
]
@init {
    $ctx->hidden = 0;
    $ctx->input = 0;
    $ctx->frozen = 0;
    $ctx->inertial = 0;

    $ctx->format = FORMAT_DEFAULT;
}

    :   /* variables and defines */
        fsm_decl_modifiers (
            fsm_var_decl
        |   fsm_define_decl
        )*

        fsm_formula_decl*
    ;

fsm_formula_decl
    : /* FSM definition */
        fsm_init_decl
    |   fsm_invar_decl
    |   fsm_trans_decl
    ;

fsm_decl_modifiers
    : ( '#'
            (
              'hidden'   { $module_decl::ctx->hidden   = 1; }
            | 'frozen'   { $module_decl::ctx->frozen   = 1; }
            | 'inertial' { $module_decl::ctx->inertial = 1; }
            | 'input'    { $module_decl::ctx->input    = 1; }

            | 'bin' { $module_decl::ctx->format = FORMAT_BINARY;      }
            | 'oct' { $module_decl::ctx->format = FORMAT_OCTAL;       }
            | 'dec' { $module_decl::ctx->format = FORMAT_DECIMAL;     }
            | 'hex' { $module_decl::ctx->format = FORMAT_HEXADECIMAL; }
            )) *
    ;

fsm_var_decl
    :
        'VAR' fsm_var_decl_body
    ;

fsm_param_decl
    : '(' fsm_param_decl_body ')'
    ;

fsm_var_decl_body
    : fsm_var_decl_clause
        ( ';' fsm_var_decl_clause)*
    ;

fsm_param_decl_body
    : fsm_param_decl_clause
        ( ',' fsm_param_decl_clause)*
    ;

fsm_var_decl_clause
@init {
    expr::ExprVector ev;
}
    : ids=identifiers[&ev] ':' tp=smv_type
    {
            expr::ExprVector::iterator expr_iter;
            assert(NULL != $tp.res);
            for (expr_iter = ev.begin(); expr_iter != ev.end(); ++ expr_iter) {
                expr::Expr_ptr vid (*expr_iter);
                symb::Variable_ptr var
                    (new symb::Variable($smv::ctx->current_module->name(), vid, $tp.res));

                if ($module_decl::ctx->hidden)
                    var->set_hidden(true);
                if ($module_decl::ctx->input)
                    var->set_input(true);
                if ($module_decl::ctx->inertial)
                    var->set_inertial(true);
                if ($module_decl::ctx->frozen)
                    var->set_frozen(true);

                if ($module_decl::ctx->format != FORMAT_DEFAULT)
                    var->set_format($module_decl::ctx->format);

                $smv::ctx->current_module->add_var(vid, var);
            }
    }
    ;

fsm_param_decl_clause
@init {
    expr::ExprVector ev;
}
    : ids=identifiers[&ev] ':' tp=smv_type
    {
            expr::ExprVector::iterator expr_iter;
            assert(NULL != $tp.res);
            for (expr_iter = ev.begin(); expr_iter != ev.end(); ++ expr_iter) {
                expr::Expr_ptr pid (*expr_iter);
                $smv::ctx->current_module->add_parameter(pid,
                                                    new symb::Parameter($smv::ctx->current_module->name(),
                                                                        pid, $tp.res));
            }
    }
    ;


fsm_define_decl
    :
        'DEFINE' fsm_define_decl_body
    ;

fsm_define_decl_body
    : fsm_define_decl_clause
        ( ';' fsm_define_decl_clause)*
    ;

fsm_define_decl_clause
    : id=identifier ':=' body=toplevel_expression
    {
      symb::Define_ptr def =
          new symb::Define($smv::ctx->current_module->name(), $id.res, $body.res);

      if ($module_decl::ctx->input)
          throw SyntaxError("#input modifier not supported in DEFINE decls");

      if ($module_decl::ctx->frozen)
          throw SyntaxError("#frozen modifier not supported in DEFINE decls");

      if ($module_decl::ctx->inertial)
          throw SyntaxError("#inertial modifier not supported in DEFINE decls");

      if ($module_decl::ctx->hidden)
          def->set_hidden(true);

      /* these are mutually exclusive, default is hexadecimal */
      if ($module_decl::ctx->format != FORMAT_DEFAULT)
          def->set_format($module_decl::ctx->format);

      $smv::ctx->current_module->add_def($id.res, def);
    }
    ;

fsm_init_decl
    : 'INIT' fsm_init_decl_body
    ;

fsm_init_decl_body
    : fsm_init_decl_clause
        (';' fsm_init_decl_clause)*
    ;

fsm_init_decl_clause
    : expr=toplevel_expression
      { $smv::ctx->current_module->add_init($expr.res); }
    ;

fsm_invar_decl
    : 'INVAR' fsm_invar_decl_body
    ;

fsm_invar_decl_body
    : fsm_invar_decl_clause
        (';' fsm_invar_decl_clause)*
    ;

fsm_invar_decl_clause
    : expr=toplevel_expression
      { $smv::ctx->current_module->add_invar($expr.res); }
    ;

fsm_trans_decl
    : 'TRANS' fsm_trans_decl_body
    ;

fsm_trans_decl_body
    : fsm_trans_decl_clause
        (';' fsm_trans_decl_clause)*
    ;

fsm_trans_decl_clause
    : lhs=toplevel_expression '?:' rhs=toplevel_expression
      { $smv::ctx->current_module->add_trans(em.make_guard($lhs.res, $rhs.res)); }

    | rhs=toplevel_expression
      { $smv::ctx->current_module->add_trans(em.make_guard(em.make_true(), $rhs.res)); }
    ;

toplevel_expression returns [expr::Expr_ptr res]
    : expr=timed_expression
      { $res = $expr.res; }
    ;

timed_expression returns [expr::Expr_ptr res]
locals [
    expr::Expr_ptr a;
    expr::Expr_ptr b;
]
@init {
    $ctx->a = NULL;
    $ctx->b = NULL;
}
    : '@' time=forward_instant { $ctx->a = $time.res; } ('..' time2=forward_instant { $ctx->b = $time2.res; })? '{' body=temporal_expression '}'
      { $res = (NULL != $ctx->b) ? em.make_at( em.make_interval($ctx->a, $ctx->b),  $body.res) : em.make_at($ctx->a, $body.res); }

    | '$' time=backward_instant { $ctx->a = $time.res; } ('..' time2=backward_instant { $ctx->b = $time2.res; })? '{' body=temporal_expression '}'
      { $res = (NULL != $ctx->b) ? em.make_at( em.make_interval($ctx->a, $ctx->b),  $body.res) : em.make_at($ctx->a, $body.res); }

    | body=temporal_expression
      { $res = $body.res; }
    ;

temporal_expression returns [expr::Expr_ptr res]
    : expr=binary_ltl_expression
      { $res = $expr.res; }
    ;

binary_ltl_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=unary_ltl_expression
      { $res = $lhs.res; } (
            'U' rhs=unary_ltl_expression
            { $res = em.make_U($res, $rhs.res); }

        |   'R' rhs=unary_ltl_expression
            { $res = em.make_R($res, $rhs.res); }
      )* ;

unary_ltl_expression returns [expr::Expr_ptr res]
@init { }
    : 'G' expr=unary_ltl_expression
        { $res = em.make_G($expr.res); }

    | 'F' expr=unary_ltl_expression
        { $res = em.make_F($expr.res); }

    | 'X' expr=unary_ltl_expression
        { $res = em.make_X($expr.res); }

    /* common shortcuts */
    | 'GF' expr=unary_ltl_expression
        { $res = em.make_G(em.make_F($expr.res)); }

    | 'GX' expr=unary_ltl_expression
        { $res = em.make_G(em.make_X($expr.res)); }

    | 'FG' expr=unary_ltl_expression
        { $res = em.make_F(em.make_G($expr.res)); }

    | 'FX' expr=unary_ltl_expression
        { $res = em.make_F(em.make_X($expr.res)); }

    | 'XG' expr=unary_ltl_expression
        { $res = em.make_X(em.make_G($expr.res)); }

    | 'XF' expr=unary_ltl_expression
        { $res = em.make_X(em.make_F($expr.res)); }

    | expr=propositional_expression
      { $res = $expr.res; }
    ;

propositional_expression returns [expr::Expr_ptr res]
@init { }
    : expr=ite_expression {
         $res = $expr.res;
      }
    ;

ite_expression returns [expr::Expr_ptr res]
@init { }
    : expr=logical_expression {
         $res = $expr.res;
      }

      (
            '?' lhs=logical_expression ':' rhs=logical_expression
            { $res = em.make_ite( em.make_cond($res, $lhs.res), $rhs.res); }
      )?
    ;

logical_expression returns [expr::Expr_ptr res]
    : expr=logical_implies_expression
      { $res = $expr.res; }
    ;

logical_implies_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=logical_or_expression
      { $res = $lhs.res; }

    (
      '->' rhs=logical_or_expression
      { $res = em.make_implies($res, $rhs.res); }
    )* ;

logical_or_expression returns[expr::Expr_ptr res]
@init { }
    : lhs=logical_and_expression
      { $res = $lhs.res; }

    (
      '||' rhs=logical_and_expression
      { $res = em.make_or($res, $rhs.res); }
    )* ;

logical_and_expression returns[expr::Expr_ptr res]
@init { }
    : lhs=equality_expression
      { $res = $lhs.res; }

    (
      '&&' rhs=equality_expression
      { $res = em.make_and($res, $rhs.res); }
    )* ;

equality_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=relational_expression
      { $res = $lhs.res; }

      ( '=' rhs=relational_expression
            { $res = em.make_eq($res, $rhs.res); }

      | '!=' rhs=relational_expression
            { $res = em.make_ne($res, $rhs.res); }

      | ':=' rhs=relational_expression
            { $res = em.make_assignment($res, $rhs.res); }

      )? /* predicates are binary */;

relational_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=algebraic_expression
      { $res = $lhs.res; }

      ( '<' rhs=algebraic_expression
            { $res = em.make_lt($res, $rhs.res); }

      | '<=' rhs=algebraic_expression
            { $res = em.make_le($res, $rhs.res); }

      | '>=' rhs=algebraic_expression
            { $res = em.make_ge($res, $rhs.res); }

      | '>' rhs=algebraic_expression
            { $res = em.make_gt($res, $rhs.res); }
      )? /* predicates are binary */ ;

algebraic_expression returns [expr::Expr_ptr res]
@init { }
    :
        expr=bw_or_expression
        { $res = $expr.res; }
    ;

bw_or_expression returns[expr::Expr_ptr res]
@init { }
    : lhs=bw_xor_expression
      { $res = $lhs.res; }

    (
      '|' rhs=bw_xor_expression
       { $res = em.make_bw_or($res, $rhs.res); }
    )* ;

bw_xor_expression returns[expr::Expr_ptr res]
@init { }
    : lhs=bw_xnor_expression
      { $res = $lhs.res; }

    (
      '^' rhs=bw_xnor_expression
      { $res = em.make_bw_xor($res, $rhs.res); }
    )* ;

bw_xnor_expression returns[expr::Expr_ptr res]
@init { }
    : lhs=bw_and_expression
      { $res = $lhs.res; }

    (
      '<->' rhs=bw_and_expression
      { $res = em.make_bw_xnor($res, $rhs.res); }
    )* ;

bw_and_expression returns[expr::Expr_ptr res]
@init { }
    : lhs=shift_expression
      { $res = $lhs.res; }

    (
      '&' rhs=shift_expression
      { $res = em.make_bw_and($res, $rhs.res); }
    )* ;

shift_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=additive_expression
      { $res = $lhs.res; }

    (
      '<<' rhs=additive_expression
      { $res = em.make_lshift($res, $rhs.res); }

    | '>>' rhs=additive_expression
       { $res = em.make_rshift($res, $rhs.res); }
    )* ;

additive_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=multiplicative_expression
      { $res = $lhs.res; }

    (
        '+' rhs=multiplicative_expression
        { $res = em.make_add($res, $rhs.res); }

    |   '-' rhs=multiplicative_expression
        { $res = em.make_sub($res, $rhs.res); }
    )* ;

multiplicative_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=cast_expression
      { $res = $lhs.res; }

    (
      '*' rhs=cast_expression
      { $res = em.make_mul($res, $rhs.res); }

    | '/' rhs=cast_expression
      { $res = em.make_div($res, $rhs.res); }

    | '%' rhs=cast_expression
      { $res = em.make_mod($res, $rhs.res); }
    )* ;

cast_expression returns [expr::Expr_ptr res]
locals [
    expr::Expr_ptr cast;
]
@init {
    $ctx->cast = NULL;
}
    : '(' tp = native_type ')' expr = cast_expression
        { $res = em.make_cast( $tp.res->repr(), $expr.res ); }
    |
        expr = unary_expression
        { $res = $expr.res; }
    ;

unary_expression returns [expr::Expr_ptr res]
@init { }
    : expr=postfix_expression
      { $res = $expr.res; }

    | expr=nondeterministic_expression
      { $res = $expr.res; }

    | expr=array_expression
      { $res = $expr.res; }

    | 'next' '(' expr=toplevel_expression ')'
      { $res = em.make_next($expr.res); }

    | '!' expr=postfix_expression
      { $res = em.make_not($expr.res); }

    | '~' expr=postfix_expression
      { $res = em.make_bw_not($expr.res); }

    | '-' expr=postfix_expression
      { $res = em.make_neg($expr.res); }
    ;

nondeterministic_expression returns[expr::Expr_ptr res]
locals [
    bool is_range;
    expr::ExprVector clauses;
]
@init {
    $ctx->is_range = false;
}
    : '{'
          c=toplevel_expression{ $ctx->clauses.push_back($c.res); }
        (  ','  c2=toplevel_expression { $ctx->clauses.push_back($c2.res); }
        | '..' c3=toplevel_expression  { assert(!$ctx->is_range); $ctx->is_range = true; $ctx->clauses.push_back($c3.res); } )+
      '}'
      {
            if (!$ctx->is_range) {
                expr::ExprVector::reverse_iterator i { $ctx->clauses.rbegin() };
                while ($ctx->clauses.rend() != i) {
                    $res = $res ? em.make_set_comma( *i, $res) : *i;
                    ++ i;
                }
            } else {
               expr::ExprVector::iterator lhs { $ctx->clauses.begin() };
               expr::Expr_ptr lhs_expr { *lhs };
               assert (em.is_constant(lhs_expr));
               value_t start { lhs_expr->value() };

               expr::ExprVector::reverse_iterator rhs { $ctx->clauses.rbegin() };
               expr::Expr_ptr rhs_expr { *rhs };
               assert (em.is_constant(rhs_expr));
               value_t stop { rhs_expr->value() };

               // ensure lhs <= rhs
               if (start > stop) {
                   value_t tmp { start };
                   start = stop;
                   stop  = tmp;
               }

               // create set interval
               for (value_t i = stop; i >= start; i -- ) {
                   $res = $res
                       ? em.make_set_comma(em.make_const(i), $res)
                       : em.make_const(i)
                       ;
               }
            }

            $res = em.make_set( $res );
      }
      ;

array_expression returns[expr::Expr_ptr res]
locals [
    expr::ExprVector clauses;
]
    : '['
          c=toplevel_expression{ $ctx->clauses.push_back($c.res); }
            (',' c2=toplevel_expression { $ctx->clauses.push_back($c2.res); })*
      ']'
      {
            expr::ExprVector::reverse_iterator i
                ($ctx->clauses.rbegin());

            while ($ctx->clauses.rend() != i) {
                $res = $res ? em.make_array_comma( *i, $res) : *i;
                ++ i;
            }

            $res = em.make_array( $res );
        }
    ;


params[expr::ExprVector* actuals] returns [expr::Expr_ptr res]
@init {
    $res = NULL;
}
    : ( expressions[actuals]
    {
            expr::ExprVector::reverse_iterator expr_iter;
            $res = NULL;

            for (expr_iter = actuals->rbegin(); expr_iter != actuals->rend(); ++ expr_iter) {
                expr::Expr_ptr expr = (*expr_iter);
                $res = (!$res) ? expr : em.make_params_comma( expr, $res );
            }
    })?

    {
      if (! $res)
          $res = em.make_empty();
    }
    ;

postfix_expression returns [expr::Expr_ptr res]
@init { }
    :   lhs=basic_expression
        { $res = $lhs.res; }

    (
        '[' rhs=toplevel_expression ']'
        { $res = em.make_subscript($res, $rhs.res); }
    |
        {
            expr::ExprVector actuals;
        }
        '(' rhs=params[&actuals] ')'
        { $res = em.make_params($res, $rhs.res); }

    |   '.' rhs=identifier
        { $res = em.make_dot($res, $rhs.res); }
    )* ;

basic_expression returns [expr::Expr_ptr res]
@init { }
    : id=identifier
      { $res = $id.res; }

    | k=constant
      { $res = $k.res; }

    | '(' expr=toplevel_expression ')'
      { $res = $expr.res; }

    | expr=case_expression
      { $res = $expr.res; }
    ;

case_expression returns [expr::Expr_ptr res]
locals [
    typedef std::pair<expr::Expr_ptr, expr::Expr_ptr> CaseClause;
    typedef std::vector<CaseClause> CaseClauses;

    CaseClauses clauses;
]  : 'case'

     (lhs=toplevel_expression ':' rhs=toplevel_expression ';'
     { $ctx->clauses.push_back( std::pair< expr::Expr_ptr, expr::Expr_ptr > ($lhs.res, $rhs.res)); }) +

     'else' ':' last=toplevel_expression ';'
     { $ctx->clauses.push_back( std::pair< expr::Expr_ptr, expr::Expr_ptr > (NULL, $last.res)); }

     'end'
     {
        CaseClauses::reverse_iterator i = $ctx->clauses.rbegin();
        $res = i->second;
        while (1) {
            if ( ++ i == $ctx->clauses.rend())
                break;
            $res = em.make_ite( em.make_cond(i->first,
                                             i->second), $res);
        }
     }
    ;

identifiers [expr::ExprVector* ids]
    :
      ident=identifier
      { ids->push_back($ident.res); }

      ( ',' ident2=identifier
            { ids->push_back($ident2.res); }
      )* ;

expressions [expr::ExprVector* exprs]
    :
      expr=toplevel_expression
      { exprs->push_back($expr.res); }

      ( ',' expr2=toplevel_expression
            { exprs->push_back($expr2.res); }
      )* ;

identifier returns [expr::Expr_ptr res]
@init { }
    : IDENTIFIER
      { $res = em.make_identifier((const char*)($IDENTIFIER.text->toStringz(ctx))); }
    ;

forward_instant returns [expr::Expr_ptr res]
@init { }
    : DECIMAL_LITERAL {
        expr::Atom tmp((const char*)($DECIMAL_LITERAL.text->toStringz(ctx)));
        $res = em.make_instant(strtoll(tmp.c_str(), NULL, 10));
      }
    ;

backward_instant returns [expr::Expr_ptr res]
@init { }
    : DECIMAL_LITERAL {
        expr::Atom tmp((const char*)($DECIMAL_LITERAL.text->toStringz(ctx)));
        $res = em.make_instant(UINT_MAX - strtoll(tmp.c_str(), NULL, 10));
      }
    ;

constant returns [expr::Expr_ptr res]
@init { }
    : HEX_LITERAL {
        expr::Atom tmp((const char*)($HEX_LITERAL.text->toStringz(ctx)));
        $res = em.make_hex_const(tmp);
      }

    | BINARY_LITERAL {
        expr::Atom tmp((const char*)($BINARY_LITERAL.text->toStringz(ctx)));
        $res = em.make_bin_const(tmp);
      }

    | OCTAL_LITERAL {
        expr::Atom tmp((const char*)($OCTAL_LITERAL.text->toStringz(ctx)));
        $res = em.make_oct_const(tmp);
      }

    | DECIMAL_LITERAL {
        expr::Atom tmp((const char*)($DECIMAL_LITERAL.text->toStringz(ctx)));
        $res = em.make_dec_const(tmp);
      }

    | QUOTED_STRING {
            pANTLR3_UINT8 p = $QUOTED_STRING.text->toStringz(ctx);
            pANTLR3_UINT8 q; for (q = p; *q; ++ q) ;

            assert (*p == '\'' || *p == '\"');
            p ++ ;  /* cut lhs quote */

            q -- ;
            assert (*q == '\'' || *q == '\"');
            *q = 0; /* cut rhs quote */

            expr::Atom atom { (const char *) p };
            $res = em.make_qstring(atom);
      }
    ;

/* pvalue is used in param passing (actuals) */
pvalue returns [expr::Expr_ptr res]
@init {}
    : 'next' '(' expr=postfix_expression ')'
      { $res = em.make_next($expr.res); }

    | expr=postfix_expression
      { $res = $expr.res; }
    ;

/* ordinary values used elsewhere */
value returns [expr::Expr_ptr res]
@init { }
    : expr=postfix_expression
      { $res = $expr.res; }
    ;

/* typedecls */
smv_type returns [type::Type_ptr res]
@init {}
    : tp = native_type
      { $res = $tp.res; }

    | tp = enum_type
      { $res = $tp.res; }

    | tp = instance_type
      { $res = $tp.res; }
    ;

native_type returns [type::Type_ptr res]
@init {}
    : tp = boolean_type
      { $res = $tp.res; }

    | tp = unsigned_int_type
      { $res = $tp.res; }

    | tp = signed_int_type
      { $res = $tp.res; }
    ;

boolean_type returns [type::Type_ptr res]
locals [
    int array_size;
]
@init {
    $ctx->array_size = 0;
}
    : 'boolean' (

            '[' size=constant ']'
            {
                $ctx->array_size = $size.res->value();
                assert(0 < $ctx->array_size);
            }
    ) ?
    {
        $res = $ctx->array_size ?
            (type::Type_ptr) tm.find_boolean_array($ctx->array_size) :
            (type::Type_ptr) tm.find_boolean();
    }
    ;

enum_type returns [type::Type_ptr res]
locals [
    int array_size;
    expr::ExprSet lits;
]
@init {
    $ctx->array_size = 0;
}
    : '{'
          lit=literal { $ctx->lits.insert($lit.res); }
              (',' lit2=literal { $ctx->lits.insert($lit2.res); })*
      '}' (
            '[' size=constant ']'
            {
                $ctx->array_size = $size.res->value();
                assert(0 < $ctx->array_size);
            }
    ) ?
    {
        $res = $ctx->array_size ?
            (type::Type_ptr) tm.find_enum_array($ctx->lits, $ctx->array_size) :
            (type::Type_ptr) tm.find_enum($ctx->lits);
    }
    ;

unsigned_int_type returns [type::Type_ptr res]
locals [
    int array_size;
    char *p;
]
@init {
    $ctx->array_size = 0;
}
    :
        UNSIGNED_INT_TYPE
        {
            $ctx->p = (char *) $UNSIGNED_INT_TYPE.text->toStringz(ctx);
            while (*$ctx->p && !isdigit(*$ctx->p))
                ++ $ctx->p;
        }
        (
            '[' size=constant ']'
            {
                $ctx->array_size = $size.res->value();
                assert(0 < $ctx->array_size);
            }
    ) ?
    {
        $res = $ctx->array_size ?
            (type::Type_ptr) tm.find_unsigned_array(*$ctx->p ? atoi($ctx->p)
                : om.word_width(), $ctx->array_size) :
            (type::Type_ptr) tm.find_unsigned( *$ctx->p ? atoi($ctx->p)
                : om.word_width());
    }
    ;

signed_int_type returns [type::Type_ptr res]
locals [
    int array_size;
    char *p;
]
@init {
    $ctx->array_size = 0;
}
    :
        SIGNED_INT_TYPE
        {
            $ctx->p = (char *) $SIGNED_INT_TYPE.text->toStringz(ctx);
            while (*$ctx->p && !isdigit(*$ctx->p))
                ++ $ctx->p;
        }
        (
            '[' size=constant ']'
            {
                $ctx->array_size = $size.res->value();
                assert(0 < $ctx->array_size);
            }
        )?
    {
        $res = $ctx->array_size ?
            (type::Type_ptr) tm.find_signed_array(*$ctx->p ? atoi($ctx->p)
                : om.word_width(), $ctx->array_size) :
            (type::Type_ptr) tm.find_signed( *$ctx->p ? atoi($ctx->p)
                : om.word_width());
    }
    ;


instance_type returns [type::Type_ptr res]
@init {
}
    : module=identifier '(' parameters=params[&ev] ')'
      {
          expr::ExprVector ev;
          $res = tm.find_instance( $module.res, $parameters.res );
      }
    ;

literal returns [expr::Expr_ptr res]
@init { }
    :  expr=identifier
       { $res = $expr.res; }
    ;

// -- Scripting sub-system Toplevel ---------------------------------------------
command_line returns [cmd::CommandVector_ptr res]
@init {
    $res = new cmd::CommandVector();
}
    : commands[$res]
    ;

commands [cmd::CommandVector_ptr cmds]
    :
        c=command
        { cmds->push_back($c.res); }

        (
            ';' c2=command
            { cmds->push_back($c2.res); }
        )* ;

command_topic returns [cmd::CommandTopic_ptr res]
    :  c=check_command_topic
       { $res = $c.res; }

    |  c=check_init_command_topic
       { $res = $c.res; }

    |  c=check_trans_command_topic
       { $res = $c.res; }

    |  c=diameter_command_topic
       { $res = $c.res; }

    |  c=clear_command_topic
       { $res = $c.res; }

    |  c=do_command_topic
       { $res = $c.res; }

    |  c=dump_model_command_topic
        { $res = $c.res; }

    |  c=dump_traces_command_topic
        { $res = $c.res; }

    |  c=dup_trace_command_topic
        { $res = $c.res; }

    |  c=echo_command_topic
       { $res = $c.res; }

    |  c=get_command_topic
       { $res = $c.res; }

    |  c=help_command_topic
       { $res = $c.res; }

    |  c=last_command_topic
       { $res = $c.res; }

    |  c=list_traces_command_topic
       { $res = $c.res; }

    |  c=on_command_topic
       {$res = $c.res; }

    |  c=read_model_command_topic
       { $res = $c.res; }

    |  c=read_trace_command_topic
       { $res = $c.res; }

    |  c=pick_state_command_topic
       { $res = $c.res; }

    |  c=quit_command_topic
       { $res = $c.res; }

    |  c=reach_command_topic
       { $res = $c.res; }

    | c=select_trace_topic
      { $res = $c.res; }

    |  c=set_command_topic
       { $res = $c.res; }

    |  c=simulate_command_topic
       { $res = $c.res; }

    |  c=time_command_topic
       { $res = $c.res; }
    ;

command returns [cmd::Command_ptr res]
    :  c = check_command
       { $res = $c.res; }

    |  c=check_init_command
       { $res = $c.res; }

    |  c=check_trans_command
       { $res = $c.res; }

    |  c=clear_command
       { $res = $c.res; }

    |  c=diameter_command
        { $res = $c.res; }

    |  c=do_command
       { $res = $c.res; }

    |  c=dump_model_command
        { $res = $c.res; }

    |  c=dump_traces_command
        { $res = $c.res; }

    |  c=dup_trace_command
        { $res = $c.res; }

    |  c=echo_command
       { $res = $c.res; }

    |  c=get_command
       { $res = $c.res; }

    |  c=help_command
       { $res = $c.res; }

    |  c=last_command
       { $res = $c.res; }

    |  c=list_traces_command
       { $res = $c.res; }

    |  c=on_command
       {$res = $c.res; }

    |  c=read_model_command
       { $res = $c.res; }

    |  c=read_trace_command
       { $res = $c.res; }

    |  c=pick_state_command
       { $res = $c.res; }

    |  c=quit_command
       { $res = $c.res; }

    |  c=reach_command
       { $res = $c.res; }

    |  c=select_trace_command
       { $res = $c.res; }

    |  c=set_command
       { $res = $c.res; }

    |  c=simulate_command
       { $res = $c.res; }

    |  c=time_command
       { $res = $c.res; }
    ;

help_command returns [cmd::Command_ptr res]
    : 'help'
      { $res = cm.make_help(); }
      (
          topic = command_topic
          { ((cmd::Help_ptr) $res)->set_topic($topic.res); }
      )? ;

help_command_topic returns [cmd::CommandTopic_ptr res]
    : 'help'
      { $res = cm.topic_help(); }
    ;

do_command returns [cmd::Command_ptr res]
    : 'do'
      { $res = cm.make_do(); }
      (
            subcommand = command ';'
            { ((cmd::Do_ptr) $res)->add_command($subcommand.res); }
      )+ ;

do_command_topic returns [cmd::CommandTopic_ptr res]
    : 'do'
       { $res = cm.topic_do(); }
    ;

echo_command returns [cmd::Command_ptr res]
locals [
    expr::ExprVector ev;
]
    : 'echo'?
      { $res = cm.make_echo(); }
      (
            expr = toplevel_expression
            {
                ((cmd::Echo_ptr) $res) -> append_expression($expr.res);
            }
      )
      ;

echo_command_topic returns [cmd::CommandTopic_ptr res]
    : 'echo'
       { $res = cm.topic_echo(); }
    ;

last_command returns [cmd::Command_ptr res]
    : 'last'
      { $res = cm.make_last(); }
    ;

last_command_topic returns [cmd::CommandTopic_ptr res]
    : 'last'
       { $res = cm.topic_last(); }
    ;

on_command returns [cmd::Command_ptr res]
    :
      'on'
        ('success' { $res = cm.make_on(); }
            tc=command { ((cmd::On_ptr) $res)->set_then($tc.res); } |

          'failure' { $res = cm.make_on(); }
            ec=command { ((cmd::On_ptr) $res)->set_else($ec.res); } )
    ;

on_command_topic returns [cmd::CommandTopic_ptr res]
    : 'on'
        { $res = cm.topic_on(); }
    ;

time_command returns [cmd::Command_ptr res]
    : 'time'
      { $res = cm.make_time(); }
    ;

time_command_topic returns [cmd::CommandTopic_ptr res]
    : 'time'
      { $res = cm.topic_time(); }
    ;

read_model_command returns [cmd::Command_ptr res]
    :  'read-model'
        { $res = cm.make_read_model(); }

        ( input=pcchar_quoted_string {
            ((cmd::ReadModel_ptr) $res)->set_input($input.res);
        }) ?
    ;

read_model_command_topic returns [cmd::CommandTopic_ptr res]
    :  'read-model'
        { $res = cm.topic_read_model(); }
    ;

read_trace_command returns [cmd::Command_ptr res]
    :  'read-trace'
        { $res = cm.make_read_trace(); }

        ( input=pcchar_quoted_string {
            ((cmd::ReadTrace_ptr) $res)->set_input($input.res);
        }) ?
    ;

read_trace_command_topic returns [cmd::CommandTopic_ptr res]
    :  'read-trace'
        { $res = cm.topic_read_trace(); }
    ;

dump_model_command returns [cmd::Command_ptr res]
    :  'dump-model'
        { $res = cm.make_dump_model(); }

        ( '-o' output=pcchar_quoted_string {
            ((cmd::DumpModel_ptr) $res)->set_output($output.res);
        }

        | '-s' ('state' { ((cmd::DumpModel_ptr) $res)->select_state(); }
        |       'init'  { ((cmd::DumpModel_ptr) $res)->select_init();  }
        |       'trans' { ((cmd::DumpModel_ptr) $res)->select_trans(); })
        ) *
    ;

dump_model_command_topic returns [cmd::CommandTopic_ptr res]
    :  'dump-model'
        { $res = cm.topic_dump_model(); }
    ;

check_command returns[cmd::Command_ptr res]
    : 'check'
      { $res = cm.make_check(); }

      property=temporal_expression
      { ((cmd::Check_ptr) $res)->set_property($property.res); }

      ( '-c' constraint=temporal_expression
      { ((cmd::Check_ptr) $res)->add_constraint($constraint.res); })*
    ;

check_command_topic returns[cmd::CommandTopic_ptr res]
    : 'check'
       { $res = cm.topic_check(); }
    ;

check_init_command returns[cmd::Command_ptr res]
    : 'check-init'
      { $res = cm.make_check_init(); }

      ( '-c' constraint=toplevel_expression
      { ((cmd::CheckInit_ptr) $res)->add_constraint($constraint.res); })*
    ;

check_init_command_topic returns [cmd::CommandTopic_ptr res]
    :  'check-init'
        { $res = cm.topic_check_init(); }
    ;

diameter_command returns[cmd::Command_ptr res]
    : 'diameter'
      { $res = cm.make_diameter(); }
    ;

diameter_command_topic returns [cmd::CommandTopic_ptr res]
    :  'diameter'
        { $res = cm.topic_diameter(); }
    ;

reach_command returns[cmd::Command_ptr res]
    :   'reach'
        { $res = cm.make_reach(); }

        target=toplevel_expression
        { ((cmd::Reach_ptr) $res)->set_target($target.res); }

        ( '-q'
            { ((cmd::Reach_ptr) $res)->go_quiet(); }
        )*

        ( '-c' constraint=toplevel_expression
          { ((cmd::Reach_ptr) $res)->add_constraint($constraint.res); }
        )*
    ;

reach_command_topic returns [cmd::CommandTopic_ptr res]
    :  'reach'
        { $res = cm.topic_reach(); }
    ;

select_trace_command returns[cmd::Command_ptr res]
    :   'select-trace'
        { $res = cm.make_select_trace(); }

        trace_id=pcchar_identifier
        { ((cmd::SelectTrace_ptr) $res)->set_trace_id($trace_id.res); }
    ;

select_trace_topic returns [cmd::CommandTopic_ptr res]
    :  'select-trace'
       { $res = cm.topic_select_trace(); }
    ;

check_trans_command returns[cmd::Command_ptr res]
    : 'check-trans'
      { $res = cm.make_check_trans(); }

      ( '-c' constraint=toplevel_expression
      { ((cmd::CheckTrans_ptr) $res)->add_constraint($constraint.res); })*
    ;

check_trans_command_topic returns [cmd::CommandTopic_ptr res]
    :  'check-trans'
        { $res = cm.topic_check_trans(); }
    ;

list_traces_command returns [cmd::Command_ptr res]
    : 'list-traces'
      { $res = cm.make_list_traces(); }
    ;

list_traces_command_topic returns [cmd::CommandTopic_ptr res]
    :  'list-traces'
        { $res = cm.topic_list_traces(); }
    ;

dump_traces_command returns [cmd::Command_ptr res]
    : 'dump-traces'
      { $res = cm.make_dump_traces(); }

    (
      '-a'
      { ((cmd::DumpTraces_ptr) $res)->set_all(true); }
    |
      '-f' format=pcchar_identifier
      { ((cmd::DumpTraces_ptr) $res)->set_format($format.res); }

    | '-o' output=pcchar_quoted_string
      {
            ((cmd::DumpTraces_ptr) $res)->set_output($output.res);
      }
    )*

    ( trace_id=pcchar_identifier
    { ((cmd::DumpTraces_ptr) $res)->add_trace_id($trace_id.res); } )*
    ;

dump_traces_command_topic returns [cmd::CommandTopic_ptr res]
    :  'dump-traces'
        { $res = cm.topic_dump_traces(); }
    ;


dup_trace_command returns [cmd::Command_ptr res]
    : 'dup-trace'
      { $res = cm.make_dup_trace(); }

      trace_id=pcchar_identifier
      { ((cmd::DupTrace_ptr) $res)->set_trace_id($trace_id.res); }

      ( duplicate_uid=pcchar_identifier
        { ((cmd::DupTrace_ptr) $res)->set_duplicate_id($duplicate_uid.res); } )?
    ;

dup_trace_command_topic returns [cmd::CommandTopic_ptr res]
    :  'dup-trace'
        { $res = cm.topic_dup_trace(); }
    ;

pick_state_command returns [cmd::Command_ptr res]
    :   'pick-state'
        { $res = cm.make_pick_state(); }
    (
         '-a'
         { ((cmd::PickState_ptr) $res)->set_allsat(true); }

    |    '-n'
        { ((cmd::PickState_ptr) $res)->set_count(true); }

    |    '-l' limit=constant
         { ((cmd::PickState_ptr) $res)->set_limit($limit.res->value()); }

    |    '-c' constraint=toplevel_expression
         { ((cmd::PickState_ptr) $res)->add_constraint($constraint.res); }
    )* ;

pick_state_command_topic returns [cmd::CommandTopic_ptr res]
    :  'pick-state'
        { $res = cm.topic_pick_state(); }
    ;

simulate_command returns [cmd::Command_ptr res]
    : 'simulate'
      { $res = cm.make_simulate(); }
    (
       '-i' invar_condition=toplevel_expression
        { ((cmd::Simulate_ptr) $res)->set_invar_condition($invar_condition.res); }

    |  '-u' until_condition=toplevel_expression
        { ((cmd::Simulate_ptr) $res)->set_until_condition($until_condition.res); }

    |   '-k' konst=constant
        { ((cmd::Simulate_ptr) $res)->set_k($konst.res->value()); }

    |   '-t' trace_id=pcchar_identifier
        { ((cmd::Simulate_ptr) $res)->set_trace_uid($trace_id.res); }
    )* ;

simulate_command_topic returns [cmd::CommandTopic_ptr res]
    :  'simulate'
        { $res = cm.topic_simulate(); }
    ;

get_command returns [cmd::Command_ptr res]
    : 'get'
      { $res = cm.make_get(); }

      ( id=identifier
      { ((cmd::Get_ptr) $res)->set_identifier($id.res); })?
    ;

get_command_topic returns [cmd::CommandTopic_ptr res]
    :  'get'
        { $res = cm.topic_get(); }
    ;

set_command returns [cmd::Command_ptr res]
    : 'set'
      { $res = cm.make_set(); }

      id=identifier
      { ((cmd::Set_ptr) $res)->set_identifier($id.res); }

      val=toplevel_expression
      { ((cmd::Set_ptr) $res)->set_value($val.res); }
    ;

set_command_topic returns [cmd::CommandTopic_ptr res]
    :  'set'
        { $res = cm.topic_set(); }
    ;

clear_command returns [cmd::Command_ptr res]
    : 'clear'
      { $res = cm.make_clear(); }

      ( id=identifier
      { ((cmd::Clear_ptr) $res)->set_identifier($id.res); })?
    ;

clear_command_topic returns [cmd::CommandTopic_ptr res]
    :  'clear'
        { $res = cm.topic_clear(); }
    ;

quit_command returns [cmd::Command_ptr res]
    :  'quit'
       { $res = cm.make_quit(); }
    ;

quit_command_topic returns [cmd::CommandTopic_ptr res]
    :  'quit'
        { $res = cm.topic_quit(); }
    ;

pcchar_identifier returns [pconst_char res]
@init {}
    : IDENTIFIER
      { $res = (pconst_char) $IDENTIFIER.text->toStringz(ctx); }
    ;

pcchar_quoted_string returns [pconst_char res]
    : QUOTED_STRING
        {
            pANTLR3_UINT8 p = $QUOTED_STRING.text->toStringz(ctx);
            pANTLR3_UINT8 q; for (q = p; *q; ++ q) ;

            assert (*p == '\'' || *p == '\"');
            p ++ ;  /* cut lhs quote */

            q -- ;
            assert (*q == '\'' || *q == '\"');
            *q = 0; /* cut rhs quote */

            $res = (pconst_char) p; // $QUOTED_STRING.text->toStringz(ctx);
        }
    ;

// -- Lexer rules --------------------------------------------------------------
UNSIGNED_INT_TYPE
    :  'uint' TYPE_WIDTH?
    ;

SIGNED_INT_TYPE
    :  'int' TYPE_WIDTH?
    ;

IDENTIFIER
    :   ID_FIRST_CHAR (ID_FOLLOWING_CHARS)*
    ;

QUOTED_STRING
    : '"' .*? '"'
    | '\'' .*? '\''
    ;

fragment TYPE_WIDTH
    : DECIMAL_LITERAL
    ;

fragment ID_FIRST_CHAR
    :   'A'..'Z'
    |   'a'..'z'
    |    '_'
    ;

fragment ID_FOLLOWING_CHARS
    :    ID_FIRST_CHAR
    |    DECIMAL_DIGIT
    |    '-'
    |    '#'
    |    '$'
    ;

HEX_LITERAL
   : ZERO ('x'|'X') HEX_DIGIT+
   ;

DECIMAL_LITERAL
   : ZERO | DECIMAL_FIRST DECIMAL_DIGIT*
   ;

OCTAL_LITERAL
   : ZERO OCTAL_DIGIT+
   ;

BINARY_LITERAL
   : ZERO ('b'|'B') BINARY_DIGIT+
   ;

fragment BINARY_DIGIT
   : ZERO | '1'
   ;

fragment OCTAL_DIGIT
   : ZERO | '1' .. '7'
   ;

fragment DECIMAL_FIRST
   : '1' .. '9'
   ;

fragment DECIMAL_DIGIT
   :  OCTAL_DIGIT | '8' | '9'
   ;

fragment HEX_DIGIT
   :  DECIMAL_DIGIT | 'a'..'f' | 'A'..'F'
   ;

fragment ZERO
   : '0'
   ;

WS
   : (' '|'\r'|'\t'|'\u000C'|'\n') -> channel(HIDDEN)
   ;

LINE_COMMENT
   : ( '//' | '--' ) ~('\n'|'\r')* '\r'? '\n' -> channel(HIDDEN)
   ;
