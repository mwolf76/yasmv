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


using namespace std;
using namespace expr;
using namespace model;
using namespace type;
using namespace opts;
using namespace cmd;

@parser::members {
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
      { smv_model.add_module(* ($current_module.res = new model::Module(module_id))); }

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
    $hidden.res = 0;
    $input.res = 0;
    $frozen.res = 0;
    $inertial.res = 0;

    $format.res = FORMAT_DEFAULT;
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
              'hidden'   { $hidden.res = 1; }
            | 'frozen'   { $frozen.res = 1; }
            | 'inertial' { $inertial.res = 1; }
            | 'input'    { $input.res = 1; }

            | 'bin' { $format.res = FORMAT_BINARY;      }
            | 'oct' { $format.res = FORMAT_OCTAL;       }
            | 'dec' { $format.res = FORMAT_DECIMAL;     }
            | 'hex' { $format.res = FORMAT_HEXADECIMAL; }
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
            assert(NULL != tp);
            for (expr_iter = ev.begin(); expr_iter != ev.end(); ++ expr_iter) {
                expr::Expr_ptr vid (*expr_iter);
                symb::Variable_ptr var
                    (new symb::Variable($current_module->name(), vid, tp));

                if ($hidden)
                    var->set_hidden(true);
                if ($input)
                    var->set_input(true);
                if ($inertial)
                    var->set_inertial(true);
                if ($frozen)
                    var->set_frozen(true);

                if ($format != FORMAT_DEFAULT)
                    var->set_format($format);

                $current_module->add_var(vid, var);
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
            assert(NULL != tp);
            for (expr_iter = ev.begin(); expr_iter != ev.end(); ++ expr_iter) {
                expr::Expr_ptr pid (*expr_iter);
                $current_module->add_parameter(pid,
                                                    new symb::Parameter($current_module->name(),
                                                                        pid, tp));
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
          new symb::Define($current_module->name(), id, body);

      if ($input)
          throw SyntaxError("#input modifier not supported in DEFINE decls");

      if ($frozen)
          throw SyntaxError("#frozen modifier not supported in DEFINE decls");

      if ($inertial)
          throw SyntaxError("#inertial modifier not supported in DEFINE decls");

      if ($hidden)
          def->set_hidden(true);

      /* these are mutually exclusive, default is hexadecimal */
      if ($format != FORMAT_DEFAULT)
          def->set_format($format);

      $current_module->add_def(id, def);
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
      { $current_module->add_init(expr); }
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
      { $current_module->add_invar(expr); }
    ;

fsm_trans_decl
    : 'TRANS' fsm_trans_decl_body
    ;

fsm_trans_decl_body
    : fsm_trans_decl_clause
        (';' fsm_trans_decl_clause)*
    ;

fsm_trans_decl_clause
    :
        lhs=toplevel_expression '?:' rhs=toplevel_expression
      { $current_module->add_trans(em.make_guard(lhs, rhs)); }

    | rhs=toplevel_expression
      { $current_module->add_trans(em.make_guard(em.make_true(), rhs)); }
    ;

toplevel_expression returns [expr::Expr_ptr res]
    : expr=timed_expression
      { $res.res = expr; }
    ;

timed_expression returns [expr::Expr_ptr res]
@init {
    expr::Expr_ptr a { NULL };
    expr::Expr_ptr b { NULL };
}
    : '@' time=forward_instant { a = time; } ('.*?' time=forward_instant { b = time; })? '{' body=temporal_expression '}'
      { $res.res = (NULL != b) ? em.make_at( em.make_interval(a, b),  body) : em.make_at(a, body); }

    | '$' time=backward_instant { a = time; } ('.*?' time=backward_instant { b = time; })? '{' body=temporal_expression '}'
      { $res.res = (NULL != b) ? em.make_at( em.make_interval(a, b),  body) : em.make_at(a, body); }

    | body=temporal_expression
      { $res.res = body; }
    ;

temporal_expression returns [expr::Expr_ptr res]
    : expr=binary_ltl_expression
      { $res.res = expr; }
    ;

binary_ltl_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=unary_ltl_expression
      { $res.res = lhs; } (
            'U' rhs=unary_ltl_expression
            { $res.res = em.make_U($res, rhs); }

        |   'R' rhs=unary_ltl_expression
            { $res.res = em.make_R($res, rhs); }
      )* ;

unary_ltl_expression returns [expr::Expr_ptr res]
@init { }
    : 'G' expr=unary_ltl_expression
        { $res.res = em.make_G(expr); }

    | 'F' expr=unary_ltl_expression
        { $res.res = em.make_F(expr); }

    | 'X' expr=unary_ltl_expression
        { $res.res = em.make_X(expr); }

    /* common shortcuts */
    | 'GF' expr=unary_ltl_expression
        { $res.res = em.make_G(em.make_F(expr)); }

    | 'GX' expr=unary_ltl_expression
        { $res.res = em.make_G(em.make_X(expr)); }

    | 'FG' expr=unary_ltl_expression
        { $res.res = em.make_F(em.make_G(expr)); }

    | 'FX' expr=unary_ltl_expression
        { $res.res = em.make_F(em.make_X(expr)); }

    | 'XG' expr=unary_ltl_expression
        { $res.res = em.make_X(em.make_G(expr)); }

    | 'XF' expr=unary_ltl_expression
        { $res.res = em.make_X(em.make_F(expr)); }

    | expr=propositional_expression
      { $res.res = expr; }
    ;

propositional_expression returns [expr::Expr_ptr res]
@init { }
    : expr=ite_expression {
         $res.res = expr;
      }
    ;

ite_expression returns [expr::Expr_ptr res]
@init { }
    : expr=logical_expression {
         $res.res = expr;
      }

      (
            '?' lhs=logical_expression ':' rhs=logical_expression
            { $res.res = em.make_ite( em.make_cond($res, lhs), rhs); }
      )?
    ;

logical_expression returns [expr::Expr_ptr res]
    : expr=logical_implies_expression
      { $res.res = expr; }
    ;

logical_implies_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=logical_or_expression
      { $res.res = lhs; }

    (
      '->' rhs=logical_or_expression
      { $res.res = em.make_implies($res, rhs); }
    )* ;

logical_or_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=logical_and_expression
      { $res.res = lhs; }

    (
      '||' rhs=logical_and_expression
      { $res.res = em.make_or($res, rhs); }
    )* ;

logical_and_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=equality_expression
      { $res.res = lhs; }

    (
      '&&' rhs=equality_expression
      { $res.res = em.make_and($res, rhs); }
    )* ;

equality_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=relational_expression
      { $res.res = lhs; }

      ( '=' rhs=relational_expression
            { $res.res = em.make_eq($res, rhs); }

      | '!=' rhs=relational_expression
            { $res.res = em.make_ne($res, rhs); }

      | ':=' rhs=relational_expression
            { $res.res = em.make_assignment($res, rhs); }

      )? /* predicates are binary */;

relational_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=algebraic_expression
      { $res.res = lhs; }

      ( '<' rhs=algebraic_expression
            { $res.res = em.make_lt($res, rhs); }

      | '<=' rhs=algebraic_expression
            { $res.res = em.make_le($res, rhs); }

      | '>=' rhs=algebraic_expression
            { $res.res = em.make_ge($res, rhs); }

      | '>' rhs=algebraic_expression
            { $res.res = em.make_gt($res, rhs); }
      )? /* predicates are binary */ ;

algebraic_expression returns [expr::Expr_ptr res]
@init { }
    :
        expr=bw_or_expression
        { $res.res = expr; }
    ;

bw_or_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=bw_xor_expression
      { $res.res = lhs; }

    (
      '|' rhs=bw_xor_expression
       { $res.res = em.make_bw_or($res, rhs); }
    )* ;

bw_xor_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=bw_xnor_expression
      { $res.res = lhs; }

    (
      '^' rhs=bw_xnor_expression
      { $res.res = em.make_bw_xor($res, rhs); }
    )* ;

bw_xnor_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=bw_and_expression
      { $res.res = lhs; }

    (
      '<->' rhs=bw_and_expression
      { $res.res = em.make_bw_xnor($res, rhs); }
    )* ;

bw_and_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=shift_expression
      { $res.res = lhs; }

    (
      '&' rhs=shift_expression
      { $res.res = em.make_bw_and($res, rhs); }
    )* ;

shift_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=additive_expression
      { $res.res = lhs; }

    (
      '<<' rhs=additive_expression
      { $res.res = em.make_lshift($res, rhs); }

    | '>>' rhs=additive_expression
       { $res.res = em.make_rshift($res, rhs); }
    )* ;

additive_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=multiplicative_expression
      { $res.res = lhs; }

    (
        '+' rhs=multiplicative_expression
        { $res.res = em.make_add($res, rhs); }

    |   '-' rhs=multiplicative_expression
        { $res.res = em.make_sub($res, rhs); }
    )* ;

multiplicative_expression returns [expr::Expr_ptr res]
@init { }
    : lhs=cast_expression
      { $res.res = lhs; }

    (
      '*' rhs=cast_expression
      { $res.res = em.make_mul($res, rhs); }

    | '/' rhs=cast_expression
      { $res.res = em.make_div($res, rhs); }

    | '%' rhs=cast_expression
      { $res.res = em.make_mod($res, rhs); }
    )* ;

cast_expression returns [expr::Expr_ptr res]
@init {
    expr::Expr_ptr cast = NULL;
}
    : '(' tp = native_type ')' expr = cast_expression
        { $res.res = em.make_cast( tp->repr(), expr ); }
    |
        expr = unary_expression
        { $res.res = expr; }
    ;

unary_expression returns [expr::Expr_ptr res]
@init { }
    : expr=postfix_expression
      { $res.res = expr; }

    | expr=nondeterministic_expression
      { $res.res = expr; }

    | expr=array_expression
      { $res.res = expr; }

    | 'next' '(' expr=toplevel_expression ')'
      { $res.res = em.make_next(expr); }

    | '!' expr=postfix_expression
      { $res.res = em.make_not(expr); }

    | '~' expr=postfix_expression
      { $res.res = em.make_bw_not(expr); }

    | '-' expr=postfix_expression
      { $res.res = em.make_neg(expr); }
    ;

nondeterministic_expression returns [expr::Expr_ptr res]
@init {
    bool is_range { false };
    expr::ExprVector clauses;
}
    : '{'
          c=toplevel_expression{ clauses.push_back(c); }
        (  ','  c=toplevel_expression { clauses.push_back(c); }
        | '.*?' c=toplevel_expression  { assert(!is_range); is_range = true; clauses.push_back(c); } )+
      '}'
      {
            if (!is_range) {
                expr::ExprVector::reverse_iterator i { clauses.rbegin() };
                while (clauses.rend() != i) {
                    $res.res = $res ? em.make_set_comma( *i, $res) : *i;
                    ++ i;
                }
            } else {
               expr::ExprVector::iterator lhs { clauses.begin() };
               expr::Expr_ptr lhs_expr { *lhs };
               assert (em.is_constant(lhs_expr));
               value_t start { $lhs_expr.res->value() };

               expr::ExprVector::reverse_iterator rhs { clauses.rbegin() };
               expr::Expr_ptr rhs_expr { *rhs };
               assert (em.is_constant(rhs_expr));
               value_t stop { $rhs_expr.res->value() };

               // ensure lhs <= rhs
               if (start > stop) {
                   value_t tmp { start };
                   start = stop;
                   stop  = tmp;
               }

               // create set interval
               for (value_t i = stop; i >= start; i -- ) {
                   $res.res = $res
                       ? em.make_set_comma(em.make_const(i), $res)
                       : em.make_const(i)
                       ;
               }
            }

            $res.res = em.make_set( $res );
      }
      ;

array_expression returns [expr::Expr_ptr res]
@init {
    expr::ExprVector clauses;
}
    : '['
          c=toplevel_expression{ clauses.push_back(c); }
            (',' c=toplevel_expression { clauses.push_back(c); })*
      ']'
      {
            expr::ExprVector::reverse_iterator i
                (clauses.rbegin());

            while (clauses.rend() != i) {
                $res.res = $res ? em.make_array_comma( *i, $res) : *i;
                ++ i;
            }

            $res.res = em.make_array( $res );
        }
    ;


params returns [expr::Expr_ptr res]
@init {
    expr::ExprVector actuals;
    res = NULL;
}
    : ( expressions[&actuals]
    {
            expr::ExprVector::reverse_iterator expr_iter;
            res = NULL;

            for (expr_iter = actuals.rbegin(); expr_iter != actuals.rend(); ++ expr_iter) {
                expr::Expr_ptr expr = (*expr_iter);
                res = (!res) ? expr : em.make_params_comma( expr, res );
            }
    })?

    {
      if (! res)
          res = em.make_empty();
    }
    ;

postfix_expression returns [expr::Expr_ptr res]
@init { }
    :   lhs=basic_expression
        { $res.res = lhs; }

    (
        '[' rhs=toplevel_expression ']'
        { $res.res = em.make_subscript($res, rhs); }
    |
        '(' rhs=params ')'
        { $res.res = em.make_params($res, rhs); }

    |   '.*?' rhs=identifier
        { $res.res = em.make_dot($res, rhs); }
    )* ;

basic_expression returns [expr::Expr_ptr res]
@init { }
    : id=identifier
      { $res.res = id; }

    | k=constant
      { $res.res = k; }

    | '(' expr=toplevel_expression ')'
      { $res.res = expr; }

    | expr=case_expression
      { $res.res = expr; }
    ;

case_expression returns [expr::Expr_ptr res]
@init {
    typedef std::pair<expr::Expr_ptr, expr::Expr_ptr> CaseClause;
    typedef std::vector<CaseClause> CaseClauses;

    CaseClauses clauses;
}  : 'case'

     (lhs=toplevel_expression ':' rhs=toplevel_expression ';'
     { clauses.push_back( std::pair< expr::Expr_ptr, expr::Expr_ptr > (lhs, rhs)); }) +

     'else' ':' last=toplevel_expression ';'
     { clauses.push_back( std::pair< expr::Expr_ptr, expr::Expr_ptr > (NULL, last)); }

     'end'
     {
        CaseClauses::reverse_iterator i = clauses.rbegin();
        res = i->second;
        while (1) {
            if ( ++ i == clauses.rend())
                break;
            $res.res = em.make_ite( em.make_cond(i->first,
                                             i->second), $res);
        }
     }
    ;

identifiers [expr::ExprVector* ids]
    :
      ident=identifier
      { ids->push_back(ident); }

      ( ',' ident=identifier
            { ids->push_back(ident); }
      )* ;

expressions [expr::ExprVector* exprs]
    :
      expr=toplevel_expression
      { exprs->push_back(expr); }

      ( ',' expr=toplevel_expression
            { exprs->push_back(expr); }
      )* ;

identifier returns [expr::Expr_ptr res]
@init { }
    : IDENTIFIER
      { $res.res = em.make_identifier((const char*)($IDENTIFIER.text)); }
    ;

forward_instant returns [expr::Expr_ptr res]
@init { }
    : DECIMAL_LITERAL {
        expr::Atom tmp((const char*)($DECIMAL_LITERAL.text));
        $res.res = em.make_instant(strtoll(tmp.c_str(), NULL, 10));
      }
    ;

backward_instant returns [expr::Expr_ptr res]
@init { }
    : DECIMAL_LITERAL {
        expr::Atom tmp((const char*)($DECIMAL_LITERAL.text));
        $res.res = em.make_instant(UINT_MAX - strtoll(tmp.c_str(), NULL, 10));
      }
    ;

constant returns [expr::Expr_ptr res]
@init { }
    : HEX_LITERAL {
        expr::Atom tmp((const char*)($HEX_LITERAL.text));
        $res.res = em.make_hex_const(tmp);
      }

    | BINARY_LITERAL {
        expr::Atom tmp((const char*)($BINARY_LITERAL.text));
        $res.res = em.make_bin_const(tmp);
      }

    | OCTAL_LITERAL {
        expr::Atom tmp((const char*)($OCTAL_LITERAL.text));
        $res.res = em.make_oct_const(tmp);
      }

    | DECIMAL_LITERAL {
        expr::Atom tmp((const char*)($DECIMAL_LITERAL.text));
        $res.res = em.make_dec_const(tmp);
      }

    | QUOTED_STRING {
            pANTLR3_UINT8 p = $QUOTED_STRING.text;
            pANTLR3_UINT8 q; for (q = p; *q; ++ q) ;

            assert (*p == '\'' || *p == '\"');
            p ++ ;  /* cut lhs quote */

            q -- ;
            assert (*q == '\'' || *q == '\"');
            *q = 0; /* cut rhs quote */

            expr::Atom atom { (const char *) p };
            $res.res = em.make_qstring(atom);
      }
    ;

/* pvalue is used in param passing (actuals) */
pvalue returns [expr::Expr_ptr res]
@init {}
    : 'next' '(' expr=postfix_expression ')'
      { $res.res = em.make_next(expr); }

    | expr=postfix_expression
      { $res.res = expr; }
    ;

/* ordinary values used elsewhere */
value returns [expr::Expr_ptr res]
@init { }
    : expr=postfix_expression
      { $res.res = expr; }
    ;

/* typedecls */
smv_type returns [type::Type_ptr res]
@init {}
    : tp = native_type
      { $res.res = tp; }

    | tp = enum_type
      { $res.res = tp; }

    | tp = instance_type
      { $res.res = tp; }
    ;

native_type returns [type::Type_ptr res]
@init {}
    : tp = boolean_type
      { $res.res = tp; }

    | tp = unsigned_int_type
      { $res.res = tp; }

    | tp = signed_int_type
      { $res.res = tp; }
    ;

boolean_type returns [type::Type_ptr res]
@init {
    int array_size = 0;
}
    : 'boolean' (

            '[' size=constant ']'
            {
                array_size = $size.res->value();
                assert(0 < array_size);
            }
    ) ?
    {
        $res.res = array_size ?
            (type::Type_ptr) tm.find_boolean_array(array_size) :
            (type::Type_ptr) tm.find_boolean();
    }
    ;

enum_type returns [type::Type_ptr res]
@init {
    int array_size = 0;
    expr::ExprSet lits;
}
    : '{'
          lit=literal { lits.insert(lit); }
              (',' lit=literal { lits.insert(lit); })*
      '}' (
            '[' size=constant ']'
            {
                array_size = $size.res->value();
                assert(0 < array_size);
            }
    ) ?
    {
        $res.res = array_size ?
            (type::Type_ptr) tm.find_enum_array(lits, array_size) :
            (type::Type_ptr) tm.find_enum(lits);
    }
    ;

unsigned_int_type returns [type::Type_ptr res]
@init {
    int array_size = 0;
    char *p;
}
    :
        UNSIGNED_INT_TYPE
        {
            p = (char *) $UNSIGNED_INT_TYPE.text;
            while (*p && !isdigit(*p))
                ++ p;
        }
        (
            '[' size=constant ']'
            {
                array_size = $size.res->value();
                assert(0 < array_size);
            }
    ) ?
    {
        $res.res = array_size ?
            (type::Type_ptr) tm.find_unsigned_array(*p ? atoi(p)
                : om.word_width(), array_size) :
            (type::Type_ptr) tm.find_unsigned( *p ? atoi(p)
                : om.word_width());
    }
    ;

signed_int_type returns [type::Type_ptr res]
@init {
    int array_size = 0;
    char *p;
}
    :
        SIGNED_INT_TYPE
        {
            p = (char *) $SIGNED_INT_TYPE.text;
            while (*p && !isdigit(*p))
                ++ p;
        }
        (
            '[' size=constant ']'
            {
                array_size = $size.res->value();
                assert(0 < array_size);
            }
        )?
    {
        $res.res = array_size ?
            (type::Type_ptr) tm.find_signed_array(*p ? atoi(p)
                : om.word_width(), array_size) :
            (type::Type_ptr) tm.find_signed( *p ? atoi(p)
                : om.word_width());
    }
    ;


instance_type returns [type::Type_ptr res]
@init {
}
    : module=identifier '(' parameters=params ')'
      { $res.res = tm.find_instance( module, parameters ); }
    ;

literal returns [expr::Expr_ptr res]
@init { }
    :  expr=identifier
       { $res.res = expr; }
    ;

// -- Scripting sub-system Toplevel ---------------------------------------------
command_line returns [cmd::CommandVector_ptr res]
@init {
    res = new cmd::CommandVector();
}
    : commands[res]
    ;

commands [cmd::CommandVector_ptr cmds]
    :
        c=command
        { cmds->push_back(c); }

        (
            ';' c=command
            { cmds->push_back(c); }
        )* ;

command_topic returns [cmd::CommandTopic_ptr res]
    :  c=check_command_topic
       { $res.res = c; }

    |  c=check_init_command_topic
       { $res.res = c; }

    |  c=check_trans_command_topic
       { $res.res = c; }

    |  c=diameter_command_topic
       { $res.res = c; }

    |  c=clear_command_topic
       { $res.res = c; }

    |  c=do_command_topic
       { $res.res = c; }

    |  c=dump_model_command_topic
        { $res.res = c; }

    |  c=dump_traces_command_topic
        { $res.res = c; }

    |  c=dup_trace_command_topic
        { $res.res = c; }

    |  c=echo_command_topic
       { $res.res = c; }

    |  c=get_command_topic
       { $res.res = c; }

    |  c=help_command_topic
       { $res.res = c; }

    |  c=last_command_topic
       { $res.res = c; }

    |  c=list_traces_command_topic
       { $res.res = c; }

    |  c=on_command_topic
       {$res.res = c; }

    |  c=read_model_command_topic
       { $res.res = c; }

    |  c=read_trace_command_topic
       { $res.res = c; }

    |  c=pick_state_command_topic
       { $res.res = c; }

    |  c=quit_command_topic
       { $res.res = c; }

    |  c=reach_command_topic
       { $res.res = c; }

    | c=select_trace_topic
      { $res.res = c; }

    |  c=set_command_topic
       { $res.res = c; }

    |  c=simulate_command_topic
       { $res.res = c; }

    |  c=time_command_topic
       { $res.res = c; }
    ;

command returns [cmd::Command_ptr res]
    :  c = check_command
       { $res.res = c; }

    |  c=check_init_command
       { $res.res = c; }

    |  c=check_trans_command
       { $res.res = c; }

    |  c=clear_command
       { $res.res = c; }

    |  c=diameter_command
        { $res.res = c; }

    |  c=do_command
       { $res.res = c; }

    |  c=dump_model_command
        { $res.res = c; }

    |  c=dump_traces_command
        { $res.res = c; }

    |  c=dup_trace_command
        { $res.res = c; }

    |  c=echo_command
       { $res.res = c; }

    |  c=get_command
       { $res.res = c; }

    |  c=help_command
       { $res.res = c; }

    |  c=last_command
       { $res.res = c; }

    |  c=list_traces_command
       { $res.res = c; }

    |  c=on_command
       {$res.res = c; }

    |  c=read_model_command
       { $res.res = c; }

    |  c=read_trace_command
       { $res.res = c; }

    |  c=pick_state_command
       { $res.res = c; }

    |  c=quit_command
       { $res.res = c; }

    |  c=reach_command
       { $res.res = c; }

    |  c=select_trace_command
       { $res.res = c; }

    |  c=set_command
       { $res.res = c; }

    |  c=simulate_command
       { $res.res = c; }

    |  c=time_command
       { $res.res = c; }
    ;

help_command returns [cmd::Command_ptr res]
    : 'help'
      { $res.res = cm.make_help(); }
      (
          topic = command_topic
          { ((cmd::Help_ptr) $res)->set_topic(topic); }
      )? ;

help_command_topic returns [cmd::CommandTopic_ptr res]
    : 'help'
      { $res.res = cm.topic_help(); }
    ;

do_command returns [cmd::Command_ptr res]
    : 'do'
      { $res.res = cm.make_do(); }
      (
            subcommand = command ';'
            { ((cmd::Do_ptr) res)->add_command(subcommand); }
      )+ ;

do_command_topic returns [cmd::CommandTopic_ptr res]
    : 'do'
       { $res.res = cm.topic_do(); }
    ;

echo_command returns [cmd::Command_ptr res]
@init {
    expr::ExprVector ev;
}
    : 'echo'?
      { $res.res = cm.make_echo(); }
      (
            expr = toplevel_expression
            {
                ((cmd::Echo_ptr) $res) -> append_expression(expr);
            }
      )
      ;

echo_command_topic returns [cmd::CommandTopic_ptr res]
    : 'echo'
       { $res.res = cm.topic_echo(); }
    ;

last_command returns [cmd::Command_ptr res]
    : 'last'
      { $res.res = cm.make_last(); }
    ;

last_command_topic returns [cmd::CommandTopic_ptr res]
    : 'last'
       { $res.res = cm.topic_last(); }
    ;

on_command returns [cmd::Command_ptr res]
    :
      'on'
        ('success' { $res.res = cm.make_on(); }
            tc=command { ((cmd::On_ptr) $res)->set_then(tc); } |

          'failure' { $res.res = cm.make_on(); }
            ec=command { ((cmd::On_ptr) $res)->set_else(ec); } )
    ;

on_command_topic returns [cmd::CommandTopic_ptr res]
    : 'on'
        { $res.res = cm.topic_on(); }
    ;

time_command returns [cmd::Command_ptr res]
    : 'time'
      { $res.res = cm.make_time(); }
    ;

time_command_topic returns [cmd::CommandTopic_ptr res]
    : 'time'
      { $res.res = cm.topic_time(); }
    ;

read_model_command returns [cmd::Command_ptr res]
    :  'read-model'
        { $res.res = cm.make_read_model(); }

        ( input=pcchar_quoted_string {
            ((cmd::ReadModel_ptr) $res)->set_input(input);
        }) ?
    ;

read_model_command_topic returns [cmd::CommandTopic_ptr res]
    :  'read-model'
        { $res.res = cm.topic_read_model(); }
    ;

read_trace_command returns [cmd::Command_ptr res]
    :  'read-trace'
        { $res.res = cm.make_read_trace(); }

        ( input=pcchar_quoted_string {
            ((cmd::ReadTrace_ptr) $res)->set_input(input);
        }) ?
    ;

read_trace_command_topic returns [cmd::CommandTopic_ptr res]
    :  'read-trace'
        { $res.res = cm.topic_read_trace(); }
    ;

dump_model_command returns [cmd::Command_ptr res]
    :  'dump-model'
        { $res.res = cm.make_dump_model(); }

        ( '-o' output=pcchar_quoted_string {
            ((cmd::DumpModel_ptr) $res)->set_output(output);
        }

        | '-s' ('state' { ((cmd::DumpModel_ptr) $res)->select_state(); }
        |       'init'  { ((cmd::DumpModel_ptr) $res)->select_init();  }
        |       'trans' { ((cmd::DumpModel_ptr) $res)->select_trans(); })
        ) *
    ;

dump_model_command_topic returns [cmd::CommandTopic_ptr res]
    :  'dump-model'
        { $res.res = cm.topic_dump_model(); }
    ;

check_command returns [cmd::Command_ptr res]
    : 'check'
      { $res.res = cm.make_check(); }

      property=temporal_expression
      { ((cmd::Check_ptr) $res)->set_property(property); }

      ( '-c' constraint=temporal_expression
      { ((cmd::Check_ptr) $res)->add_constraint(constraint); })*
    ;

check_command_topic returns [cmd::CommandTopic_ptr res]
    : 'check'
       { $res.res = cm.topic_check(); }
    ;

check_init_command returns [cmd::Command_ptr res]
    : 'check-init'
      { $res.res = cm.make_check_init(); }

      ( '-c' constraint=toplevel_expression
      { ((cmd::CheckInit_ptr) $res)->add_constraint(constraint); })*
    ;

check_init_command_topic returns [cmd::CommandTopic_ptr res]
    :  'check-init'
        { $res.res = cm.topic_check_init(); }
    ;

diameter_command returns [cmd::Command_ptr res]
    : 'diameter'
      { $res.res = cm.make_diameter(); }
    ;

diameter_command_topic returns [cmd::CommandTopic_ptr res]
    :  'diameter'
        { $res.res = cm.topic_diameter(); }
    ;

reach_command returns [cmd::Command_ptr res]
    :   'reach'
        { $res.res = cm.make_reach(); }

        target=toplevel_expression
        { ((cmd::Reach_ptr) $res)->set_target(target); }

        ( '-q'
            { ((cmd::Reach_ptr) $res)->go_quiet(); }
        )*

        ( '-c' constraint=toplevel_expression
          { ((cmd::Reach_ptr) $res)->add_constraint(constraint); }
        )*
    ;

reach_command_topic returns [cmd::CommandTopic_ptr res]
    :  'reach'
        { $res.res = cm.topic_reach(); }
    ;

select_trace_command returns [cmd::Command_ptr res]
    :   'select-trace'
        { $res.res = cm.make_select_trace(); }

        trace_id=pcchar_identifier
        { ((cmd::SelectTrace_ptr) $res)->set_trace_id(trace_id); }
    ;

select_trace_topic returns [cmd::CommandTopic_ptr res]
    :  'select-trace'
       { $res.res = cm.topic_select_trace(); }
    ;

check_trans_command returns [cmd::Command_ptr res]
    : 'check-trans'
      { $res.res = cm.make_check_trans(); }

      ( '-c' constraint=toplevel_expression
      { ((cmd::CheckTrans_ptr) $res)->add_constraint(constraint); })*
    ;

check_trans_command_topic returns [cmd::CommandTopic_ptr res]
    :  'check-trans'
        { $res.res = cm.topic_check_trans(); }
    ;

list_traces_command returns [cmd::Command_ptr res]
    : 'list-traces'
      { $res.res = cm.make_list_traces(); }
    ;

list_traces_command_topic returns [cmd::CommandTopic_ptr res]
    :  'list-traces'
        { $res.res = cm.topic_list_traces(); }
    ;

dump_traces_command returns [cmd::Command_ptr res]
    : 'dump-traces'
      { $res.res = cm.make_dump_traces(); }

    (
      '-a'
      { ((cmd::DumpTraces_ptr) $res)->set_all(true); }
    |
      '-f' format=pcchar_identifier
      { ((cmd::DumpTraces_ptr) $res)->set_format(format); }

    | '-o' output=pcchar_quoted_string
      {
            ((cmd::DumpTraces_ptr) $res)->set_output(output);
      }
    )*

    ( trace_id=pcchar_identifier
    { ((cmd::DumpTraces_ptr) $res)->add_trace_id(trace_id); } )*
    ;

dump_traces_command_topic returns [cmd::CommandTopic_ptr res]
    :  'dump-traces'
        { $res.res = cm.topic_dump_traces(); }
    ;


dup_trace_command returns [cmd::Command_ptr res]
    : 'dup-trace'
      { $res.res = cm.make_dup_trace(); }

      trace_id=pcchar_identifier
      { ((cmd::DupTrace_ptr) $res)->set_trace_id(trace_id); }

      ( duplicate_uid=pcchar_identifier
        { ((cmd::DupTrace_ptr) $res)->set_duplicate_id(duplicate_uid); } )?
    ;

dup_trace_command_topic returns [cmd::CommandTopic_ptr res]
    :  'dup-trace'
        { $res.res = cm.topic_dup_trace(); }
    ;

pick_state_command returns [cmd::Command_ptr res]
    :   'pick-state'
        { $res.res = cm.make_pick_state(); }
    (
         '-a'
         { ((cmd::PickState_ptr) $res)->set_allsat(true); }

    |    '-n'
        { ((cmd::PickState_ptr) $res)->set_count(true); }

    |    '-l' limit=constant
         { ((cmd::PickState_ptr) $res)->set_limit($limit.res->value()); }

    |    '-c' constraint=toplevel_expression
         { ((cmd::PickState_ptr) $res)->add_constraint(constraint); }
    )* ;

pick_state_command_topic returns [cmd::CommandTopic_ptr res]
    :  'pick-state'
        { $res.res = cm.topic_pick_state(); }
    ;

simulate_command returns [cmd::Command_ptr res]
    : 'simulate'
      { $res.res = cm.make_simulate(); }
    (
       '-i' invar_condition=toplevel_expression
        { ((cmd::Simulate_ptr) $res)->set_invar_condition(invar_condition); }

    |  '-u' until_condition=toplevel_expression
        { ((cmd::Simulate_ptr) $res)->set_until_condition(until_condition); }

    |   '-k' konst=constant
        { ((cmd::Simulate_ptr) $res)->set_k($konst.res->value()); }

    |   '-t' trace_id=pcchar_identifier
        { ((cmd::Simulate_ptr) $res)->set_trace_uid(trace_id); }
    )* ;

simulate_command_topic returns [cmd::CommandTopic_ptr res]
    :  'simulate'
        { $res.res = cm.topic_simulate(); }
    ;

get_command returns [cmd::Command_ptr res]
    : 'get'
      { $res.res = cm.make_get(); }

      ( id=identifier
      { ((cmd::Get_ptr) $res)->set_identifier(id); })?
    ;

get_command_topic returns [cmd::CommandTopic_ptr res]
    :  'get'
        { $res.res = cm.topic_get(); }
    ;

set_command returns [cmd::Command_ptr res]
    : 'set'
      { $res.res = cm.make_set(); }

      id=identifier
      { ((cmd::Set_ptr) $res)->set_identifier(id); }

      val=toplevel_expression
      { ((cmd::Set_ptr) $res)->set_value(val); }
    ;

set_command_topic returns [cmd::CommandTopic_ptr res]
    :  'set'
        { $res.res = cm.topic_set(); }
    ;

clear_command returns [cmd::Command_ptr res]
    : 'clear'
      { $res.res = cm.make_clear(); }

      ( id=identifier
      { ((cmd::Clear_ptr) $res)->set_identifier(id); })?
    ;

clear_command_topic returns [cmd::CommandTopic_ptr res]
    :  'clear'
        { $res.res = cm.topic_clear(); }
    ;

quit_command returns [cmd::Command_ptr res]
    :  'quit'
       { $res.res = cm.make_quit(); }
    ;

quit_command_topic returns [cmd::CommandTopic_ptr res]
    :  'quit'
        { $res.res = cm.topic_quit(); }
    ;

pcchar_identifier returns [pconst_char res]
@init {}
    : IDENTIFIER
      { $res.res = (pconst_char) $IDENTIFIER.text; }
    ;

pcchar_quoted_string returns [pconst_char res]
    : QUOTED_STRING
        {
            pANTLR3_UINT8 p = $QUOTED_STRING.text;
            pANTLR3_UINT8 q; for (q = p; *q; ++ q) ;

            assert (*p == '\'' || *p == '\"');
            p ++ ;  /* cut lhs quote */

            q -- ;
            assert (*q == '\'' || *q == '\"');
            *q = 0; /* cut rhs quote */

            $res.res = (pconst_char) p; // $QUOTED_STRING.text;
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
    : '"' .+ '"'
    | '\'' .+ '\''
    ;

fragment TYPE_WIDTH
    : DECIMAL_LITERAL
    ;

fragment ID_FIRST_CHAR
    :   'A'.*?'Z'
    |   'a'.*?'z'
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
   :  DECIMAL_DIGIT | 'a'.*?'f' | 'A'.*?'F'
   ;

fragment ZERO
   : '0'
   ;

WS
   : (' '|'\r'|'\t'|'\u000C'|'\n')
     { -> channel(HIDDEN) }
   ;

LINE_COMMENT
   : ( '//' | '--' ) ~('\n'|'\r')* '\r'? '\n'
     { -> channel(HIDDEN) }
   ;
