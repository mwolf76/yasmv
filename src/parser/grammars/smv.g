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

options {
    k = 2;
    memoize = true;
    language = C;
}

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

    /* global variables to replace scopes */
    model::Module_ptr current_module;

    /* declaration modifier flags */
    int hidden;
    int input;
    int frozen;
    int inertial;
    value_format_t format;
}

// --- Model Description Language  ---------------------------------------------
smv
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
    { om.set_word_width( width->value()); }
    ;

modules
    : module_def *
    ;

module_def
    : 'MODULE' module_id=identifier
      { smv_model.add_module(* (current_module = new model::Module(module_id))); }

      fsm_param_decl? module_body ';'
    ;

module_body
    :   module_decl ( ';' module_decl )*
    ;

module_decl
@init {
    hidden = 0;
    input = 0;
    frozen = 0;
    inertial = 0;

    format = FORMAT_DEFAULT;
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
              'hidden'   { hidden   = 1; }
            | 'frozen'   { frozen   = 1; }
            | 'inertial' { inertial = 1; }
            | 'input'    { input    = 1; }

            | 'bin' { format = FORMAT_BINARY;      }
            | 'oct' { format = FORMAT_OCTAL;       }
            | 'dec' { format = FORMAT_DECIMAL;     }
            | 'hex' { format = FORMAT_HEXADECIMAL; }
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
            assert(nullptr != tp);
            for (expr_iter = ev.begin(); expr_iter != ev.end(); ++ expr_iter) {
                expr::Expr_ptr vid (*expr_iter);
                symb::Variable_ptr var
                    (new symb::Variable(current_module->name(), vid, tp));

                if (hidden)
                    var->set_hidden(true);
                if (input)
                    var->set_input(true);
                if (inertial)
                    var->set_inertial(true);
                if (frozen)
                    var->set_frozen(true);

                if (format != FORMAT_DEFAULT)
                    var->set_format(format);

                current_module->add_var(vid, var);
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
            assert(nullptr != tp);
            for (expr_iter = ev.begin(); expr_iter != ev.end(); ++ expr_iter) {
                expr::Expr_ptr pid (*expr_iter);
                current_module->add_parameter(pid,
                                                    new symb::Parameter(current_module->name(),
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
          new symb::Define(current_module->name(), id, body);

      if (input)
          throw SyntaxError("#input modifier not supported in DEFINE decls");

      if (frozen)
          throw SyntaxError("#frozen modifier not supported in DEFINE decls");

      if (inertial)
          throw SyntaxError("#inertial modifier not supported in DEFINE decls");

      if (hidden)
          def->set_hidden(true);

      /* these are mutually exclusive, default is hexadecimal */
      if (format != FORMAT_DEFAULT)
          def->set_format(format);

      current_module->add_def(id, def);
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
      { current_module->add_init(expr); }
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
      { current_module->add_invar(expr); }
    ;

fsm_trans_decl
    : 'TRANS' fsm_trans_decl_body
    ;

fsm_trans_decl_body
    : fsm_trans_decl_clause
        (';' fsm_trans_decl_clause)*
    ;

fsm_trans_decl_clause
    : (toplevel_expression '?:' fsm_trans_decl_clause_assignments) =>
        lhs=toplevel_expression '?:' rhs=fsm_trans_decl_clause_assignments
      { current_module->add_trans(em.make_guard(lhs, rhs)); }

    | rhs=fsm_trans_decl_clause_assignments
      { current_module->add_trans(em.make_guard(em.make_true(), rhs)); }
    ;

fsm_trans_decl_clause_assignments returns [expr::Expr_ptr res]
@init {
    $res = nullptr;
    expr::ExprVector clauses;
}
    : c=toplevel_expression{ clauses.push_back(c); }
      (  ','  c=toplevel_expression { clauses.push_back(c); })*

    {
      expr::ExprVector::reverse_iterator i { clauses.rbegin() };
      while (clauses.rend() != i) {
          $res = ($res != nullptr) ? em.make_and( *i, $res) : *i;
          ++ i;
      }
    }
    ;

toplevel_expression returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : expr=timed_expression
      { $res = expr; }
    ;

timed_expression returns [expr::Expr_ptr res]
@init {
    $res = nullptr;
    expr::Expr_ptr a { nullptr };
    expr::Expr_ptr b { nullptr };
}
    : '@' time=forward_instant { a = time; } ('..' time=forward_instant { b = time; })? '{' body=propositional_expression '}'
      { $res = (nullptr != b) ? em.make_at( em.make_interval(a, b),  body) : em.make_at(a, body); }

    | '$' time=backward_instant { a = time; } ('..' time=backward_instant { b = time; })? '{' body=propositional_expression '}'
      { $res = (nullptr != b) ? em.make_at( em.make_interval(a, b),  body) : em.make_at(a, body); }

    | body=propositional_expression
      { $res = body; }
    ;

temporal_expression returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : expr=propositional_expression
      { $res = expr; }
    ;

propositional_expression returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : expr=ite_expression {
         $res = expr;
      }
    ;

ite_expression returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : expr=logical_expression {
         $res = expr;
      }

      (
            '?' lhs=logical_expression ':' rhs=logical_expression
            { $res = em.make_ite( em.make_cond($res, lhs), rhs); }
      )?
    ;

logical_expression returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : expr=logical_implies_expression
      { $res = expr; }
    ;

logical_implies_expression returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : lhs=logical_or_expression
      { $res = lhs; }

    (
      '->' rhs=logical_or_expression
      { $res = em.make_implies($res, rhs); }
    )* ;

logical_or_expression returns[expr::Expr_ptr res]
@init { $res = nullptr; }
    : lhs=logical_and_expression
      { $res = lhs; }

    (
      '||' rhs=logical_and_expression
      { $res = em.make_or($res, rhs); }
    )* ;

logical_and_expression returns[expr::Expr_ptr res]
@init { $res = nullptr; }
    : lhs=equality_expression
      { $res = lhs; }

    (
      '&&' rhs=equality_expression
      { $res = em.make_and($res, rhs); }
    )* ;

equality_expression returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : lhs=relational_expression
      { $res = lhs; }

      ( '=' rhs=relational_expression
            { $res = em.make_eq($res, rhs); }

      | '!=' rhs=relational_expression
            { $res = em.make_ne($res, rhs); }

      | ':=' rhs=relational_expression
            { $res = em.make_assignment($res, rhs); }

      )? /* predicates are binary */;

relational_expression returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : lhs=algebraic_expression
      { $res = lhs; }

      ( '<' rhs=algebraic_expression
            { $res = em.make_lt($res, rhs); }

      | '<=' rhs=algebraic_expression
            { $res = em.make_le($res, rhs); }

      | '>=' rhs=algebraic_expression
            { $res = em.make_ge($res, rhs); }

      | '>' rhs=algebraic_expression
            { $res = em.make_gt($res, rhs); }
      )? /* predicates are binary */ ;

algebraic_expression returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    :
        expr=bw_or_expression
        { $res = expr; }
    ;

bw_or_expression returns[expr::Expr_ptr res]
@init { $res = nullptr; }
    : lhs=bw_xor_expression
      { $res = lhs; }

    (
      '|' rhs=bw_xor_expression
       { $res = em.make_bw_or($res, rhs); }
    )* ;

bw_xor_expression returns[expr::Expr_ptr res]
@init { $res = nullptr; }
    : lhs=bw_xnor_expression
      { $res = lhs; }

    (
      '^' rhs=bw_xnor_expression
      { $res = em.make_bw_xor($res, rhs); }
    )* ;

bw_xnor_expression returns[expr::Expr_ptr res]
@init { $res = nullptr; }
    : lhs=bw_and_expression
      { $res = lhs; }

    (
      '<->' rhs=bw_and_expression
      { $res = em.make_bw_xnor($res, rhs); }
    )* ;

bw_and_expression returns[expr::Expr_ptr res]
@init { $res = nullptr; }
    : lhs=shift_expression
      { $res = lhs; }

    (
      '&' rhs=shift_expression
      { $res = em.make_bw_and($res, rhs); }
    )* ;

shift_expression returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : lhs=additive_expression
      { $res = lhs; }

    (
      '<<' rhs=additive_expression
      { $res = em.make_lshift($res, rhs); }

    | '>>' rhs=additive_expression
       { $res = em.make_rshift($res, rhs); }
    )* ;

additive_expression returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : lhs=multiplicative_expression
      { $res = lhs; }

    (
        '+' rhs=multiplicative_expression
        { $res = em.make_add($res, rhs); }

    |   '-' rhs=multiplicative_expression
        { $res = em.make_sub($res, rhs); }
    )* ;

multiplicative_expression returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : lhs=cast_expression
      { $res = lhs; }

    (
      '*' rhs=cast_expression
      { $res = em.make_mul($res, rhs); }

    | '/' rhs=cast_expression
      { $res = em.make_div($res, rhs); }

    | '%' rhs=cast_expression
      { $res = em.make_mod($res, rhs); }
    )* ;

cast_expression returns [expr::Expr_ptr res]
@init {
    $res = nullptr;
    expr::Expr_ptr cast = nullptr;
}
    : '(' tp = native_type ')' expr = cast_expression
        { $res = em.make_cast( tp->repr(), expr ); }
    |
        expr = unary_expression
        { $res = expr; }
    ;

unary_expression returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : expr=postfix_expression
      { $res = expr; }

    | expr=nondeterministic_expression
      { $res = expr; }

    | expr=array_expression
      { $res = expr; }

    | 'next' '(' expr=toplevel_expression ')'
      { $res = em.make_next(expr); }

    | '!' expr=postfix_expression
      { $res = em.make_not(expr); }

    | '~' expr=postfix_expression
      { $res = em.make_bw_not(expr); }

    | '-' expr=postfix_expression
      { $res = em.make_neg(expr); }
    ;

nondeterministic_expression returns[expr::Expr_ptr res]
@init {
    $res = nullptr;
    bool is_range { false };
    expr::ExprVector clauses;
}
    : '{'
          c=toplevel_expression{ clauses.push_back(c); }
        (  ','  c=toplevel_expression { clauses.push_back(c); }
        | '..' c=toplevel_expression  { assert(!is_range); is_range = true; clauses.push_back(c); } )+
      '}'
      {
            if (!is_range) {
                expr::ExprVector::reverse_iterator i { clauses.rbegin() };
                while (clauses.rend() != i) {
                    $res = $res ? em.make_set_comma( *i, $res) : *i;
                    ++ i;
                }
            } else {
               expr::ExprVector::iterator lhs { clauses.begin() };
               expr::Expr_ptr lhs_expr { *lhs };
               assert (em.is_constant(lhs_expr));
               value_t start { lhs_expr->value() };

               expr::ExprVector::reverse_iterator rhs { clauses.rbegin() };
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
@init {
    $res = nullptr;
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
                $res = $res ? em.make_array_comma( *i, $res) : *i;
                ++ i;
            }

            $res = em.make_array( $res );
        }
    ;


params returns [expr::Expr_ptr res]
@init {
    $res = nullptr;
    expr::ExprVector actuals;
    res = nullptr;
}
    : ( expressions[&actuals]
    {
            expr::ExprVector::reverse_iterator expr_iter;
            res = nullptr;

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
@init { $res = nullptr; }
    :   lhs=basic_expression
        { $res = lhs; }

    (
        '[' rhs=toplevel_expression ']'
        { $res = em.make_subscript($res, rhs); }
    |
        '(' rhs=params ')'
        { $res = em.make_params($res, rhs); }

    |   '.' rhs=identifier
        { $res = em.make_dot($res, rhs); }
    )* ;

basic_expression returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : id=identifier
      { $res = id; }

    | k=constant
      { $res = k; }

    | '(' expr=toplevel_expression ')'
      { $res = expr; }

    | expr=case_expression
      { $res = expr; }
    ;

case_expression returns [expr::Expr_ptr res]
@init {
    $res = nullptr;
    typedef std::pair<expr::Expr_ptr, expr::Expr_ptr> CaseClause;
    typedef std::vector<CaseClause> CaseClauses;

    CaseClauses clauses;
}  : 'case'

     (lhs=toplevel_expression ':' rhs=toplevel_expression ';'
     { clauses.push_back( std::pair< expr::Expr_ptr, expr::Expr_ptr > (lhs, rhs)); }) +

     'else' ':' last=toplevel_expression ';'
     { clauses.push_back( std::pair< expr::Expr_ptr, expr::Expr_ptr > (nullptr, last)); }

     'end'
     {
        CaseClauses::reverse_iterator i = clauses.rbegin();
        res = i->second;
        while (1) {
            if ( ++ i == clauses.rend())
                break;
            $res = em.make_ite( em.make_cond(i->first,
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
@init { $res = nullptr; }
    : IDENTIFIER
      { $res = em.make_identifier((const char*)($IDENTIFIER.text->chars)); }
    ;

forward_instant returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : DECIMAL_LITERAL {
        expr::Atom tmp((const char*)($DECIMAL_LITERAL.text->chars));
        $res = em.make_instant(strtoll(tmp.c_str(), nullptr, 10));
      }
    ;

backward_instant returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : DECIMAL_LITERAL {
        expr::Atom tmp((const char*)($DECIMAL_LITERAL.text->chars));
        $res = em.make_instant(UINT_MAX - strtoll(tmp.c_str(), nullptr, 10));
      }
    ;

constant returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : HEX_LITERAL {
        expr::Atom tmp((const char*)($HEX_LITERAL.text->chars));
        $res = em.make_hex_const(tmp);
      }

    | BINARY_LITERAL {
        expr::Atom tmp((const char*)($BINARY_LITERAL.text->chars));
        $res = em.make_bin_const(tmp);
      }

    | OCTAL_LITERAL {
        expr::Atom tmp((const char*)($OCTAL_LITERAL.text->chars));
        $res = em.make_oct_const(tmp);
      }

    | DECIMAL_LITERAL {
        expr::Atom tmp((const char*)($DECIMAL_LITERAL.text->chars));
        $res = em.make_dec_const(tmp);
      }

    | QUOTED_STRING {
            pANTLR3_UINT8 p = $QUOTED_STRING.text->chars;
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
@init { $res = nullptr; }
    : 'next' '(' expr=postfix_expression ')'
      { $res = em.make_next(expr); }

    | expr=postfix_expression
      { $res = expr; }
    ;

/* ordinary values used elsewhere */
value returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    : expr=postfix_expression
      { $res = expr; }
    ;

/* typedecls */
smv_type returns [type::Type_ptr res]
@init { $res = nullptr; }
    : tp = native_type
      { $res = tp; }

    | tp = enum_type
      { $res = tp; }

    | tp = instance_type
      { $res = tp; }
    ;

native_type returns [type::Type_ptr res]
@init { $res = nullptr; }
    : tp = boolean_type
      { $res = tp; }

    | tp = unsigned_int_type
      { $res = tp; }

    | tp = signed_int_type
      { $res = tp; }
    ;

boolean_type returns [type::Type_ptr res]
@init {
    $res = nullptr;
    int array_size = 0;
}
    : 'boolean' (

            '[' size=constant ']'
            {
                array_size = size->value();
                assert(0 < array_size);
            }
    ) ?
    {
        $res = array_size ?
            (type::Type_ptr) tm.find_boolean_array(array_size) :
            (type::Type_ptr) tm.find_boolean();
    }
    ;

enum_type returns [type::Type_ptr res]
@init {
    $res = nullptr;
    int array_size = 0;
    expr::ExprSet lits;
}
    : '{'
          lit=literal { lits.insert(lit); }
              (',' lit=literal { lits.insert(lit); })*
      '}' (
            '[' size=constant ']'
            {
                array_size = size->value();
                assert(0 < array_size);
            }
    ) ?
    {
        $res = array_size ?
            (type::Type_ptr) tm.find_enum_array(lits, array_size) :
            (type::Type_ptr) tm.find_enum(lits);
    }
    ;

unsigned_int_type returns [type::Type_ptr res]
@init {
    $res = nullptr;
    char *p = nullptr;
    int array_size = 0;
}
    :
        UNSIGNED_INT_TYPE
        {
            p = (char *) $UNSIGNED_INT_TYPE.text->chars;
            while (*p && !isdigit(*p))
                ++ p;
        }
        (
            '[' size=constant ']'
            {
                array_size = size->value();
                assert(0 < array_size);
            }
    ) ?
    {
        $res = array_size ?
            (type::Type_ptr) tm.find_unsigned_array(*p ? atoi(p)
                : om.word_width(), array_size) :
            (type::Type_ptr) tm.find_unsigned( *p ? atoi(p)
                : om.word_width());
    }
    ;

signed_int_type returns [type::Type_ptr res]
@init {
    $res = nullptr;
    char *p = nullptr;
    int array_size = 0;
}
    :
        SIGNED_INT_TYPE
        {
            p = (char *) $SIGNED_INT_TYPE.text->chars;
            while (*p && !isdigit(*p))
                ++ p;
        }
        (
            '[' size=constant ']'
            {
                array_size = size->value();
                assert(0 < array_size);
            }
        )?
    {
        $res = array_size ?
            (type::Type_ptr) tm.find_signed_array(*p ? atoi(p)
                : om.word_width(), array_size) :
            (type::Type_ptr) tm.find_signed( *p ? atoi(p)
                : om.word_width());
    }
    ;


instance_type returns [type::Type_ptr res]
@init { $res = nullptr; }
    : module=identifier '(' parameters=params ')'
      { $res = tm.find_instance( module, parameters ); }
    ;

literal returns [expr::Expr_ptr res]
@init { $res = nullptr; }
    :  expr=identifier
       { $res = expr; }
    ;

// -- Scripting sub-system Toplevel ---------------------------------------------
command_line returns [cmd::CommandVector_ptr res]
@init {
    $res = nullptr;
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
@init { $res = nullptr; }
    :  c=check_init_command_topic
       { $res = c; }

    |  c=check_trans_command_topic
       { $res = c; }

    |  c=diameter_command_topic
       { $res = c; }

    |  c=clear_command_topic
       { $res = c; }

    |  c=do_command_topic
       { $res = c; }

    |  c=dump_model_command_topic
        { $res = c; }

    |  c=dump_trace_command_topic
        { $res = c; }

    |  c=dup_trace_command_topic
        { $res = c; }

    |  c=echo_command_topic
       { $res = c; }

    |  c=get_command_topic
       { $res = c; }

    |  c=help_command_topic
       { $res = c; }

    |  c=last_command_topic
       { $res = c; }

    |  c=list_traces_command_topic
       { $res = c; }

    |  c=on_command_topic
       {$res = c; }

    |  c=read_model_command_topic
       { $res = c; }

    |  c=read_trace_command_topic
       { $res = c; }

    |  c=pick_state_command_topic
       { $res = c; }

    |  c=quit_command_topic
       { $res = c; }

    |  c=reach_command_topic
       { $res = c; }

    | c=select_trace_topic
      { $res = c; }

    |  c=set_command_topic
       { $res = c; }

    |  c=simulate_command_topic
       { $res = c; }

    |  c=time_command_topic
       { $res = c; }
    ;

command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    :  c=check_init_command
       { $res = c; }

    |  c=check_trans_command
       { $res = c; }

    |  c=clear_command
       { $res = c; }

    |  c=diameter_command
        { $res = c; }

    |  c=do_command
       { $res = c; }

    |  c=dump_model_command
        { $res = c; }

    |  c=dump_trace_command
        { $res = c; }

    |  c=dup_trace_command
        { $res = c; }

    |  c=echo_command
       { $res = c; }

    |  c=get_command
       { $res = c; }

    |  c=help_command
       { $res = c; }

    |  c=last_command
       { $res = c; }

    |  c=list_traces_command
       { $res = c; }

    |  c=on_command
       {$res = c; }

    |  c=read_model_command
       { $res = c; }

    |  c=read_trace_command
       { $res = c; }

    |  c=pick_state_command
       { $res = c; }

    |  c=quit_command
       { $res = c; }

    |  c=reach_command
       { $res = c; }

    |  c=select_trace_command
       { $res = c; }

    |  c=set_command
       { $res = c; }

    |  c=simulate_command
       { $res = c; }

    |  c=time_command
       { $res = c; }
    ;

help_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    : 'help'
      { $res = cm.make_help(); }
      (
          topic = command_topic
          { ((cmd::Help_ptr) $res)->set_topic(topic); }
      )? ;

help_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    : 'help'
      { $res = cm.topic_help(); }
    ;

do_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    : 'do'
      { $res = cm.make_do(); }
      (
            subcommand = command ';'
            { ((cmd::Do_ptr) res)->add_command(subcommand); }
      )+ ;

do_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    : 'do'
       { $res = cm.topic_do(); }
    ;

echo_command returns [cmd::Command_ptr res]
@init {
    $res = nullptr;
    expr::ExprVector ev;
}
    : 'echo'?
      { $res = cm.make_echo(); }
      (
            expr = toplevel_expression
            {
                ((cmd::Echo_ptr) $res) -> append_expression(expr);
            }
      )
      ;

echo_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    : 'echo'
       { $res = cm.topic_echo(); }
    ;

last_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    : 'last'
      { $res = cm.make_last(); }
    ;

last_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    : 'last'
       { $res = cm.topic_last(); }
    ;

on_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    :
      'on'
        ('success' { $res = cm.make_on(); }
            tc=command { ((cmd::On_ptr) $res)->set_then(tc); } |

          'failure' { $res = cm.make_on(); }
            ec=command { ((cmd::On_ptr) $res)->set_else(ec); } )
    ;

on_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    : 'on'
        { $res = cm.topic_on(); }
    ;

time_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    : 'time'
      { $res = cm.make_time(); }
    ;

time_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    : 'time'
      { $res = cm.topic_time(); }
    ;

read_model_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    :  'read-model'
        { $res = cm.make_read_model(); }

        ( input=pcchar_quoted_string {
            ((cmd::ReadModel_ptr) $res)->set_input(input);
        }) ?
    ;

read_model_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    :  'read-model'
        { $res = cm.topic_read_model(); }
    ;

read_trace_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    :  'read-trace'
        { $res = cm.make_read_trace(); }

        ( input=pcchar_quoted_string {
            ((cmd::ReadTrace_ptr) $res)->set_input(input);
        }) ?
    ;

read_trace_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    :  'read-trace'
        { $res = cm.topic_read_trace(); }
    ;

dump_model_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    :  'dump-model'
        { $res = cm.make_dump_model(); }

        ( '-o' output=pcchar_quoted_string {
            ((cmd::DumpModel_ptr) $res)->set_output(output);
        }

        | '-s' ('state' { ((cmd::DumpModel_ptr) $res)->select_state(); }
        |       'init'  { ((cmd::DumpModel_ptr) $res)->select_init();  }
        |       'trans' { ((cmd::DumpModel_ptr) $res)->select_trans(); })
        ) *
    ;

dump_model_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    :  'dump-model'
        { $res = cm.topic_dump_model(); }
    ;


check_init_command returns[cmd::Command_ptr res]
@init { $res = nullptr; }
    : 'check-init'
      { $res = cm.make_check_init(); }

      ( '-c' constraint=toplevel_expression
      { ((cmd::CheckInit_ptr) $res)->add_constraint(constraint); })*
    ;

check_init_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    :  'check-init'
        { $res = cm.topic_check_init(); }
    ;

diameter_command returns[cmd::Command_ptr res]
@init { $res = nullptr; }
    : 'diameter'
      { $res = cm.make_diameter(); }
    ;

diameter_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    :  'diameter'
        { $res = cm.topic_diameter(); }
    ;

reach_command returns[cmd::Command_ptr res]
@init { $res = nullptr; }
    :   'reach'
        { $res = cm.make_reach(); }

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
@init { $res = nullptr; }
    :  'reach'
        { $res = cm.topic_reach(); }
    ;

select_trace_command returns[cmd::Command_ptr res]
@init { $res = nullptr; }
    :   'select-trace'
        { $res = cm.make_select_trace(); }

        trace_id=pcchar_identifier
        { ((cmd::SelectTrace_ptr) $res)->set_trace_id(trace_id); }
    ;

select_trace_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    :  'select-trace'
       { $res = cm.topic_select_trace(); }
    ;

check_trans_command returns[cmd::Command_ptr res]
@init { $res = nullptr; }
    : 'check-trans'
      { $res = cm.make_check_trans(); }

      ( '-l' limit=constant
      { ((cmd::CheckTrans_ptr) $res)->set_limit(limit->value()); })*

      ( '-c' constraint=toplevel_expression
      { ((cmd::CheckTrans_ptr) $res)->add_constraint(constraint); })*
    ;

check_trans_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    :  'check-trans'
        { $res = cm.topic_check_trans(); }
    ;

list_traces_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    : 'list-traces'
      { $res = cm.make_list_traces(); }
    ;

list_traces_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    :  'list-traces'
        { $res = cm.topic_list_traces(); }
    ;

dump_trace_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    : 'dump-trace'
      { $res = cm.make_dump_trace(); }

    (
      '-a'
      { ((cmd::DumpTrace_ptr) $res)->set_all(true); }
    |
      '-f' format=pcchar_identifier
      { ((cmd::DumpTrace_ptr) $res)->set_format(format); }

    | '-o' output=pcchar_quoted_string
      {
            ((cmd::DumpTrace_ptr) $res)->set_output(output);
      }
    )*

    ( trace_id=pcchar_identifier
    { ((cmd::DumpTrace_ptr) $res)->add_trace_id(trace_id); } )*
    ;

dump_trace_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    :  'dump-trace'
        { $res = cm.topic_dump_trace(); }
    ;


dup_trace_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    : 'dup-trace'
      { $res = cm.make_dup_trace(); }

      trace_id=pcchar_identifier
      { ((cmd::DupTrace_ptr) $res)->set_trace_id(trace_id); }

      ( duplicate_uid=pcchar_identifier
        { ((cmd::DupTrace_ptr) $res)->set_duplicate_id(duplicate_uid); } )?
    ;

dup_trace_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    :  'dup-trace'
        { $res = cm.topic_dup_trace(); }
    ;

pick_state_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    :   'pick-state'
        { $res = cm.make_pick_state(); }
    (
         '-a'
         { ((cmd::PickState_ptr) $res)->set_allsat(true); }

    |    '-n'
        { ((cmd::PickState_ptr) $res)->set_count(true); }

    |    '-l' limit=constant
         { ((cmd::PickState_ptr) $res)->set_limit(limit->value()); }

    |    '-c' constraint=toplevel_expression
         { ((cmd::PickState_ptr) $res)->add_constraint(constraint); }
    )* ;

pick_state_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    :  'pick-state'
        { $res = cm.topic_pick_state(); }
    ;

simulate_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    : 'simulate'
      { $res = cm.make_simulate(); }
    (
       '-c' constraint=toplevel_expression
        { ((cmd::Simulate_ptr) $res)->add_constraint(constraint); }

    |  '-u' until_condition=toplevel_expression
        { ((cmd::Simulate_ptr) $res)->set_until_condition(until_condition); }

    |   '-k' konst=constant
        { ((cmd::Simulate_ptr) $res)->set_k(konst->value()); }

    |   '-t' trace_id=pcchar_identifier
        { ((cmd::Simulate_ptr) $res)->set_trace_uid(trace_id); }
    )* ;

simulate_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    :  'simulate'
        { $res = cm.topic_simulate(); }
    ;

get_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    : 'get'
      { $res = cm.make_get(); }

      ( id=identifier
      { ((cmd::Get_ptr) $res)->set_identifier(id); })?
    ;

get_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    :  'get'
        { $res = cm.topic_get(); }
    ;

set_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    : 'set'
      { $res = cm.make_set(); }

      id=identifier
      { ((cmd::Set_ptr) $res)->set_identifier(id); }

      val=toplevel_expression
      { ((cmd::Set_ptr) $res)->set_value(val); }
    ;

set_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    :  'set'
        { $res = cm.topic_set(); }
    ;

clear_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    : 'clear'
      { $res = cm.make_clear(); }

      ( id=identifier
      { ((cmd::Clear_ptr) $res)->set_identifier(id); })?
    ;

clear_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    :  'clear'
        { $res = cm.topic_clear(); }
    ;

quit_command returns [cmd::Command_ptr res]
@init { $res = nullptr; }
    :  'quit'
       { $res = cm.make_quit(); }
    ;

quit_command_topic returns [cmd::CommandTopic_ptr res]
@init { $res = nullptr; }
    :  'quit'
        { $res = cm.topic_quit(); }
    ;

pcchar_identifier returns [pconst_char res]
@init { $res = nullptr; }
    : IDENTIFIER
      { $res = (pconst_char) $IDENTIFIER.text->chars; }
    ;

pcchar_quoted_string returns [pconst_char res]
@init { $res = nullptr; }
    : QUOTED_STRING
        {
            pANTLR3_UINT8 p = $QUOTED_STRING.text->chars;
            pANTLR3_UINT8 q; for (q = p; *q; ++ q) ;

            assert (*p == '\'' || *p == '\"');
            p ++ ;  /* cut lhs quote */

            q -- ;
            assert (*q == '\'' || *q == '\"');
            *q = 0; /* cut rhs quote */

            $res = (pconst_char) p; // $QUOTED_STRING.text->chars;
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
   : (' '|'\r'|'\t'|'\u000C'|'\n')
     { $channel=HIDDEN; }
   ;

LINE_COMMENT
   : ( '//' | '--' ) ~('\n'|'\r')* '\r'? '\n'
     { $channel=HIDDEN; }
   ;

