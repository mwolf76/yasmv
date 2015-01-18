/**
   Copyright (C) 2010-2012 Marco Pensallorto

   This file is part of GNuSMV.

   GNuSMV is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   GNuSMV is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with GNuSMV.  If not, see <http://www.gnu.org/licenses/>.
*/
grammar smv;

options {
    k = 2;
    memoize = true;
    language = C;
}

@header {
#include <common.hh>

/* cmd subsystem */
#include <cmd/cmd.hh>

#include <expr/expr.hh>
#include <expr/expr_mgr.hh>

#include <type/type.hh>
#include <type/type_mgr.hh>

#include <model/model.hh>
#include <model/model_mgr.hh>
}

@members {

    /* singleton managers */
    ExprMgr& em (ExprMgr::INSTANCE());
    ModelMgr& mm (ModelMgr::INSTANCE());
    TypeMgr& tm (TypeMgr::INSTANCE());
    OptsMgr& om  (OptsMgr::INSTANCE());
    CommandMgr& cm (CommandMgr::INSTANCE());

    /* the model instance */
    Model& model (mm.model());
}

// --- Model Description Language  ---------------------------------------------
smv
scope {
    Module_ptr current_module;
}
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
    { om.set_word_width( width -> value()); }
    ;

modules
    : module_def *
    ;

module_def
    : 'MODULE' module_id=identifier
      { model.add_module(* ($smv::current_module = new Module(module_id))); }

      fsm_param_decl? module_body ';'
    ;

module_body
    :	module_decl ( ';' module_decl )*
    ;

module_decl
    :	/* variables and defines */
        fsm_var_decl
    |   fsm_ivar_decl
	|	fsm_define_decl

		/* FSM definition */
	|	fsm_init_decl
    |   fsm_invar_decl
	|	fsm_trans_decl
    ;

fsm_ivar_decl
    : 'IVAR'  fsm_ivar_decl_body
    ;

fsm_var_decl
    : 'VAR'  fsm_var_decl_body
    ;

fsm_param_decl
    : '(' fsm_param_decl_body ')'
    ;

fsm_var_decl_body
	: fsm_var_decl_clause
        ( ';' fsm_var_decl_clause)*
	;

fsm_ivar_decl_body
	: fsm_ivar_decl_clause
        ( ';' fsm_ivar_decl_clause)*
	;

fsm_param_decl_body
	: fsm_param_decl_clause
        ( ',' fsm_param_decl_clause)*
	;

fsm_var_decl_clause
@init {
    ExprVector ev;
}
	: ids=identifiers[&ev] ':' tp=type
    {
            ExprVector::iterator expr_iter;
            assert(NULL != tp);
            for (expr_iter = ev.begin(); expr_iter != ev.end(); ++ expr_iter) {
                Expr_ptr vid (*expr_iter);
                $smv::current_module->add_var(vid,
                                              new Variable($smv::current_module->name(), vid, tp));
            }
    }
	;

fsm_param_decl_clause
@init {
    ExprVector ev;
}
	: ids=identifiers[&ev] ':' tp=type
    {
            ExprVector::iterator expr_iter;
            assert(NULL != tp);
            for (expr_iter = ev.begin(); expr_iter != ev.end(); ++ expr_iter) {
                Expr_ptr pid (*expr_iter);
                $smv::current_module->add_parameter(pid,
                                                    new Parameter($smv::current_module->name(), pid, tp));
            }
    }
	;


fsm_ivar_decl_clause
@init {
    ExprVector ev;
}
	: ids=identifiers[&ev] ':' tp=type
    {
            ExprVector::iterator expr_iter;
            assert(NULL != tp);
            for (expr_iter = ev.begin(); expr_iter != ev.end(); ++ expr_iter) {
                Expr_ptr id = (*expr_iter);
                Variable_ptr ivar = new Variable($smv::current_module->name(), id, tp, true);
                $smv::current_module->add_var(id, ivar);
            }
    }
	;

fsm_define_decl
    : 'DEFINE' fsm_define_decl_body
    ;

fsm_define_decl_body
	: fsm_define_decl_clause
        ( ';' fsm_define_decl_clause)*
	;

fsm_define_decl_clause
@init {
    ExprVector formals;
}
	: id=identifier ( '(' identifiers[&formals] ')' )? ':=' body=toplevel_expression
    {
      Define_ptr def = new Define($smv::current_module->name(), id, formals, body);
      $smv::current_module->add_def(id, def);
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
      { $smv::current_module->add_init(expr); }
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
      { $smv::current_module->add_invar(expr); }
	;

fsm_trans_decl
    : 'TRANS' fsm_trans_decl_body
    ;

fsm_trans_decl_body
	: fsm_trans_decl_clause
        (';' fsm_trans_decl_clause)*
	;

fsm_trans_decl_clause
	: expr=toplevel_expression
      { $smv::current_module->add_trans(expr); }
	;

// entry point
toplevel_expression returns [Expr_ptr res]
    : expr=conditional_expression
      { $res = expr; }
    ;

conditional_expression returns [Expr_ptr res]
@init { }
	: expr=logical_or_expression {
         $res = expr;
      } (
            '?' lhs=toplevel_expression ':' rhs=toplevel_expression
            { $res = em.make_ite(em.make_cond($res, lhs), rhs); }
      )?
	;

logical_or_expression returns[Expr_ptr res]
@init { }
    : lhs=logical_and_expression
      { $res = lhs; }

    (
      'or' rhs=logical_and_expression
      { $res = em.make_or($res, rhs); }
    )*
    ;

logical_and_expression returns[Expr_ptr res]
@init { }
    : lhs=inclusive_or_expression
      { $res = lhs; }

    (
      'and' rhs=inclusive_or_expression
      { $res = em.make_and($res, rhs); }
    )*
    ;

inclusive_or_expression returns[Expr_ptr res]
@init { }
    : lhs=exclusive_or_expression
      { $res = lhs; }

    (
      '|' rhs=exclusive_or_expression
      { $res = em.make_bw_or($res, rhs); }
    )*
    ;

exclusive_or_expression returns[Expr_ptr res]
@init { }
    : lhs=equivalence_expression
      { $res = lhs; }

    (
      '^' rhs=equivalence_expression
      { $res = em.make_bw_xor($res, rhs); }
    )*
    ;

equivalence_expression returns[Expr_ptr res]
@init { }
    : lhs=and_expression
      { $res = lhs; }

    (
      '~' rhs=and_expression
      { $res = em.make_bw_xnor($res, rhs); }
    )*
    ;

and_expression returns[Expr_ptr res]
@init { }
    : lhs=iff_expression
      { $res = lhs; }

    (
      '&' rhs=iff_expression
      { $res = em.make_bw_and($res, rhs); }
    )*
    ;

iff_expression returns [Expr_ptr res]
@init { }
	:  lhs=implies_expression
       { $res = lhs; }

    (
       '<->' rhs=implies_expression
       { $res = em.make_iff($res, rhs); }
    )*
	;

implies_expression returns [Expr_ptr res]
@init { }
	: lhs=temporal_formula
      { $res = lhs; }

    (
      '->' rhs=temporal_formula
      { $res = em.make_implies($res, rhs); }
    )*
    ;

temporal_formula returns [Expr_ptr res]
@init { }
    :
        formula=binary_ltl_formula
        { $res = formula; }
    ;

binary_ltl_formula returns [Expr_ptr res]
@init { }
    : lhs=unary_ltl_formula
      { $res = lhs; } (
            'U' rhs=unary_ltl_formula
            { $res = em.make_U($res, rhs); }

        |   'R' rhs=unary_ltl_formula
            { $res = em.make_R($res, rhs); }
    )*
    ;

unary_ltl_formula returns [Expr_ptr res]
@init { }
    : 'G' formula=unary_ltl_formula
      { $res = em.make_G(formula); }

    | 'F' formula=unary_ltl_formula
      { $res = em.make_F(formula); }

    | 'X' formula=unary_ltl_formula
      { $res = em.make_X(formula); }

    | formula=equality_expression
      { $res = formula; }
    ;

equality_expression returns [Expr_ptr res]
@init { }
	: lhs=relational_expression
      { $res = lhs; }

    ( '=' rhs=relational_expression
     { $res = em.make_eq($res, rhs); }

    | '!=' rhs=relational_expression
     { $res = em.make_ne($res, rhs); }
    )*
	;

relational_expression returns [Expr_ptr res]
@init { }
	: lhs=shift_expression
      { $res = lhs; }

    (
      '<' rhs=shift_expression
      { $res = em.make_lt($res, rhs); }

    | '<=' rhs=shift_expression
      { $res = em.make_le($res, rhs); }

    | '>=' rhs=shift_expression
      { $res = em.make_ge($res, rhs); }

    | '>' rhs=shift_expression
      { $res = em.make_gt($res, rhs); }
    )*
	;

shift_expression returns [Expr_ptr res]
@init { }
	: lhs=additive_expression
      { $res = lhs; }

    (
      '<<' rhs=additive_expression
      { $res = em.make_lshift($res, rhs); }

    | '>>' rhs=additive_expression
       { $res = em.make_rshift($res, rhs); }
    )*
	;

additive_expression returns [Expr_ptr res]
@init { }
	: lhs=multiplicative_expression
      { $res = lhs; }

    (
        '+' rhs=multiplicative_expression
        { $res = em.make_add($res, rhs); }

    |   '-' rhs=multiplicative_expression
        { $res = em.make_sub($res, rhs); }
    )*
	;

multiplicative_expression returns [Expr_ptr res]
@init { }
	: lhs=cast_expression
      { $res = lhs; }
    (
      '*' rhs=cast_expression
      { $res = em.make_mul($res, rhs); }

    | '/' rhs=cast_expression
      { $res = em.make_div($res, rhs); }

    | '%' rhs=cast_expression
      { $res = em.make_mod($res, rhs); }
    )*
	;

cast_expression returns [Expr_ptr res]
@init {
    Expr_ptr cast = NULL;
}
    : '(' tp = native_type ')' expr = cast_expression
        { $res = em.make_cast( tp -> repr(), expr ); }
	|
        expr = unary_expression
        { $res = expr; }
	;

unary_expression returns [Expr_ptr res]
@init { }
	: expr=postfix_expression
      { $res = expr; }

	| 'next' '(' expr=toplevel_expression ')'
      { $res = em.make_next(expr); }

	| 'not' expr=postfix_expression
      { $res = em.make_not(expr); }

    | '!' expr=postfix_expression
      { $res = em.make_bw_not(expr); }

    | '-' expr=postfix_expression
      { $res = em.make_neg(expr); }
	;

params returns [Expr_ptr res]
@init {
    ExprVector actuals;
    res = NULL;
}
	: ( expressions[&actuals]
    {
            ExprVector::reverse_iterator expr_iter;
            res = NULL;

            for (expr_iter = actuals.rbegin(); expr_iter != actuals.rend(); ++ expr_iter) {
                Expr_ptr expr = (*expr_iter);
                res = (!res) ? expr : em.make_comma( expr, res );
            }
    })?

    {
      if (! res)
          res = em.make_empty();
    }

	;

postfix_expression returns [Expr_ptr res]
@init { }
	:   lhs=basic_expression
        { $res = lhs; }

    (
        '[' rhs=toplevel_expression ']'
        { $res = em.make_subscript($res, rhs); }
    |
        '(' rhs=params ')'
        { $res = em.make_params($res, rhs); }

        // TODO: nested dot not yet supported
    |   '.' rhs=identifier
        { $res = em.make_dot($res, rhs); }
    )*
    ;

basic_expression returns [Expr_ptr res]
@init { }
    : id=identifier
      { $res = id; }

	| k=constant
      { $res = k; }

	| '(' expr=toplevel_expression ')'
      { $res = expr; }

    | 'switch' '(' expr=toplevel_expression ')'
         clauses = case_clauses[expr]
        'default' ':' dflt=toplevel_expression ';'
      'end' {
            $res = dflt;
            for (ExprVector::reverse_iterator eye = clauses->rbegin();
                 eye != clauses->rend(); ++ eye) {

                    $res = em.make_ite((*eye), $res);
            }
            delete clauses;
        }
	;

case_clauses [Expr_ptr expr] returns [ExprVector_ptr res]
@init { res = new ExprVector (); }
    :
    (
      'case' lhs=toplevel_expression ':' rhs=toplevel_expression ';'
      {
       assert(lhs);
       assert(rhs);
       $res->push_back(em.make_cond( em.make_eq(lhs, expr), rhs));
      }
    )+
    ;

identifiers [ExprVector* ids]
    :
      ident=identifier { ids->push_back(ident); }
      ( ',' ident=identifier { ids->push_back(ident); }  )*
    ;

expressions [ExprVector* exprs]
    :
      expr=toplevel_expression { exprs->push_back(expr); }
      ( ',' expr=toplevel_expression { exprs->push_back(expr); }  )*
    ;

identifier returns [Expr_ptr res]
@init { }
	: IDENTIFIER
      { $res = em.make_identifier((const char*)($IDENTIFIER.text->chars)); }
	;

constant returns [Expr_ptr res]
	: HEX_LITERAL
      {
        Atom tmp((const char*)($HEX_LITERAL.text->chars));
        $res = em.make_hex_const(tmp);
      }

   	| DECIMAL_LITERAL
      {
        Atom tmp((const char*)($DECIMAL_LITERAL.text->chars));
        $res = em.make_dec_const(tmp);
      }

    | OCTAL_LITERAL
      {
        Atom tmp((const char*)($OCTAL_LITERAL.text->chars));
        $res = em.make_oct_const(tmp);
      }
	;

/* pvalue is used in param passing (actuals) */
pvalue returns [Expr_ptr res]
@init {}
	: 'next' '(' expr=postfix_expression ')'
      { $res = em.make_next(expr); }

	| expr=postfix_expression
      { $res = expr; }
	;

/* ordinary values used elsewhere */
value returns [Expr_ptr res]
@init { }
    : expr=postfix_expression
      { $res = expr; }
    ;

type returns [Type_ptr res]
@init {}
    : tp = native_type
      { $res = tp; }

    | tp = enum_type
      { $res = tp; }

    | tp = instance_type
      { $res = tp; }
    ;

native_type returns [Type_ptr res]
@init {}
    : tp = boolean_type
      { $res = tp; }

    | tp = unsigned_int_type
      { $res = tp; }

    | tp = signed_int_type
      { $res = tp; }

    | tp = unsigned_fxd_type
      { $res = tp; }

    | tp = signed_fxd_type
      { $res = tp; }

    ;

boolean_type returns [Type_ptr res]
@init {}
    : 'boolean'
    { $res = tm.find_boolean(); }
    ;

unsigned_int_type returns [Type_ptr res]
@init {
    char *p;
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
            { $res = tm.find_unsigned_array( *p ? atoi(p)
                : OptsMgr::INSTANCE().word_width(), size->value()); }
    |
        {
            $res = tm.find_unsigned( *p ? atoi(p)
                : OptsMgr::INSTANCE().word_width());
        }
    )
    ;

signed_int_type returns [Type_ptr res]
@init {
    char *p;
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
            { $res = tm.find_signed_array( *p ? atoi(p)
                : OptsMgr::INSTANCE().word_width(), size->value()); }
    |
        {
            $res = tm.find_signed( *p ? atoi(p)
                : OptsMgr::INSTANCE().word_width());
        }
    )
    ;

unsigned_fxd_type returns [Type_ptr res]
@init {
    char *p, *q;
}
	:
        UNSIGNED_FXD_TYPE
        {
            p = (char *) $UNSIGNED_FXD_TYPE.text->chars;
            while (!isdigit(*p))
                ++ p;

            q = p;
            while (*q != '.')
                ++ q;

            *(q ++) = 0;
        }
        (
            '[' size=constant ']'
            { $res = tm.find_unsigned_array( atoi(p), atoi(q), size->value()); }
    |
        {
            $res = tm.find_unsigned( atoi(p), atoi(q));
        }
    )
    ;

signed_fxd_type returns [Type_ptr res]
@init {
    char *p, *q;
}
	:
        SIGNED_FXD_TYPE
        {
            p = (char *) $SIGNED_FXD_TYPE.text->chars;
            while (!isdigit(*p))
                ++ p;

            q = p;
            while (*q != '.')
                ++ q;

            *(q ++) = 0;
        }
        (
            '[' size=constant ']'
            { $res = tm.find_signed_array( atoi(p), atoi(q), size->value()); }
    |
        {
            $res = tm.find_signed( atoi(p), atoi(q));
        }
    )
    ;

enum_type returns [Type_ptr res]
@init {
    ExprSet lits;
}
    : '{' lit=literal { lits.insert(lit); } (',' lit=literal { lits.insert(lit); })* '}'
          { $res = tm.find_enum( lits ); }
    ;

instance_type returns [Type_ptr res]
@init {
}
    : module=identifier '(' parameters=params ')'
      { $res = tm.find_instance( module, parameters ); }
    ;

literal returns [Expr_ptr res]
@init { }
    :  expr=identifier
       { $res = expr; }
    ;

// -- Scripting sub-system Toplevel ---------------------------------------------
cmd returns [Command_ptr res]
    : command = commands
    { $res = command; }
    ;

commands returns [Command_ptr res]
    :  c=help_command
       { $res = c; }

    |  c=time_command
       { $res = c; }

    | c=job_command
      { $res = c; }

    |  c=init_command
       { $res = c; }

    |  c=model_command
       { $res = c; }

    |  c=simulate_command
       { $res = c; }

    |  c=verify_command
       { $res = c; }

    |  c=witness_command
       { $res = c; }

    |  c=quit_command
       { $res = c; }
    ;

help_command returns [Command_ptr res]
@init {
    Atom topic;
}
    : 'help'
      ( IDENTIFIER { topic = (const char *) $IDENTIFIER.text->chars; } )?
      { $res = cm.make_help(topic); }
    ;

time_command returns [Command_ptr res]
    : 'time' { $res = cm.make_time(); }
    ;

init_command returns [Command_ptr res]
    : 'init' { $res = cm.make_init(); }
    ;

job_command returns [Command_ptr res]
    :   'job' (

            'list'
            { $res = cm.make_job_list(); }

        |   'status' wid=identifier
            { $res = cm.make_job_status(wid); }

        |   'kill' wid=identifier
            { $res = cm.make_job_kill(wid); }
        )
    ;
model_command returns [Command_ptr res]
    : 'model' (
            'load' fp=filepath
            { $res = cm.make_model_load(fp); }

        |   'dump'
            { $res = cm.make_model_dump(); }
        )
    ;


verify_command returns[Command_ptr res]
@init {
    ExprVector constraints;
}
    : 'verify' property=toplevel_expression

        ( 'with' expr=toplevel_expression
          { constraints.push_back( expr ); }

          ( ',' expr=toplevel_expression
            { constraints.push_back( expr ); }
          ) *
        ) ?

        { $res = cm.make_verify( property, constraints ); }
    ;

witness_command returns [Command_ptr res]
    :   'witness' (

            'list'
            { $res = cm.make_witness_list(); }

        |   'dump' wid=identifier
            { $res = cm.make_witness_dump(wid); }

        )
    ;

simulate_command returns [Command_ptr res]
@init {
    Expr_ptr halt_cond = NULL;
    Expr_ptr resume_id = NULL;
    ExprVector constraints;
}
    : 'simulate'

        ( 'with' expr=toplevel_expression
          { constraints.push_back( expr ); }

          ( ',' expr=toplevel_expression
            { constraints.push_back( expr ); }
          ) *
        ) ?

        ( 'halt' expr=toplevel_expression
          { halt_cond = expr; }
        |  expr=constant
          { halt_cond = expr; }
        ) ?

        (  'resume' wid=identifier
           { resume_id = wid; }
        )?

        { $res = cm.make_simulate( halt_cond, resume_id, constraints ); }
    ;

quit_command returns [Command_ptr res]
    :  'quit'
       { $res = cm.make_quit(); }
    ;

filepath returns [const char *res]
@init { std::ostringstream oss; }
    :
        (
            frag=filepath_fragment
            { oss << frag; }
        ) +
        { $res = oss.str().c_str(); }
    ;

filepath_fragment returns [const char *res]
    :
        IDENTIFIER
        { $res = (const char *) $IDENTIFIER.text->chars; }

    |   '.'
        { $res = "."; }

    |   '/'
        { $res = "/"; }
    ;

// -- Lexer rules --------------------------------------------------------------
UNSIGNED_INT_TYPE
    :  'uint' TYPE_WIDTH?
    ;

SIGNED_INT_TYPE
    :  'int' TYPE_WIDTH?
    ;

UNSIGNED_FXD_TYPE
    :  'ufxd' TYPE_MAG_FRAC
    ;

SIGNED_FXD_TYPE
    :  'fxd' TYPE_MAG_FRAC
    ;

IDENTIFIER
	:	ID_FIRST_CHAR (ID_FOLLOWING_CHARS)*
	;

FILEPATH
    :  (FP_CHARS)+
    ;

fragment TYPE_WIDTH
    : DECIMAL_LITERAL
    ;

fragment TYPE_MAG_FRAC
    : DECIMAL_LITERAL '.' DECIMAL_LITERAL
    ;

fragment ID_FIRST_CHAR
	:	'A'..'Z' | 'a'..'z' | '_'
	;

fragment FP_CHARS
	:	'/' | '.' | '..'
	;

fragment ID_FOLLOWING_CHARS
	:	 ID_FIRST_CHAR
    |    DECIMAL_DIGIT
    |    '$'
    |    '#'
	;

HEX_LITERAL
   : '0' ('x'|'X') HEX_DIGIT+
   ;

DECIMAL_LITERAL
   : ZERO | DECIMAL_FIRST DECIMAL_DIGIT*
   ;

OCTAL_LITERAL
   : ZERO OCTAL_DIGIT+
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
