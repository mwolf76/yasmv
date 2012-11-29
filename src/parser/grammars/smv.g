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
	k = 3;
    memoize = true;
    language = C;
}

@header {
#include <common.hh>

/* cmd subsystem */
#include <cmd.hh>

#include <expr.hh>
#include <expr_mgr.hh>

#include <type.hh>
#include <type_mgr.hh>

#include <model.hh>
#include <model_mgr.hh>

}

@members {
    // singleton managers
    ExprMgr& em = ExprMgr::INSTANCE();
    ModelMgr& mm = ModelMgr::INSTANCE();
    TypeMgr& tm = TypeMgr::INSTANCE();

    // cmd subsystem
    CommandMgr& cm = CommandMgr::INSTANCE();
}

/* SMV model Toplevel */
smv
scope {
    IModel_ptr model;
}

@init {
    $smv::model = mm.model();
}
    : 'MODEL' id=identifier
      { $smv::model->set_name(id); }

      modules ';'? // exit point
    ;

/* Scripting sub-system Toplevel */
cmd returns [Command_ptr res]
    : command = commands
    { $res = command; }
    ;

/* Commands to be implemented:

 * SAT <expr> [ ; <expr]* -- pure satisfiability problem on a (set of)
 propositional formulas. Requires variable definitions in separate
 model. Returns UNSAT, or a witness #

 * I/O
 READ MODEL <filename> - load a new model from file (stdin not supported)
 Returns OK, <0 errcode otherwise

 DUMP MODEL [ TO <filename> ] - save a new model to file
 Returns OK, <0 errcode otherwise

 READ TRACE <filename> - load a trace from .json file (stdin not supported)
 Returns trace#, <0 errcode otherwise

 DUMP TRACE #trace [ TO <filename> ] - save a trace to .json file
 Returns OK, <0 errcode otherwise

 * Model
 ANALYZE - analyzes the model and prints stats to stdout.
 Returns nothing.

 * MC

 INVAR <expr>, model checking of given properties.
 Returns witness index or UNKNOWN if no witness was found, TRUE if property was found to be true.

 SIMULATE [ INIT | RESUME #trace ] [#steps] [CONSTRAINED constraint1] [GUIDED <#trace>]...
 Returns witness index or UNSAT if simulation failed.

 >> SIMULATE
 OK. Created Trace (#4)

 >> SIMULATE INIT
 OK. Created Trace (#4)

 * TRACE

 SHOW TRACES
 TRACE

 PRINT TRACE

 * OTHERS

 CLK
 Returns CPU time in millisecs

 FORMAT "FMT", ...
 Returns a formatted message.

 PRINT "FMT", ...
 Same as above. Always prints to STDOUT.

 SH <shell command>
 Returns the output of an embedded shell command.

 SET "name" TO "value" (eg. SET general.verbosity TO TRUE)
 Returns current value

 GET "name"
 Returns current value

 * CONTROL
 LET <var> BE <expr> (e.g. LET t0 BE NOW -q)

 IF (...) DO  ... END, if control block
 WHILE (...) DO ... END, while control block

 QUIT [-r retcode], terminates the program
*/
commands returns [Command_ptr res]
    :
        'SAT' expr=toplevel_expression
        { $res = cm.make_sat(expr); }

    |   'ASSERT' expr=toplevel_expression
        { $res = cm.make_check_invspec(expr); }

    |   'CLK'
        { $res = cm.make_now(); }

    |   'MODEL' fp=filepath
        { $res = cm.make_load_model(fp); }

    |   'QUIT'
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

modules
scope { IModule_ptr module ; }
@init { $modules::module = NULL; }

    : ( 'MODULE' id=identifier
      {
        $modules::module = new Module(id);
        $smv::model->add_module(id, $modules::module);
      }

      formal_params? fsm_isa_decl_clause* module_body
      )*
    ;

formal_params
	:	'('
        id=identifier
        { $modules::module->add_formalParam(id); }

        ( ',' id=identifier
        { $modules::module->add_formalParam(id); }
        )*
        ')'
    ;

// FSM definition entry point
module_body
    :	module_decl ( ';' module_decl )*
    ;

module_decl
    :	/* variables and defines */
        fsm_var_decl
	|	fsm_define_decl

		/* FSM definition */
	|	fsm_init_decl
	|	fsm_trans_decl
    ;

fsm_isa_decl_clause
	: 'ISA' id=identifier
       { $modules::module->add_isaDecl(id); }
	;

fsm_var_decl
    : 'VAR' fsm_var_decl_body
    ;

fsm_var_decl_body
	: fsm_var_decl_clause
        ( ';' fsm_var_decl_clause)*
	;

fsm_var_decl_clause
@init {
    ExprVector ev;
}
	: ids=identifiers[&ev] ':' tp=type_name
    {
            ExprVector::iterator expr_iter;
            assert(NULL != tp);
            for (expr_iter = ev.begin(); expr_iter != ev.end(); ++ expr_iter) {
                Expr_ptr id = (*expr_iter);
                IVariable_ptr var = new StateVar($modules::module->expr(), id, tp);
                $modules::module->add_localVar(id, var);
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
	: id=identifier ':=' body=toplevel_expression
    {
      IDefine_ptr def = new Define($modules::module->expr(), id, body);
      $modules::module->add_localDef(id, def);
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
      { $modules::module->add_init(expr); }
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
      { $modules::module->add_trans(expr); }
	;

toplevel_expression returns [Expr_ptr res]
@init { }
	: expr=iff_expression {
         $res = expr;
      } (
            '?' lhs=toplevel_expression ':' rhs=toplevel_expression
            { $res = em.make_ite(em.make_cond($res, lhs), rhs); }
      )?
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
	: lhs=inclusive_or_expression
      { $res = lhs; }

    (
      '->' rhs=inclusive_or_expression
      { $res = em.make_implies($res, rhs); }
    )*
    ;

inclusive_or_expression returns [Expr_ptr res]
@init { }
	: lhs=exclusive_or_expression
      { $res = lhs; }

    (
      '|' rhs=exclusive_or_expression
      { $res = em.make_or($res, rhs); }
    )*
	;

exclusive_or_expression returns [Expr_ptr res]
@init { }
	: lhs=and_expression
      { $res = lhs; }

    (
      'xor' rhs=and_expression
     { $res = em.make_xor($res, rhs); }

    |  'xnor' rhs=and_expression
     { $res = em.make_xnor($res, rhs); }
    )*
	;

and_expression returns [Expr_ptr res]
@init { }
	: lhs=equality_expression
      { $res = lhs; }

    (
      '&' rhs=equality_expression
      { $res = em.make_and($res, rhs); }
    )*
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
	: lhs=unary_expression
      { $res = lhs; }
    (
      '*' rhs=unary_expression
      { $res = em.make_mul($res, rhs); }

    | '/' rhs=unary_expression
      { $res = em.make_div($res, rhs); }

    | 'mod' rhs=unary_expression
      { $res = em.make_mod($res, rhs); }
    )*
	;

unary_expression returns [Expr_ptr res]
@init { }
	: expr=postfix_expression
      { $res = expr; }

	| 'next' '(' expr=toplevel_expression ')'
      { $res = em.make_next(expr); }

	| '!' expr=postfix_expression
      { $res = em.make_not(expr); }

    | '-' expr=postfix_expression
      { $res = em.make_neg(expr); }

	;

postfix_expression returns [Expr_ptr res]
@init { }
	:   lhs=basic_expression
        { $res = lhs; }

    (
        '[' rhs=basic_expression ']'
        { $res = em.make_subscript($res, rhs); }

    |   '.' rhs=basic_expression
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

    | 'case'
           cls=case_clauses

      'esac' {
           for (ExprVector::reverse_iterator eye = cls->rbegin();
                eye != cls->rend(); ++ eye) {
                if (!res) {
                    res = (*eye)->rhs(); /* default value */
                }
                else {
                    res = const_cast<Expr_ptr>( em.make_ite( (*eye), res));
                }
           }
           delete cls;  // avoid memleaks
      }

	;

case_clauses returns [ExprVector_ptr res]
@init { res = new ExprVector (); }
    :
    (
      lhs=toplevel_expression ':' rhs=toplevel_expression ';'
      {
       assert(lhs); assert(rhs);
       $res->push_back(em.make_cond(lhs, rhs));
      }
    )+
    ;

identifiers [ExprVector* ids]
    :
      ident=identifier { ids->push_back(ident); }
      ( ',' ident=identifier { ids->push_back(ident); }  )*
    ;

identifier returns [Expr_ptr res]
@init { }
	: IDENTIFIER
      { $res = em.make_identifier((const char*)($IDENTIFIER.text->chars)); }
	;

constant returns [Expr_ptr res]
@init { }
    :	k=enum_constant
        { $res = k; }

    |   k=range_constant // holds int_constants as well
        { $res = k; }

    ;

int_constant returns [Expr_ptr res]
@init { }
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

range_constant returns [Expr_ptr res]
@init { }
	: lhs=int_constant
      { $res = lhs; }

      ('..' rhs=int_constant
      { $res = em.make_range_type(lhs, rhs); }
      )?
	;

enum_constant returns [Expr_ptr res]
@init {
    ExprSet lits;
}
	: enum_type[lits]
    { $res = em.make_enum_type(lits); }
    ;

// /* lvalue is used in assignments */
// lvalue returns [Expr_ptr res]
// @init { }
// 	: 'init' '(' expr=postfix_expression ')'
//       { $res = em.make_init(expr); }

// 	| 'next' '(' expr=postfix_expression ')'
//       { $res = em.make_next(expr); }

// 	| expr=postfix_expression
//       { $res = expr; }
// 	;

/* pvalue is used in param passing (actuals) */
pvalue returns [Expr_ptr res]
@init { }
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

type_name returns [Type_ptr res]
@init {
    ExprSet lits;
}
    // boolean
	: 'boolean'
    { $res = tm.find_boolean(); }

    // finite integer types
    | 'unsigned' '(' width=int_constant ')'
      { $res = tm.find_unsigned(width->value()); }
	| 'signed' '(' k=int_constant ')'
      { $res = tm.find_signed(width->value()); }

    // ranges
    // | lhs=int_constant '..' rhs=int_constant
    //   { $res = tm.find_range(lhs, rhs); }

    // enumeratives, pure symbolic
	| enum_type[lits]
      { $res = tm.find_enum(lits); }

    // instances
    | id=identifier
      { $res = tm.find_instance(id); }  actual_param_decls[$res]
    ;

enum_type [ExprSet& lits]
	:
     '{'
          lit=literal
          { $lits.insert(lit); }

          (',' lit=literal
          { $lits.insert(lit); }
          )*
     '}'
	;

actual_param_decls [Type_ptr m]
	:
     // '('
     //      ap=pvalue
     //        { ((Instance*)(m)) -> add_param(ap); }

     //      (',' pvalue
     //      { ((Instance*)(m)) -> add_param(ap); }
     //      )*
     // ')'
    ;

literal returns [Expr_ptr res]
@init { }
    :  expr=identifier
       { $res = expr; }

    |  expr=int_constant
       { $res = expr; }
    ;

/** Lexer rules */
IDENTIFIER
	:	ID_FIRST_CHAR (ID_FOLLOWING_CHARS)*
	;

FILEPATH
    :  (FP_CHARS)+
    ;

WORD_CONSTANT
    :   '0' ('s' | 'u') DECIMAL_LITERAL '_' HEX_DIGIT +
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
//    |    '$'
//    |    '#'
//    |    '-'
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
   : '--' ~('\n'|'\r')* '\r'? '\n'
     { $channel=HIDDEN; }
   ;
