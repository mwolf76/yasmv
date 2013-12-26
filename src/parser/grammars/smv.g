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
	k = 3; // TODO = 3??
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
    IModule_ptr module;
}


// TODO: support for multiple machines
@init {
    $smv::model = mm.model();
}
    : 'FSM' id=identifier
      {
            $smv::model->set_name(id);

            $smv::module = new Module(em.make_main());
            $smv::model->add_module(em.make_main(), $smv::module);
      }

      module_body ';'? // exit point
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

 ASSERT <expr>, model checking of given properties.
 Returns witness index or UNKNOWN if no witness was found, TRUE if property was found to be true.

 SIMULATE ( RUN | RESUME ) [ CONSTRAINED constraint ( "," constraint )*  ] ( #steps )? [ HALT | PAUSE ON <halt_condition> ]
 Returns witness index or UNSAT if simulation failed.

 >> SIMULATE
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
    :  c=assert_command
       { $res = c; }

    |  c=clk_command
       { $res = c; }

    |  c=sat_command
       { $res = c; }

    |  c=model_command
       { $res = c; }

    | c=init_command
      { $res = c; }

    |  c=simulate_command
       { $res = c; }

    |  c=quit_command
        { $res = c; }
    ;

assert_command returns [Command_ptr res]
    :   'ASSERT' expr=toplevel_expression
        { $res = cm.make_check_invspec(expr); }
    ;

clk_command returns [Command_ptr res]
    : 'CLK' { $res = cm.make_now(); }
    ;

model_command returns [Command_ptr res]
    : 'MODEL' fp=filepath
      { $res = cm.make_load_model(fp); }
    ;

sat_command returns [Command_ptr res]
    : 'SAT' expr=toplevel_expression
       { $res = cm.make_sat(expr); }
    ;

init_command returns [Command_ptr res]
@init {
    ExprVector constraints;
}
    : 'INIT'

        ( 'WITH' expr=toplevel_expression
          { constraints.push_back( expr ); }

          ( ',' expr=toplevel_expression
            { constraints.push_back( expr ); }
          ) *
        ) ?

        {$res = cm.make_init( constraints ); }
    ;

simulate_command returns [Command_ptr res]
@init {
    Expr_ptr halt_cond = em.make_false();
    ExprVector constraints;
}
    : 'SIMULATE'

        ( 'WITH' expr=toplevel_expression
          { constraints.push_back( expr ); }

          ( ',' expr=toplevel_expression
            { constraints.push_back( expr ); }
          ) *
        ) ?

        ( 'HALT' 'ON' expr=toplevel_expression
          { halt_cond = expr; }
        ) ?

        {$res = cm.make_simulate( halt_cond, constraints ); }
    ;

resume_command returns [Command_ptr res]
@init {
    Expr_ptr halt_cond = em.make_false();
    ExprVector constraints;
}
    : 'RESUME' wid=identifier

        ( 'WITH' expr=toplevel_expression
          { constraints.push_back( expr ); }

          ( ',' expr=toplevel_expression
            { constraints.push_back( expr ); }
          ) *
        ) ?

        ( 'HALT' 'ON' expr=toplevel_expression
          { halt_cond = expr; }
        ) ?

        {$res = cm.make_resume( halt_cond, constraints, wid); }
    ;

quit_command returns [Command_ptr res]
    :  'QUIT'
       { $res = cm.make_quit(); }
    ;

// -------------------------------------------------------------------------------

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

// FSM definition entry point
module_body
    :	module_decl ( ';' module_decl )*
    ;

module_decl
    :	/* variables and defines */
        fsm_var_decl
    |   fsm_enum_decl
	|	fsm_define_decl

		/* FSM definition */
	|	fsm_init_decl
    |   fsm_invar_decl
	|	fsm_trans_decl
    ;

fsm_var_decl
    : 'VAR'  fsm_var_decl_body
    ;

fsm_enum_decl
    : 'ENUM' fsm_enum_decl_body
    ;

fsm_enum_decl_body
    : fsm_enum_decl_clause
        ( ';' fsm_enum_decl_clause)*
    ;

fsm_enum_decl_clause
@init {
    ExprSet lits;
}
    : expr=identifier ':' fsm_enum_type_lits[lits]
      { tm.add_enum( $smv::module->expr(), expr, lits ); }
    ;

fsm_enum_type_lits [ExprSet& lits]
	:
     '{'
          lit=literal
          { $lits.insert(lit); }

          (',' lit=literal
          { $lits.insert(lit); }
          )*
     '}'
	;

fsm_var_decl_body
	: fsm_var_decl_clause
        ( ';' fsm_var_decl_clause)*
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
                Expr_ptr id = (*expr_iter);
                IVariable_ptr var = new Variable($smv::module->expr(), id, tp);
                $smv::module->add_var(id, var);
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
     IDefine_ptr def = new Define($smv::module->expr(), id, formals, body);
     $smv::module->add_def(id, def);
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
      { $smv::module->add_init(expr); }
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
      { $smv::module->add_invar(expr); }
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
      { $smv::module->add_trans(expr); }
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
	: lhs=ltl_formula
      { $res = lhs; }

    (
      '&' rhs=ltl_formula
      { $res = em.make_and($res, rhs); }
    )*
	;

ltl_formula returns [Expr_ptr res]
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

    | 'mod' rhs=cast_expression
      { $res = em.make_mod($res, rhs); }
    )*
	;

cast_expression returns [Expr_ptr res]
@init {
    Expr_ptr cast = NULL;
}
    : '(' tp = castable_type ')' expr = cast_expression
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

	| 'prev' '(' expr=toplevel_expression ')'
      { $res = em.make_prev(expr); }

	| '!' expr=postfix_expression
      { $res = em.make_not(expr); }

    | '-' expr=postfix_expression
      { $res = em.make_neg(expr); }

	;

actual_params returns [Expr_ptr res]
@init {
    ExprVector actuals;
}
	: expressions[&actuals]
    {
            ExprVector::reverse_iterator expr_iter;
            res = NULL;

            for (expr_iter = actuals.rbegin(); expr_iter != actuals.rend(); ++ expr_iter) {
                Expr_ptr expr = (*expr_iter);
                res = (!res) ? expr : em.make_comma( expr, res );
            }
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
        '(' rhs=actual_params ')'
        { $res = em.make_params($res, rhs); }

        // TODO: nested dot not supported
    |   '.' rhs=identifier
        { $res = em.make_dot($res, rhs); }

    )*
    ;

basic_expression returns [Expr_ptr res]
@init { }
	: err=error
      { $res = err; }

    | id=identifier
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

error returns [Expr_ptr res]
@init {}
    : 'ERR'
    { $res = em.make_error(); }
    ;

/* pvalue is used in param passing (actuals) */
pvalue returns [Expr_ptr res]
@init {}
	: 'next' '(' expr=postfix_expression ')'
      { $res = em.make_next(expr); }

    | 'prev' '(' expr=postfix_expression ')'
      { $res = em.make_prev(expr); }

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
    : tp = castable_type
      { $res = tp; }

    | tp = enum_type
      { $res = tp; }
    ;

castable_type returns [Type_ptr res]
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
            while (!isdigit(*p)) ++ p; // skip to width
        }
        (
            '[' size=constant ']'
            { $res = tm.find_unsigned_array( atoi(p), size->value()); }
    |
        {
            $res = tm.find_unsigned( atoi(p));
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
            while (!isdigit(*p)) ++ p; // skip to width
        }
        (
            '[' size=constant ']'
            { $res = tm.find_signed_array( atoi(p), size->value()); }
    |
        {
            $res = tm.find_signed( atoi(p));
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
            while (!isdigit(*p)) ++ p; // skip to magnitude

            q = p;
            while (*q != '.') ++ q; // skip to fractional

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
            while (!isdigit(*p)) ++ p; // skip to magnitude

            q = p;
            while (*q != '.') ++ q; // skip to fractional

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
@init {}
    : expr=identifier
      { $res = tm.find_enum( $smv::module->expr(), expr ); }
    ;

literal returns [Expr_ptr res]
@init { }
    :  expr=identifier
       { $res = expr; }
    ;

/** Lexer rules */
UNSIGNED_INT_TYPE
    :  'uint' TYPE_WIDTH
    ;

SIGNED_INT_TYPE
    :  'int' TYPE_WIDTH
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
