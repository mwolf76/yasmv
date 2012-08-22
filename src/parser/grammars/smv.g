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
	k = 2; /* LL(1) grammar with a few exceptions */
    memoize = true;
    language = C;
}

@header {
#include <common.hh>
#include <expr.hh>
#include <types.hh>
#include <expr_mgr.hh>
#include <model.hh>

#define PROP_EXPR 0
#define LTL_EXPR 1
#define CTL_EXPR 2
// ...
}

@members {
    // singleton managers
    ExprMgr& em = ExprMgr::INSTANCE();
    ModelMgr& mm = ModelMgr::INSTANCE();
    TypeMgr& tm = TypeMgr::INSTANCE();
}

/* Toplevel */
smv
scope {
    IModel_ptr model;
    int mode;
}

@init {
    $smv::model = mm.get_model();
    $smv::mode = PROP_EXPR;
}
    : modules ';'?
    ;

/** CTL  properties */
ctl_spec returns [Expr_ptr res]
@init { }
    : ( 'SPEC' | 'CTLSPEC') formula=ctl_formula
     { $res = formula; }
	;

ctl_formula returns [Expr_ptr res]
@init { int prev_mode; }
	:
        { prev_mode = $smv::mode; $smv::mode= CTL_EXPR; }
        formula=binary_ctl_formula

        { $smv::mode = prev_mode; $res = formula; }
    ;

binary_ctl_formula returns [Expr_ptr res]
@init { }
	:	lhs=unary_ctl_formula
        { $res = lhs; }
        (
           'AU' rhs=unary_ctl_formula
           { $res = em.make_AU($res, rhs); }

        |
           'EU' rhs=unary_ctl_formula
           { $res = em.make_EU($res, rhs); }

        |
           'AR' rhs=unary_ctl_formula
           { $res = em.make_AR($res, rhs); }

        |
           'ER' rhs=unary_ctl_formula
           { $res = em.make_ER($res, rhs); }

        )*
	;

unary_ctl_formula returns [Expr_ptr res]
@init { }
	:
       'AG' formula=unary_ctl_formula
       { $res = em.make_AG(formula); }
    |
       'EG' formula=unary_ctl_formula
       { $res = em.make_EG(formula); }
    |
       'AF' formula=unary_ctl_formula
       { $res = em.make_AF(formula); }
    |
       'EF' formula=unary_ctl_formula
       { $res = em.make_EF(formula); }
    |
       'AX' formula=unary_ctl_formula
       { $res = em.make_AX(formula); }
    |
       'EX' formula=unary_ctl_formula
       { $res = em.make_EX(formula); }

    |   formula=untimed_expression
       { $res = formula; }
	;

/** LTL properties */
ltl_spec returns [Expr_ptr res]
@init { }
    : 'LTLSPEC' formula=ltl_formula
     { $res = formula; }
	;

ltl_formula returns [Expr_ptr res]
@init { int prev_mode; }
	:
        { prev_mode = $smv::mode; $smv::mode= LTL_EXPR; }
        formula=binary_ltl_formula

        { $smv::mode = prev_mode; $res = formula; }
    ;

binary_ltl_formula returns [Expr_ptr res]
@init { }
	:	lhs=unary_ltl_formula
        { $res = lhs; } (
            'U' rhs=unary_ltl_formula
           { $res = em.make_U($res, rhs); }

        |   'R' rhs=unary_ltl_formula
           { $res = em.make_R($res, rhs); } )*
	;

unary_ltl_formula returns [Expr_ptr res]
@init { }
	:	'G' formula=unary_ltl_formula
       { $res = em.make_G(formula); }

	|	'F' formula=unary_ltl_formula
       { $res = em.make_F(formula); }

	|	'X' formula=unary_ltl_formula
       { $res = em.make_X(formula); }

    |   formula=untimed_expression
       { $res = formula; }
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

property
    : formula=ltl_spec
      { $modules::module->add_ltlspec(formula); }

    |
      formula=ctl_spec
      { $modules::module->add_ctlspec(formula); }
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
	|	fsm_ivar_decl
	|	fsm_frozenvar_decl
	|	fsm_define_decl

		/* relational FSM */
	|	fsm_init_decl
	|	fsm_invar_decl
	|	fsm_trans_decl
    |   fsm_fairn_decl

        /* functional FSM */
	|	assignment_formula

        /* properties */
    |   property
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
	: id=identifier ':' tp=type_name
    {
      IVariable_ptr var = new StateVar($modules::module->expr(), id, tp);
      $modules::module->add_localVar(id, var);
    }
	;

fsm_ivar_decl
    : 'IVAR' fsm_ivar_decl_body
    ;

fsm_ivar_decl_body
	: fsm_ivar_decl_clause
        ( ';' fsm_ivar_decl_clause)*
	;

fsm_ivar_decl_clause
	: id=identifier ':' tp=type_name
    {
      IVariable_ptr var = new InputVar($modules::module->expr(), id, tp);
      $modules::module->add_localVar(id, var);
    }
	;

fsm_frozenvar_decl
    : 'FROZENVAR' fsm_frozenvar_decl_body
    ;

fsm_frozenvar_decl_body
	: fsm_frozenvar_decl_clause
        ( ';' fsm_frozenvar_decl_clause)*
	;

fsm_frozenvar_decl_clause
	: id=identifier ':' tp=type_name
    {
      IVariable_ptr var = new FrozenVar($modules::module->expr(), id, tp);
      $modules::module->add_localVar(id, var);
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
	: id=identifier ':=' body=untimed_expression
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
	: expr=untimed_expression
      { $modules::module->add_init(expr); }
	;

fsm_invar_decl
    : 'INVAR' fsm_invar_decl_body
    ;

fsm_invar_decl_body
	: fsm_invar_decl_clause
        (';' fsm_invar_decl_clause)*
	;

fsm_invar_decl_clause
	: expr=untimed_expression
      { $modules::module->add_invar(expr); }
	;

fsm_trans_decl
    : 'TRANS' fsm_trans_decl_body
    ;

fsm_trans_decl_body
	: fsm_trans_decl_clause
        (';' fsm_trans_decl_clause)*
	;

fsm_trans_decl_clause
	: expr=untimed_expression
      { $modules::module->add_trans(expr); }
	;

fsm_fairn_decl
    : 'FAIRNESS' fsm_fairn_decl_body
    ;

fsm_fairn_decl_body
	: fsm_fairn_decl_clause
        (';' fsm_fairn_decl_clause)*
	;

fsm_fairn_decl_clause
	: expr=untimed_expression
      { $modules::module->add_fairness(expr); }
	;

assignment_formula
	: 'ASSIGN' assignment_body
	;

assignment_body
	: assignment_clause (
            ';' assignment_clause) *
	;

assignment_clause
	: id=lvalue ':=' body=untimed_expression
      {
       IDefine_ptr def = new Define($modules::module->expr(), id, body);
       $modules::module->add_assign(id, def);
      }
    ;

// main expression entry point
untimed_expression returns [Expr_ptr res]
@init { }
	: expr=case_expression
      { $res = expr; }

	| expr=cond_expression
      { $res = expr; }
	;

case_expression returns [Expr_ptr res]
@init { ExprVector_ptr clauses = new ExprVector (); }
	: 'case' cls=case_clauses 'esac'
      {
        for (ExprVector::reverse_iterator eye = cls->rbegin(); eye != cls->rend();
             eye ++) {
            if (!res) res = (*eye);
            else {
                res = const_cast<Expr_ptr>(em.make_ite((*eye), res));
            }
        }
      }
	;

case_clauses returns [ExprVector_ptr res]
@init { res = new ExprVector (); }
    :
    (
      lhs=untimed_expression ':' rhs=untimed_expression ';'
      {
       assert(lhs); assert(rhs);
       $res->push_back(em.make_cond(lhs, rhs));
      }
    )+
    ;

cond_expression returns [Expr_ptr res]
@init { }
	: expr=iff_expression
      { $res = expr; }

    (
      '?' lhs=untimed_expression ':' rhs=cond_expression
      { $res = em.make_ite(em.make_cond($res, lhs), rhs); }
    )?
	;

iff_expression returns [Expr_ptr res]
@init { }
	:  lhs=imply_expression
       { $res = lhs; }

    (
       '<->' rhs=imply_expression
       { $res = em.make_iff($res, rhs); }
    )*
	;

imply_expression returns [Expr_ptr res]
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
	: lhs=union_expression
      { $res = lhs; }

    (
      '<' rhs=union_expression
     { $res = em.make_lt($res, rhs); }

    | '<=' rhs=union_expression
     { $res = em.make_le($res, rhs); }

    | '>=' rhs=union_expression
     { $res = em.make_ge($res, rhs); }

    | '>' rhs=union_expression
     { $res = em.make_gt($res, rhs); }
    )*
	;

union_expression returns [Expr_ptr res]
@init { }
    : lhs=member_expression
     { $res= lhs; }

    (
      'union' rhs=member_expression
     { $res = em.make_union($res, rhs); }
    )*
    ;

member_expression returns [Expr_ptr res]
@init { }
    : lhs=shift_expression
      { $res = lhs; }

    (
      'in' rhs=shift_expression
      { $res = em.make_member($res, rhs); }
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
	: lhs=concatenative_expression
      { $res = lhs; }

    (
      '*' rhs=concatenative_expression
      { $res = em.make_mul($res, rhs); }

    | '/' rhs=concatenative_expression
      { $res = em.make_div($res, rhs); }

    | 'mod' rhs=concatenative_expression
      { $res = em.make_mod($res, rhs); }
    )*
	;

concatenative_expression returns [Expr_ptr res]
@init { }
	: lhs=unary_expression
      { $res = lhs; }

    (
       '::' rhs=unary_expression
       { $res = em.make_concat($res, rhs); }
    )*
	;

unary_expression returns [Expr_ptr res]
@init { }
	: expr=postfix_expression
      { $res = expr; }

	| 'next' '(' expr=postfix_expression ')'
      { $res = em.make_next(expr); }

	| '!' expr=postfix_expression
      { $res = em.make_not(expr); }

    | '-' expr=postfix_expression
      { $res = em.make_neg(expr); }

    | 'toint' '(' expr=postfix_expression ')'
       { $res = em.make_toint(expr); }

    | 'bool' '(' expr=postfix_expression ')'
       { $res = em.make_bool(expr); }

    | 'word1' '(' expr=postfix_expression ')'
       { $res = em.make_word1(expr); }

    | 'signed' '(' expr=postfix_expression ')'
       { $res = em.make_signed(expr); }

    | 'unsigned' '(' expr=postfix_expression ')'
       { $res = em.make_unsigned(expr); }

    | 'count' '(' expr=postfix_expression ')'
       { $res = em.make_count(expr); }
	;

postfix_expression returns [Expr_ptr res]
@init { }
	:   lhs=primary_expression
        { $res = lhs; }

    (
        '[' rhs=primary_expression ']'
        { $res = em.make_subscript($res, rhs); }

    |   '.' rhs=primary_expression
        { $res = em.make_dot($res, rhs); }

    )*
    ;

primary_expression returns [Expr_ptr res]
@init { }
	: id=identifier
      { $res = id; }

	| k=constant
      { $res = k; }

	| '(' (
            { $smv::mode == LTL_EXPR }?=> expr=ltl_formula ')'
            { $res = expr; }

	      | { $smv::mode == PROP_EXPR }?=> expr=untimed_expression ')'
            { $res = expr; }
          )
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

    |   k=range_constant
        { $res = k; }

    |   k=word_constant
        { $res = k; }
    ;

word_constant returns [Expr_ptr res]
@init { }
    : WORD_CONSTANT
      { $res = em.make_wconst((const char*)($WORD_CONSTANT.text->chars)); }
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
      { $res = em.make_range(lhs, rhs); }
      )?
	;

enum_constant returns [Expr_ptr res]
@init { }
	: literals=enum_type
    { $res = em.make_enum(literals); }
    ;

/* lvalue is used in assignments */
lvalue returns [Expr_ptr res]
@init { }
	: 'init' '(' expr=postfix_expression ')'
      { $res = em.make_init(expr); }

	| 'next' '(' expr=postfix_expression ')'
      { $res = em.make_next(expr); }

	| expr=postfix_expression
      { $res = expr; }
	;

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
@init { }
	: 'boolean'
    { $res = tm.find_boolean(); }

	| literals=enum_type
      { $res = tm.find_enum($modules::module->expr(), literals); }

    | lhs=int_constant '..' rhs=int_constant
      { $res = tm.find_range(lhs, rhs); }

    | 'unsigned'? 'word' '[' k=int_constant ']'
      { $res = tm.find_uword(k); }

	| 'signed' 'word' '[' k=int_constant ']'
      { $res = tm.find_sword(k); }

    | id=identifier
      { $res = tm.find_instance(id); }  actual_param_decls[$res]
    ;

enum_type returns [ExprSet_ptr res]
@init { res = new ExprSet (); }
	:
     '{'
          lit=literal
          { $res->insert(lit); }

          (',' lit=literal
          { $res->insert(lit); }
          )*
     '}'
	;

actual_param_decls [Type_ptr m]
	:
     '('
          ap=pvalue
            { ((Instance*)(m)) -> add_param(ap); }

          (',' pvalue
          { ((Instance*)(m)) -> add_param(ap); }
          )*
     ')'
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

WORD_CONSTANT
    :   '0' ('s' | 'u') DECIMAL_LITERAL '_' HEX_DIGIT +
    ;

fragment ID_FIRST_CHAR
	:	'A'..'Z' | 'a'..'z' | '_'
	;

fragment ID_FOLLOWING_CHARS
	:	 ID_FIRST_CHAR
    |    DECIMAL_DIGIT
    |    '$'
    |    '#'
    |    '-'
	;

HEX_LITERAL
   : '0' ('x'|'X') HEX_DIGIT
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
