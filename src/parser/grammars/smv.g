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
}

@members {
    // singleton managers
    ExprMgr& em = ExprMgr::INSTANCE();
    ModelMgr& mm = ModelMgr::INSTANCE();
    TypeMgr& tm = TypeMgr::INSTANCE();
}

/* Toplevel */
smv
scope { IModel_ptr model; }
@init { $smv::model = mm.get_model(); }
    : modules
    ;

// backjump entry point (see README below)
temporal_formula returns [Expr_ptr res]
@init { res = NULL; }
    : formula=ltl_formula
     { $res = formula; }
    ;

/** LTL properties */
ltl_spec returns [Expr_ptr res]
@init { res = NULL; }
    : 'LTLSPEC' formula=ltl_formula
     { $res = formula; }
	;

ltl_formula returns [Expr_ptr res]
@init { res = NULL; }
	:	formula=binary_ltl_formula
       { $res = formula; }
    ;

binary_ltl_formula returns [Expr_ptr res]
@init { res = NULL; }
	:	lhs=unary_ltl_formula
        { $res = lhs; } (
            'U' rhs=unary_ltl_formula
           { $res = em.make_U($res, rhs); }

        |   'R' rhs=unary_ltl_formula
           { $res = em.make_R($res, rhs); } )*
	;

unary_ltl_formula returns [Expr_ptr res]
@init { res = NULL; }
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
        $smv::model->add_module($modules::module);
      }

      formal_params? fsm_isa_decl_clause* module_body
      )*
    ;

properties
    : (property ';'?)*
    ;

property
    : formula=ltl_spec
      { $modules::module->add_ltlspec(formula); }
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
    :	module_decl
        ( ';' module_decl )*
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
      IVariable_ptr var = new StateVar(id, tp);
      $modules::module->add_localVar(var);
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
      IVariable_ptr var = new InputVar(id, tp);
      $modules::module->add_localVar(var);
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
      IVariable_ptr var = new FrozenVar(id, tp);
      $modules::module->add_localVar(var);
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
      IDefine_ptr def = new Define(id, body);
      $modules::module->add_localDef(def);
    }
	;

fsm_init_decl
    : 'INIT' fsm_init_decl_body
    ;

fsm_init_decl_body
	: fsm_init_decl_clause +
	;

fsm_init_decl_clause
	: expr=untimed_expression ';'
      { $modules::module->add_init(expr); }
	;

fsm_invar_decl
    : 'INVAR' fsm_invar_decl_body
    ;

fsm_invar_decl_body
	: fsm_invar_decl_clause +
	;

fsm_invar_decl_clause
	: expr=untimed_expression ';'
      { $modules::module->add_invar(expr); }
	;

fsm_trans_decl
    : 'TRANS' fsm_trans_decl_body
    ;

fsm_trans_decl_body
	: fsm_trans_decl_clause +
	;

fsm_trans_decl_clause
	: expr=untimed_expression ';'
      { $modules::module->add_trans(expr); }
	;

fsm_fairn_decl
    : 'FAIRNESS' fsm_fairn_decl_body
    ;

fsm_fairn_decl_body
	: fsm_fairn_decl_clause +
	;

fsm_fairn_decl_clause
	: expr=untimed_expression ';'
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
	: id=lvalue ':=' expr=untimed_expression
      {
       IAssign_ptr assgn = new Assign(id, expr);
       $modules::module->add_assign(assgn);
      }
    ;

// main expression entry point
untimed_expression returns [Expr_ptr res]
@init { res = NULL; }
	: expr=case_expression
      { $res = expr; }

	| expr=cond_expression
      { $res = expr; }
	;

case_expression returns [Expr_ptr res]
@init { Exprs clauses; res = NULL; }
	: 'case' cls=case_clauses 'esac'
      {
        for (Exprs::reverse_iterator eye = cls.rbegin(); eye != cls.rend();
             eye ++) {
            if (!res) res = (*eye);
            else {
                res = const_cast<Expr_ptr>(em.make_ite((*eye), res));
            }
        }
      }
	;

case_clauses returns [Exprs res]
    :
    (
      lhs=untimed_expression ':' rhs=untimed_expression ';'
      {
assert(lhs);
assert(rhs);
$res.push_back(em.make_cond(lhs, rhs)); }
    )+
    ;

cond_expression returns [Expr_ptr res]
@init { res = NULL; }
	: expr=iff_expression
      { $res = expr; }

    (
      '?' lhs=untimed_expression ':' rhs=cond_expression
      { $res = em.make_ite(em.make_cond($res, lhs), rhs); }
    )?
	;

iff_expression returns [Expr_ptr res]
@init { res = NULL; }
	:  lhs=imply_expression
       { $res = lhs; }

    (
       '<->' rhs=imply_expression
       { $res = em.make_iff($res, rhs); }
    )*
	;

imply_expression returns [Expr_ptr res]
@init { res = NULL; }
	: lhs=inclusive_or_expression
      { $res = lhs; }

    (
      '->' rhs=inclusive_or_expression
      { $res = em.make_implies($res, rhs); }
    )*
    ;

inclusive_or_expression returns [Expr_ptr res]
@init { res = NULL; }
	: lhs=exclusive_or_expression
      { $res = lhs; }

    (
      '|' rhs=exclusive_or_expression
      { $res = em.make_or($res, rhs); }
    )*
	;

exclusive_or_expression returns [Expr_ptr res]
@init { res = NULL; }
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
@init { res = NULL; }
	: lhs=equality_expression
      { $res = lhs; }

    (
      '&' rhs=equality_expression
      { $res = em.make_and($res, rhs); }
    )*
	;

equality_expression returns [Expr_ptr res]
@init { res = NULL; }
	: lhs=relational_expression
      { $res = lhs; }

    ( '=' rhs=relational_expression
     { $res = em.make_eq($res, rhs); }

    | '!=' rhs=relational_expression
     { $res = em.make_ne($res, rhs); }
    )*
	;

relational_expression returns [Expr_ptr res]
@init { res = NULL; }
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
@init { res = NULL; }
    : lhs=member_expression
     { $res= lhs; }

    (
      'union' rhs=member_expression
     { $res = em.make_union($res, rhs); }
    )*
    ;

member_expression returns [Expr_ptr res]
@init { res = NULL; }
    : lhs=shift_expression
      { $res = lhs; }

    (
      'in' rhs=shift_expression
      { $res = em.make_member($res, rhs); }
    )*
    ;

shift_expression returns [Expr_ptr res]
@init { res = NULL; }
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
@init { res = NULL; }
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
@init { res = NULL; }
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
@init { res = NULL; }
	: lhs=unary_expression
      { $res = lhs; }

    (
       '::' rhs=unary_expression
       { $res = em.make_concat($res, rhs); }
    )*
	;

unary_expression returns [Expr_ptr res]
@init { res = NULL; }
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
@init { res = NULL; }
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
@init { res = NULL; }
	: id=identifier
      { $res = id; }

	| k=constant
      { $res = k; }

    /*
       README: follow recursive rule avoids a lot of code duplication
       in the grammar, however this relaxes the grammar to the point
       of allowing temporal operators in non-temporal expressions, and
       mixing CTL and LTL operators (bad). A proper check needs to be
       done at compilation time.
    */
	| '(' expr=temporal_formula ')'
      { $res = expr; }
	;

identifier returns [Expr_ptr res]
@init { res = NULL; }
	: IDENTIFIER
      { $res = em.make_identifier((const char*)($IDENTIFIER.text->chars)); }
	;

constant returns [Expr_ptr res]
@init { res = NULL; }
    :	k=enum_constant
        { $res = k; }

    |   k=range_constant
        { $res = k; }

    |   k=word_constant
        { $res = k; }
    ;

word_constant returns [Expr_ptr res]
@init { res = NULL; }
    : WORD_CONSTANT
      { $res = em.make_wconst((const char*)($WORD_CONSTANT.text->chars)); }
    ;

int_constant returns [Expr_ptr res]
@init { res = NULL; }
	: HEX_LITERAL
      {
        Atom tmp((const char*)($HEX_LITERAL.text->chars));
        $res = em.make_hex_const(tmp);
      }

    | OCTAL_LITERAL
      {
        Atom tmp((const char*)($OCTAL_LITERAL.text->chars));
        $res = em.make_oct_const(tmp);
      }

   	| DECIMAL_LITERAL
      {
        Atom tmp((const char*)($DECIMAL_LITERAL.text->chars));
        $res = em.make_dec_const(tmp);
      }
	;

range_constant returns [Expr_ptr res]
@init { res = NULL; }
	: lhs=int_constant
      { $res = lhs; }

      ('..' rhs=int_constant
      { $res = em.make_range(lhs, rhs); }
      )?
	;

enum_constant returns [Expr_ptr res]
@init { res = NULL; }

	: literals=enum_type
    { $res = em.make_enum(literals); }
    ;

/* lvalue is used in assignments */
lvalue returns [Expr_ptr res]
@init { res = NULL; }
	: 'init' '(' expr=postfix_expression ')'
      { $res = em.make_init(expr); }

	| 'next' '(' expr=postfix_expression ')'
      { $res = em.make_next(expr); }

	| expr=postfix_expression
      { $res = expr; }
	;

/* pvalue is used in param passing (actuals) */
pvalue returns [Expr_ptr res]
@init { res = NULL; }
	: 'next' '(' expr=postfix_expression ')'
      { $res = em.make_next(expr); }

	| expr=postfix_expression
      { $res = expr; }
	;

/* ordinary values used elsewhere */
value returns [Expr_ptr res]
@init { res = NULL; }
    : expr=postfix_expression
      { $res = expr; }
    ;

type_name returns [Type_ptr res]
@init { res = NULL; }
	: 'boolean'
    { $res = tm.find_boolean(); }

	| literals=enum_type
      { $res = tm.find_enum(literals); }

    | lhs=int_constant '..' rhs=int_constant
      { $res = tm.find_range(lhs, rhs); }

    | 'unsigned'? 'word' '[' k=int_constant ']'
      { $res = tm.find_uword(k); }

	| 'signed' 'word' '[' k=int_constant ']'
      { $res = tm.find_sword(k); }

    | id=identifier
      { $res = tm.find_instance(id); }  actual_param_decls[$res]
    ;

enum_type returns [EnumLiterals lits]
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
     '('
          ap=pvalue
            { ((Instance*)(m)) -> add_param(ap); }

          (',' pvalue
          { ((Instance*)(m)) -> add_param(ap); }
          )*
     ')'
    ;

literal returns [Expr_ptr res]
@init { res = NULL; }
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
