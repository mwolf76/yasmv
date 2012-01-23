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
	k = 1; /* LL(1) grammar with a few exceptions */
	memoize = true;
    language = C;
}

@members {
#include <common.hh>
#include <model.hh>

Model model;
}

/* Toplevel */
model [IModel_ptr model]:
        modules[$model] properties
	;

/* properties */
property_list
	: 	property ( ';'! property )
    ;

// TODO PSLSPEC
property
  : ltl_spec
  | ctl_spec
  ;

/** CTL properties */
// ctl_spec:	('CTLSPEC' | 'SPEC') formula=ctl_formula -> ^(CTLSPEC $formula)
// 	;

// ctl_formula
// 	:	binary_ctl_formula;

// binary_ctl_formula
// 	:	unary_ctl_formula (
// 			binary_ctl_operator^ unary_ctl_formula
// 		)*
// 	;

// binary_ctl_operator
// 	:	'AU' -> AU
// 	|	'EU' -> EU
// 	|	'AR' -> AR
// 	|	'ER' -> ER
// 	;

// unary_ctl_formula
// 	:	'AG' formula=unary_ctl_formula -> ^(AG $formula)
// 	|	'EG' formula=unary_ctl_formula -> ^(AG $formula)
// 	|	'AF' formula=unary_ctl_formula -> ^(AF $formula)
// 	|	'EF' formula=unary_ctl_formula -> ^(EF $formula)
// 	|	next_ctl_formula
// 	;

// next_ctl_formula
// 	:	'AX' formula=ctl_untimed_expression -> ^(AX $formula)
// 	|	'EX' formula=ctl_untimed_expression -> ^(EX $formula)
// 	|	ctl_untimed_expression
// 	;

// ctl_untimed_expression
// 	: ctl_case_expression
// 	| ctl_conditional_expression
// 	;
// ctl_case_expression
// 	: 'case'! ctl_case_clauses 'esac'!
// 	;

// ctl_case_clauses
// 	: ctl_case_clause (ite_operator^ ctl_case_clause)*
// 	;

// ctl_case_clause
// 	: (ctl_conditional_expression column_operator ctl_conditional_expression)
// 		=> ctl_conditional_expression column_operator^ ctl_conditional_expression
// 	| -> NIL
// 	;

// ctl_conditional_expression
// 	: ctl_iff_expression ('?' ctl_iff_expression ':' ctl_iff_expression)?
// 	;

// ctl_iff_expression
// 	:  ctl_imply_expression (iff_operator^ ctl_imply_expression)*
// 	;

// ctl_imply_expression
// 	: ctl_inclusive_or_expression (imply_operator^ ctl_inclusive_or_expression)*
// 	;

// ctl_inclusive_or_expression
// 	: ctl_exclusive_or_expression ( inclusive_or_operator^ ctl_exclusive_or_expression)*
// 	;

// ctl_exclusive_or_expression
// 	: ctl_and_expression (exclusive_or_operator^ ctl_and_expression)*
// 	;

// ctl_and_expression
// 	: ctl_equality_expression (and_operator^ ctl_equality_expression)*
// 	;

// ctl_equality_expression
// 	: ctl_relational_expression (equality_operator^ ctl_relational_expression)*
// 	;

// ctl_relational_expression
// 	: ctl_shift_expression (relational_operator^ ctl_shift_expression)*
// 	;

// ctl_shift_expression
// 	: ctl_additive_expression (shift_operator^ ctl_additive_expression)*
// 	;

// // arithmetic
// ctl_additive_expression
// 	: ctl_multiplicative_expression (additive_operator^ ctl_multiplicative_expression)*
// 	;

// ctl_multiplicative_expression
// 	: ctl_cast_expression (multiplicative_operator^ ctl_cast_expression)*
// 	;

// ctl_cast_expression
// 	: boolean_type^ '('! ctl_cast_expression ')'!
// 	| ctl_unary_expression
// 	;

// ctl_unary_expression
// 	: ctl_postfix_expression
// 	| 'next' '(' expr=ctl_postfix_expression ')' -> ^(NEXT $expr)
// 	| '!' expr=ctl_postfix_expression	     -> ^(NOT $expr)
// 	;

// ctl_postfix_expression : ctl_subscript_expression;

// ctl_subscript_expression
// 	:   ctl_primary_expression (
// 		subscript_operator^ ctl_primary_expression ']'! |
// 		dot_operator^ ctl_primary_expression )*
// 	;

// ctl_primary_expression
// 	: identifier
// 	| constant
// 	| '(' expr=ctl_formula ')' -> $expr
// 	;

// /** LTL properties */
// ltl_spec:	'LTLSPEC' formula=ltl_formula -> ^(LTLSPEC $formula)
// 	;

// ltl_formula
// 	:	binary_ltl_formula;

// binary_ltl_formula
// 	:	unary_ltl_formula (
// 			binary_ltl_operator^ unary_ltl_formula
// 		)*
// 	;

// binary_ltl_operator
// 	:	'U' -> U
// 	|	'R' -> R
// 	;

// unary_ltl_formula
// 	:	'G' formula=unary_ltl_formula -> ^(G $formula)
// 	|	'F' formula=unary_ltl_formula -> ^(F $formula)
// 	|	next_ltl_formula
// 	;

// next_ltl_formula
// 	:	'X' formula=ltl_untimed_expression -> ^(X $formula)
// 	|	ltl_untimed_expression
// 	;

// ltl_untimed_expression
// 	: ltl_case_expression
// 	| ltl_conditional_expression
// 	;
// ltl_case_expression
// 	: 'case'! ltl_case_clauses 'esac'!
// 	;

// ltl_case_clauses
// 	: ltl_case_clause (ite_operator^ ltl_case_clause)*
// 	;

// ltl_case_clause
// 	: (ltl_conditional_expression column_operator ltl_conditional_expression)
// 		=> ltl_conditional_expression column_operator^ ltl_conditional_expression
// 	| -> NIL
// 	;

// ltl_conditional_expression
// 	: ltl_iff_expression ('?' ltl_iff_expression ':' ltl_iff_expression)?
// 	;

// ltl_iff_expression
// 	:  ltl_imply_expression (iff_operator^ ltl_imply_expression)*
// 	;

// ltl_imply_expression
// 	: ltl_inclusive_or_expression (imply_operator^ ltl_inclusive_or_expression)*
// 	;

// ltl_inclusive_or_expression
// 	: ltl_exclusive_or_expression ( inclusive_or_operator^ ltl_exclusive_or_expression)*
// 	;

// ltl_exclusive_or_expression
// 	: ltl_and_expression (exclusive_or_operator^ ltl_and_expression)*
// 	;

// ltl_and_expression
// 	: ltl_equality_expression (and_operator^ ltl_equality_expression)*
// 	;

// ltl_equality_expression
// 	: ltl_relational_expression (equality_operator^ ltl_relational_expression)*
// 	;

// ltl_relational_expression
// 	: ltl_shift_expression (relational_operator^ ltl_shift_expression)*
// 	;

// ltl_shift_expression
// 	: ltl_additive_expression (shift_operator^ ltl_additive_expression)*
// 	;

// // arithmetic
// ltl_additive_expression
// 	: ltl_multiplicative_expression (additive_operator^ ltl_multiplicative_expression)*
// 	;

// ltl_multiplicative_expression
// 	: ltl_cast_expression (multiplicative_operator^ ltl_cast_expression)*
// 	;

// ltl_cast_expression
// 	: boolean_type^ '('! ltl_cast_expression ')'!
// 	| ltl_unary_expression
// 	;

// ltl_unary_expression
// 	: ltl_postfix_expression
// 	| 'next' '(' expr=ltl_postfix_expression ')' -> ^(NEXT $expr)
// 	| '!' expr=ltl_postfix_expression	     -> ^(NOT $expr)
// 	;

// ltl_postfix_expression : ltl_subscript_expression;

// ltl_subscript_expression
// 	:   ltl_primary_expression (
// 		subscript_operator^ ltl_primary_expression ']'! |
// 		dot_operator^ ltl_primary_expression )*
// 	;

// ltl_primary_expression
// 	: identifier
// 	| constant
// 	| '(' expr=ltl_formula ')' -> $expr
// 	;

modules
	:	(module { model += $module; })+
	;

module returns [IModule_ptr res]
    :	'MODULE' id=identifier
    {
     string module_name((const char *)($id.text->chars));
     res = new Module(module_name);
    }

    formal_params[res]
    fsm[res]
    ;

properties
	:	(property { model += $property; })+
	;

formal_params[IModule_ptr module]
	:	'('
        id=identifier {
            Atom param_name((const char *)($id.text->chars));
            $module += $param_name;
        }

        ( ',' id=identifier {
            Atom param_name((const char *)($id.text->chars));
            $module += $param_name;
        })*
        ')'
    ;

fsm[IModule_ptr module]
	:	(fsm_formula [ module ])+
    ;

fsm_formula[IModule_ptr module]
    :	/* isa decls */
        fsm_isa_decl_body[$module]

        /* variables and defines */
	|   fsm_var_decl[$module]
	|	fsm_ivar_decl[$module]
	|	fsm_frozenvar_decl[$module]
	|	fsm_define_decl[$module]

		/* relational FSM */
	|	fsm_init_decl[$module]
	|	fsm_invar_decl[$module]
	|	fsm_trans_decl[$module]
    |   fsm_fairn_decl[$module]

        /* functional FSM */
	|	assignment_formula[$module]
	;

/* ISA */
fsm_isa_decl_body[IModule_ptr module]
	: fsm_isa_decl_clause[$module] +
	;

fsm_isa_decl_clause[IModule_ptr module]
	: 'ISA' id=identifier
        {
            ISADeclaration isa((const char *)($id.text->chars));
            $module += isa;
        }
	;

/* VAR */
fsm_var_decl[IModule_ptr module]
    : 'VAR' fsm_var_decl_body[$module]
    ;

fsm_var_decl_body[IModule_ptr module]
	: fsm_var_decl_clause[$module] +
	;

fsm_var_decl_clause[IModule_ptr module]
	: id=identifier ':' type=type_name ';'
    {
     Atom var_name((const char *)($id.text->chars));
     $module += StateVar(var_name);
    }
	;


/* IVAR */
fsm_ivar_decl
    : 'IVAR' fsm_ivar_decl_body
    ;

fsm_ivar_decl_body
	: fsm_ivar_decl_clause+
	;

fsm_ivar_decl_clause
	: id=identifier ':' type=type_name ';'
    {
     Atom var_name((const char *)($id.text->chars));
     $module += IVar(var_name);
    }
	;

/* FROZENVAR */
fsm_frozenvar_decl
    : 'FROZENVAR' fsm_frozenvar_decl_body
    ;

fsm_frozenvar_decl_body
	: fsm_frozenvar_decl_clause+
	;

fsm_frozenvar_decl_clause
	: id=identifier ':' type=type_name ';'
    {
     Atom var_name((const char *)($id.text->chars));
     $module += IVar(var_name);
    }
	;


/* DEFINE */
fsm_define_decl
    : 'DEFINE' fsm_define_decl_body
    ;

fsm_define_decl_body
	: fsm_define_decl_clause+
	;

fsm_define_decl_clause
	: id=identifier ':=' body=untimed_expression ';'
    {
     Atom symb_name((const char *)($id.text->chars));
     $module += Define(symb_name, $body);
    }
	;

/* INIT */
fsm_init_decl[Module_ptr module]
    : 'INIT' fsm_var_decl_body[$module]
    ;

fsm_init_decl_body[Module_ptr module]
	: fsm_init_decl_clause[$module] +
	;

fsm_init_decl_clause[Module_ptr module]
	: expr=untimed_expression ';'
      { $module.add_init($expr); }
	;


/* INVAR */
fsm_invar_decl[Module_ptr module]
    : 'INVAR' fsm_var_decl_body[$module]
    ;

fsm_invar_decl_body[Module_ptr module]
	: fsm_invar_decl_clause[$module] +
	;

fsm_invar_decl_clause[Module_ptr module]
	: expr=untimed_expression ';'
      { $module.add_invar($expr); }
	;

/* TRANS */
fsm_trans_decl[Module_ptr module]
    : 'TRANS' fsm_var_decl_body[$module]
    ;

fsm_trans_decl_body[Module_ptr module]
	: fsm_trans_decl_clause[$module] +
	;

fsm_trans_decl_clause[Module_ptr module]
	: expr=untimed_expression ';'
      { $module.add_trans($expr); }
	;

/* FAIRN */
fsm_fairn_decl[Module_ptr expr]
    : 'FAIRNESS' fsm_var_decl_body[$module]
    ;

fsm_fairn_decl_body[Module_ptr expr]
	: fsm_fairn_decl_clause[$module] +
	;

fsm_fairn_decl_clause[Module_ptr expr]
	: expr=untimed_expression ';'
      { $module.add_fairness($expr); }
	;


/* functional FSM definition */
assignment_formula[Module_ptr module]
	: 	'ASSIGN' assignment_body[$module]
	;

assignment_body[Module_ptr module]
	: assignment_clause[$module] +
	;

assignment_clause[Module_ptr module]
	: lvalue ':=' expr=untimed_expression ';'
        { $module.add_assign($lvalue, $expr); }
	;

// argument_expression_list
// 	:   untimed_expression (','! untimed_expression)*
// 	;

untimed_expression returns [Expr& expr]
	: case_expression
	| conditional_expression
	;

// predicates
case_expression returns [Expr& expr]
	: 'case' $expr=case_clauses 'esac'
	;

case_clauses
scope {

}
	: cl=case_clause (';' case_clause)*
	;

case_clause returns [Expr& res]
	: (cond=untimed_expression ':' then=untimed_expression)
    { $expr = Expr_mgr.make_cond($cond, $then); }
	;

conditional_expression returns [Expr& res]
	: cond=iff_expression '?' then=iff_expression ':' else=iff_expression
      { $res = make_ite($cond, $then, $else); }

    | expr=iff_expression
      { $res = $expr; }

	;

iff_expression returns [Expr& res]
	:  imply_expression (iff_operator^ imply_expression)*
	;

iff_operator
	:	'<->' -> IFF
	;

imply_expression
	: inclusive_or_expression (imply_operator^ inclusive_or_expression)*
	;

imply_operator
	:	'->' -> IMPLIES
	;

inclusive_or_expression
	: exclusive_or_expression ( inclusive_or_operator^ exclusive_or_expression)*
	;

inclusive_or_operator
	:	'|' -> OR
	;

exclusive_or_expression
	: and_expression (exclusive_or_operator^ and_expression)*
	;

exclusive_or_operator
	:	'xor' -> XOR
	|	'xnor' -> XNOR
	;

and_expression
	: equality_expression (and_operator^ equality_expression)*
	;

and_operator
	: 	'&' -> AND
	;
equality_expression
	: relational_expression (equality_operator^ relational_expression)*
	;

equality_operator
	: 	'=' -> EQ
	| 	'!=' -> NE
	;

relational_expression
	: shift_expression (relational_operator^ shift_expression)*
	;

relational_operator
	: '<' -> LT
	| '<=' -> LE
	| '>=' -> GE
	| '>' -> GT
	;

shift_expression
	: additive_expression (shift_operator^ additive_expression)*
	;

shift_operator
	: '<<' -> LHS
	| '>>' -> RHS
	;

// arithmetic
additive_expression
	: multiplicative_expression (additive_operator^ multiplicative_expression)*
	;

additive_operator
	:	'+' -> PLUS
	| 	'-' -> MINUS
	;

multiplicative_expression
	: cast_expression (multiplicative_operator^ cast_expression)*
	;

multiplicative_operator
	: '*' -> TIMES
	| '/' -> DIVIDE
	| 'mod' -> MOD
	;

cast_expression
	: boolean_type^ '('! cast_expression ')'!
	| unary_expression
	;

unary_expression
	: postfix_expression
	| 'next' '(' expr=postfix_expression ')' -> ^(NEXT $expr)
	| '!' expr=postfix_expression -> ^(NOT $expr)
	;

postfix_expression : subscript_expression;

subscript_expression
	:   primary_expression (
		subscript_operator^ primary_expression ']'! |
		dot_operator^ primary_expression )*
	;

subscript_operator
	:	'[' -> SUBSCRIPT
	;

dot_operator
	:	'.' -> DOT
	;

primary_expression
	: identifier
	| constant
	| '(' expr=untimed_expression ')' -> $expr
	;

identifier returns [Atom_ptr res]
	: id=IDENTIFIER
    { res = new Atom((const char*)($id.text->chars)); }
	;

constant
    :	enum_constant
    |   range_constant
   // |	real_constant
    ;

int_constant
	:   hex_literal ->
		^(NUMBER hex_literal)
    	|   octal_literal ->
    		^(NUMBER octal_literal)
   	|   decimal_literal ->
   		^(NUMBER decimal_literal)
	;

real_constant
	:   (real_literal) => real_literal ->
		^(NUMBER real_literal)
	;

range_constant
	:	j=int_constant (
			'..' k=int_constant -> ^(RANGE $j $k)
			| -> $j )
	;

hex_literal
	:	HEX_LITERAL;

octal_literal
	:	OCTAL_LITERAL;

decimal_literal
	:	DECIMAL_LITERAL;

real_literal
	:       decimal_literal FLOATING_POINT_SUFFIX;

enum_constant
	:	 enum_type;

/* lvalue is used in assignments */
lvalue
	:	'init' '(' postfix_expression ')' -> ^(INIT postfix_expression)
	|	'next' '(' postfix_expression ')' -> ^(NEXT postfix_expression)
	|	postfix_expression
	;

/* pvalue is used in param passing (actuals) */
pvalue returns [Term_ptr res]
	:	'next' '(' expr=postfix_expression ')'
        { $res = term_mgr.make_next($expr) }

	|	expr=postfix_expression
        { $res = $expr; }
	;

/* ordinary values used elsewhere */
value returns [Term_ptr res]
    :   expr=postfix_expression
        { $res = $expr; }
    ;

type_name returns [IVarType_ptr res]
	: 'boolean'
    { $res = type_register.find_boolean(); }

	| enum_type
	| range_type
	| word_type

    | id=identifier
      {
       Atom module_name((const char *)($id.text->chars));
       $res = type_register.find_instance($module_name);
      }

      actual_param_decls[$res]
    ;

actual_param_decls [IVarType_ptr type_]
scope {
    FormalParameters formalParams();
    InstanceType_ptr module = dynamic_cast<InstanceType_ptr> ($type_);
}
	:
        '(' ap=pvalue {
            module += ap;
        }
        (',' pvalue {
                module += ap;
        })*
        ')'
    ;

enum_type
scope {
    Literals literals;
}
	:	'{' lit=literal {
            Literal literal(const char *)($lit.text->chars);
            literals += lit;
        }

        (',' lit=literal {
            Literal literal(const char *)($lit.text->chars);
            literals += lit;
        })*
        '}'
	;

word_type returns [IVarType_ptr res]
	:	'unsigned'? 'word' '[' k=int_constant ']'
        {
         $res = new UnsignedWordType($k);
        }

	|	'signed' 'word' '[' k=int_constant ']'
        {
         $res = new SignedWordType($k)
        }
	;

range_type returns[IVarType_ptr res]
	:	j=int_constant '..' k=int_constant
        { $res = new RangeType($j, $k); }

literal
    :  identifier
    |  int_constant
    ;

/* conditional separator */
column_operator
	:	':' -> COND;

// /** separators are all mapped to CONS */
// semi_operator
// 	:	';' -> CONS;

// comma_operator
// 	:	',' -> CONS;

/** Lexer rules */
IDENTIFIER
	:	LETTER (LETTER|'0'..'9')*
	;

fragment
LETTER
	:	'A'..'Z' | 'a'..'z' | '_'|'-'
	;

HEX_LITERAL : '0' ('x'|'X') HexDigit+ ;

DECIMAL_LITERAL : ('0' | '1'..'9' '0'..'9'*) ;

OCTAL_LITERAL : '0' ('0'..'7')+ ;

FLOATING_POINT_SUFFIX
    :   '.' ('0'..'9')* Exponent?
    ;

fragment
Exponent : ('e'|'E') ('+'|'-')? ('0'..'9')+ ;

fragment
HexDigit : ('0'..'9'|'a'..'f'|'A'..'F') ;


WS  :  (' '|'\r'|'\t'|'\u000C'|'\n') {$channel=HIDDEN;} ;

LINE_COMMENT : '--' ~('\n'|'\r')* '\r'? '\n' {$channel=HIDDEN;} ;
