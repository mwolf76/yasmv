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
#include <expr.hh>
#include <model.hh>

// singleton managers
ExprMgr& em = ExprMgr::INSTANCE();
ModelMgr& mm = ModelMgr::INSTANCE();
}

/* Toplevel */
smv : modules // properties
;

/* properties */
// property_list
// 	: 	property ( ';'! property )
//     ;

// TODO PSLSPEC
// property
//   : ltl_spec
//   | ctl_spec
//   ;

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
// 	| ctl_cond_expression
// 	;
// ctl_case_expression
// 	: 'case'! ctl_case_clauses 'esac'!
// 	;

// ctl_case_clauses
// 	: ctl_case_clause (ite_operator^ ctl_case_clause)*
// 	;

// ctl_case_clause
// 	: (ctl_cond_expression column_operator ctl_cond_expression)
// 		=> ctl_cond_expression column_operator^ ctl_cond_expression
// 	| -> NIL
// 	;

// ctl_cond_expression
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
// 	| ltl_cond_expression
// 	;
// ltl_case_expression
// 	: 'case'! ltl_case_clauses 'esac'!
// 	;

// ltl_case_clauses
// 	: ltl_case_clause (ite_operator^ ltl_case_clause)*
// 	;

// ltl_case_clause
// 	: (ltl_cond_expression column_operator ltl_cond_expression)
// 		=> ltl_cond_expression column_operator^ ltl_cond_expression
// 	| -> NIL
// 	;

// ltl_cond_expression
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
scope {
    Module& module ;
}
@init {
    module = mm.nil();
}
	: ( 'MODULE' id=identifier
      { module = mm.new_module(id); }

      formal_params? fsm
      )*
    ;

formal_params
	:	'('
        id=identifier {
            $module.add_formalParam(id);
        }

        ( ',' id=identifier {
            $module.add_formalParam(id);
        })*
        ')'
    ;

// FSM definition entry point
fsm :	(fsm_formula)*
    ;

fsm_formula
    :	/* isa decls */
//        fsm_isa_decl_body

        /* variables and defines */
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
	;

/* ISA */
// fsm_isa_decl_body
// 	: fsm_isa_decl_clause +
// 	;

fsm_isa_decl_clause
	: 'ISA' id=identifier
       { $module.add_isa_decl(id); }
	;

/* VAR */
fsm_var_decl
    : 'VAR' fsm_var_decl_body
    ;

fsm_var_decl_body
	: fsm_var_decl_clause +
	;

fsm_var_decl_clause
	: id=identifier ':' type=type_name ';'
    { $module.add_state_var(id, type); }
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
    { $module.add_input_var(id, type) }
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
    { $module.add_frozen_var_(id, type); }
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
    { $module.add_def(id, body); }
	;

/* INIT */
fsm_init_decl
    : 'INIT' fsm_var_decl_body
    ;

fsm_init_decl_body
	: fsm_init_decl_clause +
	;

fsm_init_decl_clause
	: expr=untimed_expression ';'
      { $module.add_init(expr); }
	;


/* INVAR */
fsm_invar_decl
    : 'INVAR' fsm_var_decl_body
    ;

fsm_invar_decl_body
	: fsm_invar_decl_clause +
	;

fsm_invar_decl_clause
	: expr=untimed_expression ';'
      { $module.add_invar(expr); }
	;

/* TRANS */
fsm_trans_decl
    : 'TRANS' fsm_var_decl_body
    ;

fsm_trans_decl_body
	: fsm_trans_decl_clause +
	;

fsm_trans_decl_clause
	: expr=untimed_expression ';'
      { $module.add_trans(expr); }
	;

/* FAIRN */
fsm_fairn_decl
    : 'FAIRNESS' fsm_var_decl_body
    ;

fsm_fairn_decl_body
	: fsm_fairn_decl_clause +
	;

fsm_fairn_decl_clause
	: expr=untimed_expression ';'
      { $module.add_fairness(expr); }
	;


/* functional FSM definition */
assignment_formula
	: 	'ASSIGN' assignment_body
	;

assignment_body
	: assignment_clause +
	;

assignment_clause
	: lvalue ':=' expr=untimed_expression ';'
        { $module.add_assign(lvalue, expr); }
	;

// argument_expression_list
// 	:   untimed_expression (','! untimed_expression)*
// 	;

untimed_expression returns [Expr& expr]
	: case_expression
	| cond_expression
	;

// predicates
case_expression returns [Expr& expr]
	: 'case' case_clauses 'esac'
    { expr = $case_clauses; }
	;

case_clauses
scope {

}
	: cl=case_clause (';' case_clause)*
	;

case_clause returns [Expr& res]
	: (cond=untimed_expression ':' then=untimed_expression)
    { expr = Expr_em.make_cond(cond, then); }
	;

cond_expression returns [Expr& res]
	: expr=iff_expression (
        '?' then=iff_expression ':' else=iff_expression
        { $res = make_ite(expr, then, else); }

    | { $res = expr; } )

	;

iff_expression returns [Expr& res]
	:  lhs=imply_expression (
            '<->' rhs=iff_expression
            { $res = em.make_iff(lhs, rhs); }

    |       { $res = lhs; } )
	;

imply_expression returns [Expr& res]
	: lhs=inclusive_or_expression (
            '->' rhs=imply_expression
            { $res = em.make_implies(lhs, rhs); }

    |      { lhs = $res; } )

	;

inclusive_or_expression returns [Expr& res]
	: lhs=exclusive_or_expression (
            '|' rhs=inclusive_or_expression
            { $res = em.make_or(lhs, rhs); }

    |       { $res = lhs; } )

	;

exclusive_or_expression returns [Expr& res]
	: lhs=and_expression (
            'xor' rhs=exclusive_or_expression
            { $res = em.make_xor(lhs, rhs); }

        |  'xnor' rhs=exclusive_or_expression
            { $res = em.make_xnor(lhs, rhs); }

        |   { $res = lhs; } )
	;

and_expression returns [Expr& res]
	: lhs=equality_expression (
            '&' rhs=equality_expression
            { $res = em.make_and(lhs, rhs); }

    |       { $res = lhs; } )
	;

equality_expression returns [Expr& res]
	: lhs=relational_expression (
            '=' rhs=equality_expression
            { $res = em.make_eq(lhs, rhs); }

    |       '!=' rhs=equality_expression
            { $res = em.make_ne(lhs, rhs); }

    |       { $res = lhs; } )

	;

relational_expression returns [Expr& res]
	: lhs=shift_expression (
            '<' rhs=relational_expression
            { $res = em.make_lt(lhs, rhs); }

    |       '<=' rhs=relational_expression
            { $res = em.make_le(lhs, rhs); }

    |       '>=' rhs=relational_expression
            { $res = em.make_ge(lhs, rhs); }

    |       '>' rhs=relational_expression
            { $res = em.make_gt(lhs, rhs); }

    |       { $res = lhs; } )

	;

shift_expression returns [Expr& res]
	: lhs=additive_expression (
            '<<' rhs=shift_expression
            { $res = em.make_lshift(lhs, rhs); }

    |       '>>' rhs=shift_expression
            { $res = em.make_rshift(lhs, rhs); }

    |       { $res = lhs; } )
	;

additive_expression returns [Expr& res]
	: lhs=multiplicative_expression (
            '+' rhs=additive_expression
            { $res = em.make_add(lhs, rhs); }

    |       '-' rhs=additive_expression
            { $res = em.make_sub(lhs, rhs); }

    |       { $res = lhs; } )
	;

multiplicative_expression returns [Expr& res]
	: lhs=unary_expression (
            '*' rhs=multiplicative_expression
            { $res = em.make_mul(lhs, rhs); }

    |       '/' rhs=multiplicative_expression
            { $res = em.make_div(lhs, rhs); }

    |       'mod' rhs=multiplicative_expression
            { $res = em.make_mod(lhs, rhs); }

    |       { $res = lhs; } )
	;

unary_expression returns [Expr& res]
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

postfix_expression returns [Expr& res]
	:   lhs=primary_expression (

            '[' rhs=primary_expression ']'
            { $res = make_subscript(lhs, rhs); }
        |

            '.' rhs=primary_expression
            { $res = make_dot(lhs, rhs); }

        |   { $res = lhs; } )

	;

primary_expression returns [Expr& res]
	: id=identifier
      { $res = id; }

	| k=constant
      { $res = k; }

	| '(' expr=untimed_expression ')'
      { $res = expr; }

	;

identifier returns [Expr& res]
	: IDENTIFIER
    {
        Atom tmp((const char*)($IDENTIFIER.text->chars));
        $res = em.make_identifier(tmp);
    }
	;

constant returns [Expr& res]
    :	enum_constant
    |   range_constant
    ;

int_constant returns [Expr& res]
	:   HEX_LITERAL
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

range_constant returns [Expr& res]
	:	lhs=int_constant (
			'..' rhs=int_constant
            { $res = make_range(lhs, rhs); }

    |   { $res = lhs; } )

	;

enum_constant returns [Expr& res]
	:	 enum_type;

/* lvalue is used in assignments */
lvalue returns [Expr& res]
	:	'init' '(' expr=postfix_expression ')'
        { $res = make_init(lhs); }

	|	'next' '(' expr=postfix_expression ')'
        { $res = make_next(lhs); }

	|	expr=postfix_expression
        { $res = expr; }
	;

/* pvalue is used in param passing (actuals) */
pvalue returns [Expr& res]
	:	'next' '(' expr=postfix_expression ')'
        { $res = em.make_next(expr) }

	|	expr=postfix_expression
        { $res = expr; }
	;

/* ordinary values used elsewhere */
value returns [Expr& res]
    :   expr=postfix_expression
        { $res = expr; }
    ;

type_name returns [IVarType_ptr res]
	: 'boolean'
    { $res = type_register.find_boolean(); }

	| enum_type

    | lhs=int_constant '..' rhs=int_constant
      { $res = new RangeType(lhs, rhs); }

	| word_type

    | id=identifier
      { $res = type_register.find_instance(id); }

      actual_param_decls[$res]
    ;

actual_param_decls [IVarType_ptr type_]
scope {
    Exprs formalParams;
    Instance module;
}

@init {
    module = dynamic_cast<Instance*> ($type_);
}
	:
        '(' ap=pvalue {
            module.addParam(ap);
        }
        (',' pvalue {
                module.addParam(ap);
        })*
        ')'
    ;

enum_type
scope {
    Literals literals;
}
	:	'{' lit=literal {
            Literal literal(const char *)($lit.text->chars);
            literals.addLiteral(lit);
        }

        (',' lit=literal {
            Literal literal(const char *)($lit.text->chars);
            literals.addLiteral(lit);
        })*
        '}'
	;

word_type returns [IVarType_ptr res]
	:	'unsigned'? 'word' '[' k=int_constant ']'
        {
         $res = new UnsignedWordType(k);
        }

	|	'signed' 'word' '[' k=int_constant ']'
        {
         $res = new SignedWordType(k)
        }
	;

literal
    :  identifier
    |  int_constant
    ;

/** Lexer rules */
IDENTIFIER
	:	LETTER (LETTER|'0'..'9')*
	;

fragment
LETTER
	:	'A'..'Z' | 'a'..'z' | '_'|'-'
	;

HEX_LITERAL
    : '0' ('x'|'X') HexDigit+
    ;

DECIMAL_LITERAL
    : ('0' | '1'..'9' '0'..'9'*)
    ;

OCTAL_LITERAL
    : '0' ('0'..'7')+
    ;

fragment
Exponent
    : ('e'|'E') ('+'|'-')? ('0'..'9')+ ;

fragment
HexDigit
    : ('0'..'9'|'a'..'f'|'A'..'F') ;

WS  : (' '|'\r'|'\t'|'\u000C'|'\n') {
    $channel=HIDDEN;
} ;

LINE_COMMENT : '--' ~('\n'|'\r')* '\r'? '\n' {
    $channel=HIDDEN;
} ;
