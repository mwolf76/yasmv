/**
   Copyright (C) 2010-2015 Marco Pensallorto

   This file is part of YASMINE.

   YASMINE is free software: you can redistribute it and/or modify it
   under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   YASMINE is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

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

#ifndef GRAMMAR_EXCEPTION
#define GRAMMAR_EXCEPTION
class GrammarException : public Exception {

    virtual const char* what() const throw()
    {
        std::ostringstream oss;
        oss
            << "Grammar exception: "
            << f_message
            << std::endl
            ;

        return (strdup(oss.str().c_str()));
    }

    std::string f_message;

public:
    GrammarException(const std::string &message)
        : f_message(message)
    {}

    virtual ~GrammarException() throw()
    {}
};
#endif
}

@members {
    /* singleton managers */
    ExprMgr& em
        (ExprMgr::INSTANCE());

    ModelMgr& mm
        (ModelMgr::INSTANCE());

    TypeMgr& tm
        (TypeMgr::INSTANCE());

    OptsMgr& om
        (OptsMgr::INSTANCE());

    CommandMgr& cm
        (CommandMgr::INSTANCE());

    /* the model instance */
    Model& model
        (mm.model());
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
    :   module_decl ( ';' module_decl )*
    ;

module_decl
scope {
    int hidden;
    int input;
    int frozen;
}
@init {
    $module_decl::hidden = 0;
    $module_decl::input = 0;
    $module_decl::frozen = 0;
}

    :   /* variables and defines */
        fsm_decl_modifiers (
            fsm_var_decl | fsm_define_decl
        )

        /* FSM definition */
    |   fsm_init_decl
    |   fsm_invar_decl
    |   fsm_trans_decl
    ;

fsm_decl_modifiers
    : ( '@'
            (
                'hidden' { $module_decl::hidden = 1; } |
                'frozen' { $module_decl::frozen = 1; } |
                'input'  { $module_decl::input  = 1; }
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
    ExprVector ev;
}
    : ids=identifiers[&ev] ':' tp=type
    {
            ExprVector::iterator expr_iter;
            assert(NULL != tp);
            for (expr_iter = ev.begin(); expr_iter != ev.end(); ++ expr_iter) {
                Expr_ptr vid (*expr_iter);
                Variable_ptr var
                    (new Variable($smv::current_module->name(), vid, tp));

                if ($module_decl::hidden)
                    var -> set_hidden(true);
                if ($module_decl::input)
                    var -> set_input(true);
                if ($module_decl::frozen)
                    var -> set_frozen(true);

                $smv::current_module->add_var(vid, var);
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


fsm_define_decl
    :
        'DEFINE' fsm_define_decl_body
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

      if ($module_decl::input)
          throw GrammarException("@input modifier not supported in DEFINE decls");
      if ($module_decl::frozen)
          throw GrammarException("@frozen modifier not supported in DEFINE decls");
      if ($module_decl::hidden)
          def -> set_hidden(true);

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
    : expr=logical_expression {
         $res = expr;
      }

      (
            '?' lhs=toplevel_expression ':' rhs=toplevel_expression
            { $res = em.make_ite( em.make_cond($res, lhs), rhs); }
      )?
    ;

logical_expression returns [Expr_ptr res]
    : expr=logical_implies_expression
      { $res = expr; }
    ;

logical_implies_expression returns [Expr_ptr res]
@init { }
    : lhs=logical_or_expression
      { $res = lhs; }

    (
      '->' rhs=logical_or_expression
      { $res = em.make_implies($res, rhs); }
    )*
    ;

logical_or_expression returns[Expr_ptr res]
@init { }
    : lhs=logical_and_expression
      { $res = lhs; }

    (
      '||' rhs=logical_and_expression
      { $res = em.make_or($res, rhs); }
    )*
    ;

logical_and_expression returns[Expr_ptr res]
@init { }
    : lhs=bw_or_expression
      { $res = lhs; }

    (
      '&&' rhs=bw_or_expression
      { $res = em.make_and($res, rhs); }
    )*
    ;

bw_or_expression returns[Expr_ptr res]
@init { }
    : lhs=bw_xor_expression
      { $res = lhs; }

    (
      '|' rhs=bw_xor_expression
       { $res = em.make_bw_or($res, rhs); }
    )*
    ;

bw_xor_expression returns[Expr_ptr res]
@init { }
    : lhs=bw_xnor_expression
      { $res = lhs; }

    (
      '^' rhs=bw_xnor_expression
      { $res = em.make_bw_xor($res, rhs); }
    )*
    ;

bw_xnor_expression returns[Expr_ptr res]
@init { }
    : lhs=bw_and_expression
      { $res = lhs; }

    (
      '~^' rhs=bw_and_expression
      { $res = em.make_bw_xnor($res, rhs); }
    )*
    ;

bw_and_expression returns[Expr_ptr res]
@init { }
    : lhs=temporal_expression
      { $res = lhs; }

    (
      '&' rhs=temporal_expression
      { $res = em.make_bw_and($res, rhs); }
    )*
    ;

temporal_expression returns [Expr_ptr res]
@init { }
    :
        expr=binary_ltl_expression
        { $res = expr; }
    ;

binary_ltl_expression returns [Expr_ptr res]
@init { }
    : lhs=unary_ltl_expression
      { $res = lhs; } (
            'U' rhs=unary_ltl_expression
            { $res = em.make_U($res, rhs); }

        |   'R' rhs=unary_ltl_expression
            { $res = em.make_R($res, rhs); }
    )*
    ;

unary_ltl_expression returns [Expr_ptr res]
@init { }
    : 'G' expr=unary_ltl_expression
      { $res = em.make_G(expr); }

    | 'F' expr=unary_ltl_expression
      { $res = em.make_F(expr); }

    | 'X' expr=unary_ltl_expression
      { $res = em.make_X(expr); }

    | expr=equality_expression
      { $res = expr; }
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

nondeterministic_expression returns[Expr_ptr res]
@init {
    ExprVector clauses;
}
    : '{'
          c=toplevel_expression{ clauses.push_back(c); }
            (',' c=toplevel_expression { clauses.push_back(c); })*
      '}'
      {
            ExprVector::reverse_iterator i
                (clauses.rbegin());

            while (clauses.rend() != i) {
                $res = $res ? em.make_set_comma( *i, $res) : *i;
                ++ i;
            }

            $res = em.make_set( $res );
        }
    ;

array_expression returns[Expr_ptr res]
@init {
    ExprVector clauses;
}
    : '['
          c=toplevel_expression{ clauses.push_back(c); }
            (',' c=toplevel_expression { clauses.push_back(c); })*
      ']'
      {
            ExprVector::reverse_iterator i
                (clauses.rbegin());

            while (clauses.rend() != i) {
                $res = $res ? em.make_array_comma( *i, $res) : *i;
                ++ i;
            }

            $res = em.make_array( $res );
        }
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
                res = (!res) ? expr : em.make_params_comma( expr, res );
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

    | expr=case_expression
      { $res = expr; }
    ;

case_expression returns [Expr_ptr res]
@init {
    typedef std::pair<Expr_ptr, Expr_ptr> CaseClause;
    typedef std::vector<CaseClause> CaseClauses;

    CaseClauses clauses;
}  : 'case'

     (lhs=toplevel_expression ':' rhs=toplevel_expression ';'
     { clauses.push_back( std::make_pair< Expr_ptr, Expr_ptr > (lhs, rhs)); }) +

     'else' ':' last=toplevel_expression ';'
     { clauses.push_back( std::make_pair< Expr_ptr, Expr_ptr > (NULL, last)); }

     'end'
     {
        CaseClauses::reverse_iterator i = clauses.rbegin();
        res = i -> second;
        while (1) {
            if ( ++ i == clauses.rend())
                break;
            $res = em.make_ite( em.make_cond(i -> first,
                                             i -> second), $res);
        }
     }
    ;

identifiers [ExprVector* ids]
    :
      ident=identifier
      { ids->push_back(ident); }

      ( ',' ident=identifier
            { ids->push_back(ident); }
      )*
    ;

expressions [ExprVector* exprs]
    :
      expr=toplevel_expression
      { exprs->push_back(expr); }

      ( ',' expr=toplevel_expression
            { exprs->push_back(expr); }
      )*
    ;

identifier returns [Expr_ptr res]
@init { }
    : IDENTIFIER
      { $res = em.make_identifier((const char*)($IDENTIFIER.text->chars)); }
    ;

constant returns [Expr_ptr res]
@init {
}
    : HEX_LITERAL {
        Atom tmp((const char*)($HEX_LITERAL.text->chars));
        $res = em.make_hex_const(tmp);
      }

    | x=DECIMAL_LITERAL {
        Atom tmp (Atom((const char*)($x.text->chars)));
        $res = em.make_dec_const(tmp);
      }

    | OCTAL_LITERAL {
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

/* typedecls */
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

    ;

boolean_type returns [Type_ptr res]
@init {
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
            (Type_ptr) tm.find_boolean_array(array_size) :
            (Type_ptr) tm.find_boolean();
    }
    ;

enum_type returns [Type_ptr res]
@init {
    int array_size = 0;
    ExprSet lits;
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
            (Type_ptr) tm.find_enum_array(lits, array_size) :
            (Type_ptr) tm.find_enum(lits);
    }
    ;

unsigned_int_type returns [Type_ptr res]
@init {
    int array_size = 0;
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
            {
                array_size = size->value();
                assert(0 < array_size);
            }
    ) ?
    {
        $res = array_size ?
            (Type_ptr) tm.find_unsigned_array(*p ? atoi(p)
                : OptsMgr::INSTANCE().word_width(), array_size) :
            (Type_ptr) tm.find_unsigned( *p ? atoi(p)
                : OptsMgr::INSTANCE().word_width());
    }

    ;

signed_int_type returns [Type_ptr res]
@init {
    int array_size = 0;
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
            {
                array_size = size->value();
                assert(0 < array_size);
            }
    ) ?
    {
        $res = array_size ?
            (Type_ptr) tm.find_signed_array(*p ? atoi(p)
                : OptsMgr::INSTANCE().word_width(), array_size) :
            (Type_ptr) tm.find_signed( *p ? atoi(p)
                : OptsMgr::INSTANCE().word_width());
    }

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
command_line returns [CommandVector_ptr res]
@init {
    res = new CommandVector();
}
    : commands[res]
    ;

commands [CommandVector_ptr cmds]
    :
        c=command
        { cmds->push_back(c); }

        (
            ';' c=command
            { cmds->push_back(c); }
        )*
    ;

command returns [Command_ptr res]
    :  c=help_command
       { $res = c; }

    |  c=time_command
       { $res = c; }

    |  c=read_model_command
       { $res = c; }

    |  c=write_model_command
       { $res = c; }

    |  c=pick_state_command
       { $res = c; }

    |  c=simulate_command
       { $res = c; }

    |  c=check_init_command
       { $res = c; }

    |  c=check_invar_command
       { $res = c; }

    |  c=list_traces_command
       { $res = c; }

    |  c=dump_trace_command
       { $res = c; }

    |  c=dup_trace_command
       { $res = c; }

    |  c=quit_command
       { $res = c; }
    ;

help_command returns [Command_ptr res]
    : 'help'
      { $res = cm.make_help(); }
      (
          topic = command
          { ((Help*) $res) -> set_topic(topic); }
      )?
    ;

time_command returns [Command_ptr res]
    : 'time'
      { $res = cm.make_time(); }
    ;

read_model_command returns [Command_ptr res]
    :  'read_model'
        { $res = cm.make_read_model(); }

        ( input=filepath {
            ((ReadModel*) $res) -> set_input(input);
        }) ?
    ;

write_model_command returns [Command_ptr res]
    :  'write_model'
        { $res = cm.make_write_model(); }

        ( output=filepath {
            ((WriteModel*) $res) -> set_output(output);
        }) ?
    ;

check_init_command returns[Command_ptr res]
    : 'check_init'
      { $res = cm.make_check_init(); }

      init=toplevel_expression
      { ((CheckInit *) $res) -> set_init(init); }
    ;

check_invar_command returns[Command_ptr res]
    : 'check_invar'
      { $res = cm.make_check_invar(); }

      invar=toplevel_expression
      { ((CheckInvar *) $res) -> set_invar(invar); }
    ;

list_traces_command returns [Command_ptr res]
    : 'list_traces'
      { $res = cm.make_list_traces(); }
    ;

dump_trace_command returns [Command_ptr res]
    : 'dump_trace'
      { $res = cm.make_dump_trace(); }

    (
      '-f' format=string
      { ((DumpTrace*) $res) -> set_format(format); }

    | '-o' output=filepath
      {
            ((DumpTrace*) $res) -> set_output(output);
            free((void *) output);
      }

    )*

    ( trace_id=string
    { ((DumpTrace*) $res) -> set_trace_id(trace_id); } )?

    ;

dup_trace_command returns [Command_ptr res]
    : 'dup_trace'
      { $res = cm.make_dup_trace(); }

      trace_id=string
      { ((DupTrace*) $res) -> set_trace_id(trace_id); }

      ( duplicate_uid=string
        { ((DupTrace*) $res) -> set_duplicate_id(duplicate_uid); } )?
    ;

pick_state_command returns [Command_ptr res]
    :   'pick_state'
        { $res = cm.make_pick_state(); }
    (
         '-i' init_condition=toplevel_expression
         { ((PickState*) $res) -> set_init_condition(init_condition); }

    |    '-t' trace_id=string
         { ((PickState*) $res) -> set_trace_uid(trace_id); }
    )*
    ;

simulate_command returns [Command_ptr res]
    : 'simulate'
      { $res = cm.make_simulate(); }
    (
       '-i' invar_condition=toplevel_expression
        { ((Simulate *) $res) -> set_invar_condition(invar_condition); }

    |  '-u' until_condition=toplevel_expression
        { ((Simulate*) $res) -> set_until_condition(until_condition); }

    |   '-k' konst=constant
        { ((Simulate*) $res) -> set_k(konst->value()); }

    |   '-t' trace_id=string
        { ((Simulate*) $res) -> set_trace_uid(trace_id); }
    )*
    ;

quit_command returns [Command_ptr res]
    :  'quit'
       { $res = cm.make_quit(); }
    ;

string returns [pconst_char res]
@init {}
    : IDENTIFIER
      { $res = (pconst_char) $IDENTIFIER.text -> chars; }
    ;

filepath returns [pconst_char res]
    : QUOTE
    { $res = (pconst_char) $QUOTE.text -> chars; }

    | dquote = DQUOTE
    { $res = (pconst_char) $DQUOTE.text -> chars; }
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

DQUOTE
    : '\'' ~'\''* '\''
    ;

QUOTE
    : '"' ~'"'* '"'
    ;

fragment TYPE_WIDTH
    : DECIMAL_LITERAL
    ;

fragment ID_FIRST_CHAR
    :   'A'..'Z' | 'a'..'z' | '_'
    ;

fragment FP_CHARS
    :   '/' | '.' | '..'
    ;

fragment ID_FOLLOWING_CHARS
    :    ID_FIRST_CHAR
    |    DECIMAL_DIGIT
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

fragment FRACTIONAL_DIGIT
    : ZERO | DECIMAL_DIGIT
    ;

WS
   : (' '|'\r'|'\t'|'\u000C'|'\n')
     { $channel=HIDDEN; }
   ;

LINE_COMMENT
   : ( '//' | '--' ) ~('\n'|'\r')* '\r'? '\n'
     { $channel=HIDDEN; }
   ;
