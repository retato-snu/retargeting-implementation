/* ocamlyacc grammar for the source language S.

   It builds the permissive surface AST (defined in the header): expressions may
   nest freely in operand positions, and the distinction between primitive head,
   declared-function call, and constructor application is left to the wrapper's
   A-normalizer (S_parser), not resolved here. The grammar actions stay pure. */

%{
open S_ast
%}

%token <int> INT
%token <string> IDENT
%token <string> CTOR
%token LET IN MATCH WITH END RETURN DEF MAIN
%token LPAREN RPAREN COMMA BAR ARROW EQUALS SEMI EOF

%start program
%start cmd_only
%type <S_ast.program> program
%type <S_ast.cmd> cmd_only

%%

program:
  | fundefs MAIN EQUALS cmd EOF { { funs = $1; main = $4 } }

/* A possibly-empty run of definitions, in source order. */
fundefs:
  | /* empty */ { [] }
  | fundef fundefs { $1 :: $2 }

fundef:
  | DEF IDENT LPAREN params RPAREN EQUALS cmd SEMI
      { { name = $2; params = $4; body = $7 } }

/* A possibly-empty, comma-separated list of parameter binders. */
params:
  | /* empty */ { [] }
  | param_list { $1 }

param_list:
  | IDENT { [ $1 ] }
  | IDENT COMMA param_list { $1 :: $3 }

cmd:
  | RETURN expr { Return $2 }
  | LET IDENT EQUALS expr IN cmd { Let ($2, $4, $6) }
  | MATCH IDENT WITH branches END { Match ($2, $4) }

/* Zero or more '| pat -> cmd' branches, in source order. */
branches:
  | /* empty */ { [] }
  | BAR pat ARROW cmd branches { ($2, $4) :: $5 }

/* A pattern is a capitalized constructor applied to a parenthesized list of
   field binders (identifiers), possibly empty. */
pat:
  | CTOR LPAREN binders RPAREN { ($1, $3) }

binders:
  | /* empty */ { [] }
  | binder_list { $1 }

binder_list:
  | IDENT { [ $1 ] }
  | IDENT COMMA binder_list { $1 :: $3 }

/* Expressions may nest freely in operand positions. A lowercase head followed
   by '(' is an application (primitive or call, disambiguated by the wrapper);
   without arguments it is a variable. A capitalized head must be applied (a
   nullary constructor is written Nil()). */
expr:
  | INT { Int $1 }
  | IDENT { Var $1 }
  | IDENT LPAREN args RPAREN { App ($1, $3) }
  | CTOR LPAREN args RPAREN { App ($1, $3) }
  | LPAREN expr RPAREN { $2 }

/* A possibly-empty, comma-separated argument list. */
args:
  | /* empty */ { [] }
  | arg_list { $1 }

arg_list:
  | expr { [ $1 ] }
  | expr COMMA arg_list { $1 :: $3 }

/* Entry point for parsing a single command (no definitions, no 'main ='). */
cmd_only:
  | cmd EOF { $1 }
