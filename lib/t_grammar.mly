/* ocamlyacc grammar for the target language T. */

%{
open T_ast

(* Recover (function name, parameter name) from an [f(x)] header, or fail. *)
let def_header (head : sexpr) : string * string =
  match head with
  | SApp (name, SVar param) -> (name, param)
  | _ -> raise (Parse_error "malformed function definition header")
%}

%token <int> INT
%token <string> IDENT
%token LET IN IFZ THEN ELSE
%token LPAREN RPAREN MINUS STAR EQUALS SEMI EOF

%start program
%start expr_only
%type <T_ast.sprogram> program
%type <T_ast.sexpr> expr_only

%%

program:
  | items EOF { $1 }

items:
  | expr { { defs = []; main = $1 } }
  | expr EQUALS expr SEMI items
      { let name, param = def_header $1 in
        let rest = $5 in
        { rest with defs = { name; param; body = $3 } :: rest.defs } }

expr:
  | LET IDENT EQUALS expr IN expr { SLet ($2, $4, $6) }
  | IFZ expr THEN expr ELSE expr { SIfz ($2, $4, $6) }
  | add { $1 }

add:
  | add MINUS mul { SSub ($1, $3) }
  | mul { $1 }

mul:
  | mul STAR atom { SMul ($1, $3) }
  | atom { $1 }

atom:
  | INT { SInt $1 }
  | IDENT { SVar $1 }
  | IDENT LPAREN expr RPAREN { SApp ($1, $3) }
  | LPAREN expr RPAREN { $2 }

expr_only:
  | expr EOF { $1 }
