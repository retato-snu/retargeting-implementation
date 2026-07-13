/* ocamlyacc grammar for the target language T.

   It builds the label-less surface AST defined in T_ast; identifier resolution,
   function-id assignment, and fresh-label assignment are performed by the
   wrapper module T_parser, not here, keeping the grammar actions pure.

   A definition and the main expression both begin with an expression, so the
   program is left-factored on a leading [expr]: a following '=' commits it to a
   definition header (and the leading expression must be an application of a
   function name to a single bare-identifier parameter, recovered in the action);
   otherwise the expression is the main expression. This keeps the grammar LR(1)
   without any token-level lookahead. */

%{
open T_ast

(* A definition header is a leading [expr] of the shape [f(x)], [f(x, y)], or
   [f(x, y, z)] — an application of a function name to one, two, or three bare
   identifiers (the formal parameters). Recover (function name, parameter names)
   or fail. *)
let def_header (head : sexpr) : string * string list =
  let as_param = function
    | SVar p -> p
    | _ -> raise (Parse_error "function parameters must be plain identifiers")
  in
  match head with
  | SApp (name, p) -> (name, [ as_param p ])
  | SApp2 (name, p1, p2) -> (name, [ as_param p1; as_param p2 ])
  | SApp3 (name, p1, p2, p3) ->
      (name, [ as_param p1; as_param p2; as_param p3 ])
  | _ -> raise (Parse_error "malformed function definition header")
%}

%token <int> INT
%token <string> IDENT
%token LET IN IFZ THEN ELSE
%token LPAREN RPAREN PLUS MINUS STAR SLASH PERCENT LT EQUALS COMMA SEMI EOF

%start program
%start expr_only
%type <T_ast.sprogram> program
%type <T_ast.sexpr> expr_only

%%

program:
  | items EOF { $1 }

/* A program is zero or more definitions followed by the main expression. Each
   item begins with an [expr]; a trailing '= expr ;' makes it a definition,
   otherwise it is the (final) main expression. */
items:
  | expr { { defs = []; main = $1 } }
  | expr EQUALS expr SEMI items
      { let name, params = def_header $1 in
        let rest = $5 in
        { rest with defs = { name; params; body = $3 } :: rest.defs } }

/* Loosest level: let / ifz extend as far right as possible by recursing into
   [expr] for their bodies; otherwise the comparison level.

   Arithmetic precedence, loosest to tightest (all left-associative):
     '<' (comparison, SLt) < '+' '-' (SAdd/SSub) < '*' '/' '%' (SMul/SDiv/SMod).
   So 'a - b < c * d' parses as '(a - b) < (c * d)', 'x / 2 % 3' as '(x/2)%3',
   and '/' / '%' bind like '*' (one tier tighter than '+' / '-'). */
expr:
  | LET IDENT EQUALS expr IN expr { SLet ($2, $4, $6) }
  | IFZ expr THEN expr ELSE expr { SIfz ($2, $4, $6) }
  | cmp { $1 }

/* Comparison: left-associative chains of '<', the loosest arithmetic tier. */
cmp:
  | cmp LT add { SLt ($1, $3) }
  | add { $1 }

/* Additive: left-associative chains of '+' and '-'. */
add:
  | add PLUS mul { SAdd ($1, $3) }
  | add MINUS mul { SSub ($1, $3) }
  | mul { $1 }

/* Multiplication / division / remainder: left-associative, binding tighter than
   '-'. '*' is SMul, '/' is SDiv, '%' is SMod. */
mul:
  | mul STAR atom { SMul ($1, $3) }
  | mul SLASH atom { SDiv ($1, $3) }
  | mul PERCENT atom { SMod ($1, $3) }
  | atom { $1 }

atom:
  | INT { SInt $1 }
  | IDENT { SVar $1 }
  | IDENT LPAREN expr RPAREN { SApp ($1, $3) }
  | IDENT LPAREN expr COMMA expr RPAREN { SApp2 ($1, $3, $5) }
  | IDENT LPAREN expr COMMA expr COMMA expr RPAREN { SApp3 ($1, $3, $5, $7) }
  | LPAREN expr RPAREN { $2 }

/* Entry point for parsing a single expression (no definitions, no main). */
expr_only:
  | expr EOF { $1 }
