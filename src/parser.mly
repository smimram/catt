%{
    open Stdlib
    open Lang

    let defpos () = Parsing.symbol_start_pos (), Parsing.symbol_end_pos ()

    let mk ?pos e =
      let pos = Option.default (defpos ()) pos in
      mk ~pos e

    let rec abs ?pos args e =
      match args with
      | (x,t)::args -> mk ?pos (Abs(x,t,abs args e))
      | [] -> e

    let var_name = function
      | VIdent x -> x
      | _ -> assert false
%}

%token COH LET IN SET ARR ARROW OBJ TYPE HOMTYPE
%token LPAR RPAR LACC RACC COL EQ US
%token <string> IDENT STRING
%token CHECK EVAL HYP ENV
%token EOF

%right ARR ARROW

%start prog ps
%type <Lang.prog> prog
%type <Lang.PS.t> ps
%%

prog:
    | cmd prog { $1::$2 }
    | EOF { [] }

cmd:
    | LET var args EQ expr { Decl ($2,abs $3 $5) }
    | HYP var COL expr { Axiom ($2,$4) }
    | COH var args COL expr { Decl ($2,mk (Coh (var_name $2,PS.make $3,$5,0))) }
    | SET IDENT EQ IDENT { Set ($2,$4) }
    | CHECK expr { Check $2 }
    | EVAL expr { Eval $2 }
    | ENV { Env }

var:
    | IDENT { VIdent $1 }

args:
    | LPAR var COL expr RPAR args { ($2,$4)::$6 }
    | { [] }

ps:
    | args { PS.make $1 }

simple_expr:
    | LPAR expr RPAR { $2 }
    | var { mk (Var $1) }
    | TYPE { mk Type }
    | HOMTYPE { mk HomType }
    | OBJ { mk Obj }

app_expr:
    | app_expr simple_expr { mk (App ($1,$2)) }
    | simple_expr { $1 }

expr:
    | app_expr { $1 }
    | expr ARR expr { mk (Arr (mk Daimon,$1,$3)) }
//    | COH stringopt args COL simple_expr { mk (Coh ($2,PS.make $3,$5,0)) }
    | LET var EQ expr IN expr { $6 } // TODO....

stringopt:
    | STRING { $1 }
    | { "" }
