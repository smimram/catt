%{
    open Lang

    let rec abs args e =
      match args with
      | (x,t)::args -> Abs(x, t, abs args e)
      | [] -> e
%}

%token COH LET SET ARR ARROW OBJ TYPE
%token LPAR RPAR COL EQ US
%token <string> IDENT
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
    | COH var args COL expr { Coh ($2,$3,$5) }
    | SET IDENT EQ IDENT { Set ($2,$4) }
    | CHECK expr { Check $2 }
    | EVAL expr { Eval $2 }
    | ENV { Env }

var:
    | IDENT { VIdent $1 }

args:
    | LPAR var COL expr RPAR args { ($2,$4)::$6 }
    | var args { ($1,fresh_evar ())::$2 }
    | { [] }

ps:
    | args { $1 }

simple_expr:
    | LPAR expr RPAR { $2 }
    | var { Var $1 }
    | TYPE { Type }
    | OBJ { Obj }
    | US { fresh_evar () }

app_expr:
    | app_expr simple_expr { App ($1,$2) }
    | simple_expr { $1 }

expr:
    | app_expr { $1 }
    | expr ARR expr { Arr (fresh_evar (),$1,$3) }
