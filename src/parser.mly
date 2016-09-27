%{
    open Lang

    let rec abs args e =
      match args with
      | (x,t)::args -> Abs(x, t, abs args e)
      | [] -> e
%}

%token COH LET SET ARR ARROW OBJ
%token LPAR RPAR COL EQ US
%token <string> IDENT
%token CHECK EVAL HYP
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
    | LET IDENT args EQ expr { Decl ($2,abs $3 $5) }
    | HYP IDENT COL expr { Axiom ($2,$4) }
    | SET IDENT EQ IDENT { Set ($2,$4) }
    | CHECK expr { Check $2 }
    | EVAL expr { Eval $2 }

args:
    | LPAR IDENT COL expr RPAR args { ($2,$4)::$6 }
    | { [] }

ps:
    | args { $1 }

simple_expr:
    | LPAR expr RPAR { $2 }
    | IDENT { Var $1 }
    | OBJ { Obj }
    | US { fresh_evar () }

app_expr:
    | app_expr simple_expr { App ($1,$2) }
    | simple_expr { $1 }

expr:
    | app_expr { $1 }
    | expr ARR expr { Arr ($1,$3) }
    | COH args ARROW expr { Coh ($2,$4) }
