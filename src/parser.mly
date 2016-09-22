%{
    open Lang

    let rec abs args e =
      match args with
      | (x,t)::args -> Abs(x, t, abs args e)
      | [] -> e
%}

%token COH LET SET ARR ARROW OBJ
%token LPAR RPAR COL EQ
%token <string> IDENT
%token EOF

%right ARR ARROW

%start decls
%type <Lang.prog> decls
%%

decls:
    | decl decls { $1::$2 }
    | EOF { [] }

decl:
    | LET IDENT args EQ expr { Decl ($2,abs $3 $5) }
    | SET IDENT EQ IDENT { Set ($2,$4) }

args:
    | LPAR IDENT COL expr RPAR args { ($2,$4)::$6 }
    | { [] }

simple_expr:
    | LPAR expr RPAR { $2 }
    | IDENT { Var $1 }
    | OBJ { Obj }

app_expr:
    | app_expr simple_expr { App ($1,$2) }
    | simple_expr { $1 }

expr:
    | app_expr { $1 }
    | expr ARR expr { Arr ($1,$3) }
    | COH args ARROW expr { Coh ($2,$4) }
