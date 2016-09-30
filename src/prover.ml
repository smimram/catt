(** Interaction with user. *)

open Lang
open LangExt
open Common

(** Parse a string. *)
let parse s =
  let lexbuf = Lexing.from_string s in
  try
    Parser.prog Lexer.token lexbuf
  with
  | Failure s when s = "lexing: empty token" ->
     let pos = Lexing.lexeme_end_p lexbuf in
     Common.error
       "lexing error in file %s at line %d, character %d"
       pos.Lexing.pos_fname
       pos.Lexing.pos_lnum
       (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
  | Parsing.Parse_error ->
     let pos = (Lexing.lexeme_end_p lexbuf) in
     Common.error
       "parsing error in file %s at word \"%s\", line %d, character %d"
       pos.Lexing.pos_fname
       (Lexing.lexeme lexbuf)
       pos.Lexing.pos_lnum
       (pos.Lexing.pos_cnum - pos.Lexing.pos_bol - 1)

let init () =
  print_string "=^.^= "

let exec envs s =
  try
    if s = "exit" then
      exit 0
    else if s = "build" then
      let s = read_line () in
      let ps = Parser.ps Lexer.token (Lexing.from_string s) in
      PS.check ps;
      let ps = Subst.of_ps ps in
      let ps = ref ps in
      let loop = ref true in
      while !loop do
        print_string "=^o^= ";
        let s = read_line () in
        let ss = Subst.match_app (fst envs) !ps (mk (Var (VIdent s))) in
        print_endline ("len: "^string_of_int (List.length ss))
      done;
      envs
    else
      Lang.exec envs (parse s)
  with
  | End_of_file -> print_newline () ; exit 0
  | Failure e -> print_endline ("Error: " ^ e ^ "."); envs
  | e -> print_endline ("Error: " ^ Printexc.to_string e); envs


(** Interactive loop. *)
let loop envs =
  (* Current environment. *)
  let envs = ref envs in
  while true do
    init ();
    let s = read_line () in
    envs := exec !envs s
  done
