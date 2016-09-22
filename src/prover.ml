(** Parse a string. *)
let parse s =
  let lexbuf = Lexing.from_string s in
  try
    Parser.decls Lexer.token lexbuf
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

(** Interactive loop. *)
let loop env =
  (* Current environment. *)
  let env = ref env in
  let ps = ref None in
  while true do
    try
      print_string "=^.^= ";
      let s = read_line () in
      if s = "exit" then
        exit 0
      else if s = "env" then
        print_endline ("\n" ^ Lang.Env.to_string (List.rev !env))
      else
        env := Lang.exec !env (parse s)
    with
    | End_of_file -> exit 0
    | Failure e -> print_endline ("Error: " ^ e ^ ".")
    | e -> print_endline ("Error: " ^ Printexc.to_string e)
  done
