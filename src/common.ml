(** Position in source code. *)
module Pos = struct
  type t = Lexing.position * Lexing.position

  let dummy = Lexing.dummy_pos, Lexing.dummy_pos

  (** String representation of a position. *)
  let to_string ((p1,p2):t) =
    let l1 = p1.Lexing.pos_lnum in
    let l2 = p2.Lexing.pos_lnum in
    let b1 = p1.Lexing.pos_bol in
    let b2 = p2.Lexing.pos_bol in
    let c1 = p1.Lexing.pos_cnum in
    let c2 = p2.Lexing.pos_cnum in
    let c1 = c1 - b1 in
    let c2 = c2 - b2 in
    (
      if p1.Lexing.pos_fname <> "" then
        Printf.sprintf "in file %s " p1.Lexing.pos_fname
      else
        ""
    ) ^
      if l1 = l2 then
        if c1 = c2 then
          Printf.sprintf "line %d character %d" l1 c1
        else
          Printf.sprintf "line %d characters %d-%d" l1 c1 c2
      else
        Printf.sprintf "from line %d character %d to line %d character %d" l1 c1 l2 c2
end

let print_string_fun = ref print_string
let print_string s = !print_string_fun s
let print_newline () = print_string "\n"
let print_endline s = print_string s; print_newline ()
let read_line_fun = ref read_line
let read_line () = !read_line_fun ()

let printf e = Printf.ksprintf print_string e

let debug e = Printf.ksprintf (fun s -> printf "=D.D= %s.\n\n%!" s) e

let info e = Printf.ksprintf (fun s -> printf "=I.I= %s.\n\n%!" s) e

let command e = Printf.ksprintf (fun s -> printf "=^.^= %s\n\n%!" s) e

(* let error e = Printf.ksprintf (fun s -> Printf.printf "[EE]: %s.\n%!" s; exit 1) e *)

exception Error of string

let error ?pos e =
  let pos =
    match pos with
    | None -> ""
    | Some pos when pos = Pos.dummy -> ""
    | Some pos -> Pos.to_string pos ^ ": "
  in
  Printf.ksprintf (fun s -> raise (Error (pos^s))) e
