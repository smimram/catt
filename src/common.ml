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

let error e = Printf.ksprintf (fun s -> raise (Error s)) e
         
