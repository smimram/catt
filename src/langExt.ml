(** Extensions to the language. *)

open Stdlib
open Lang

(** Substitutions. *)
module Subst = struct
  (** A substitution: a list of terms with their type. *)
  type t = (expr * expr) list

  (** Create from a pasting scheme. *)
  let of_ps (ps:PS.t) : t =
    List.map (fun (x,t,_) -> mk (Var x), t) ps

  let dummy = Var (VIdent "?")

  (** Compute all the possible applications of a function to a substitution. *)
  let match_app env ps f =
    let rec aux f =
      match (unevar (infer_type env f)).desc with
      | Pi ((x,t,_),u) ->
         Enum.flatten
           (Enum.may_map
              (fun (e,t) ->
                let f = mk (App (f,e)) in
                (* Printf.printf "try: %s\n" (to_string f); *)
                try
                  ignore (infer_type env f);
                  Some (aux f)
                with
                | Common.Error e ->
                   (* print_endline ("rejected: " ^ e); *)
                   None
              ) (Enum.of_list ps))
      | _ -> Enum.once f
    in
    Enum.to_list (aux f)
    (*
    let args =
      let rec aux = function
        | Pi (x,t,u) -> (x,t)::(aux u)
        | _ -> []
      in
      aux (infer_type env f)
    in
    let rec aux env' = function
      | (x,t)::args ->
         Enum.flatten
           (Enum.may_map
              (fun (e,u) ->
                (* Printf.printf "env: %s\n%!" (Env.to_string env); *)
                let t = subst env' t in
                Printf.printf "proposed: %s = %s : %s / %s\n%!" x (to_string e) (to_string t) (to_string u);
                let eq = try eq env t u with Common.Error s -> print_endline s; false in
                if not eq then (Printf.printf "rejected\n"; None) else
                  let x' = fresh_var x in
                  Printf.printf "OK\n%!";
                  let env' = (x,e)::env' in
                  let ans = aux env' args in
                  let ans = Enum.map (fun ss -> (x,e)::ss) ans in
                  Some ans
              ) (Enum.of_list ps)
           )
      | [] ->
         Enum.once []
    in
    let ss = aux [] args in
    Enum.to_list ss
     *)
end
