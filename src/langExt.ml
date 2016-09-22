(** Extensions to the language. *)

open Lang

(** Substitutions. *)
module Subst = struct
  (** A substitution: a list of terms with their type. *)
  type t = (expr * expr) list

  (** Create from a pasting scheme. *)
  let of_ps (ps:PS.t) : t =
    List.map (fun (x,t) -> Var x, t) ps

  (*
  (** Compute all the possible applications of a function to a substitution. *)
  let match_app env ps f =
    let args =
      let rec aux = function
        | Pi (x,t,u) -> (x,t)::(aux u)
        | _ -> []
      in
      aux (infer_type env f)
    in
    (* Substitution for the arguments. *)
    let ss = List.map (fun (x,t) -> (x,Var x,t)) args in
    let rec aux env ps ss =
      match ss with
      | (x,
      | [] -> [ss]
    in
  *)
end
