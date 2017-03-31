(** Core part of the language. *)

open Stdlib
open Common

(** {2 Global options} *)

(** Do we want the theory of groupoids? *)
let groupoid = ref false
(** Do we allow unsafe uses of meta-variables? *)
let unsafe_evars = ref false
(** Do we allow parametric pasting schemes? *)
let parametric_schemes = ref true
(** Do we show instance numbers in strings? *)
let show_instances = ref true

(** {2 Data types} *)

(** A variable. *)
type var =
  | VIdent of string
  | VFresh of string * int

(** An expression. *)
type expr =
  {
    desc : desc;
    pos : Pos.t;
  }

 (** Contents of an expression. *)
 and desc =
   | Var of var (** type variable *)
   | EVar of evar ref (** meta-variable *)
   | Type
   | HomType (** a type of hom set *)
   | Obj (** type of 0-cells *)
   | Arr of expr * expr * expr (** arrow type *)
   | Pi of var * expr * expr
   | Abs of var * expr * expr
   | App of expr * expr
   | Coh of string * ps * expr (** coherence (name, source, target) *)
   | Clos of subst * expr  (** closure *)

 (** A pasting scheme. *)
 and ps =
   | PNil of (var * expr) (** start *)
   | PCons of ps * (var * expr) * (var * expr) (** extend *)
   | PDrop of ps (** drop *)

 (** A meta-variable. *)
 and evar =
   | ENone of int * expr (** unknown variable with given number and type *)
   | ESome of expr (** instantiated variable *)

 (** A substitution. *)
 and subst = (var * expr) list

(** Create an expression from its contents. *)
let mk ?pos desc =
  let pos = Option.default Pos.dummy pos in
  { desc; pos }

(** {2 String representation} *)
    
(** String representation of a variable. *)
let string_of_var = function
  | VIdent x -> x
  | VFresh (x,n) -> x ^ (if !show_instances then "." ^ string_of_int n else "")

(** String representation of an expression. *)
let rec to_string ?(pa=false) e =
  let to_string pa e = to_string ~pa e in
  let string_of_evar x = string_of_evar ~pa x in
  let pa s = if pa then "("^s^")" else s in
  match e.desc with
  | Var x -> string_of_var x
  | EVar x -> string_of_evar !x
  | Type -> "Type"
  | HomType -> "HomType"
  | Obj -> "*"
  | Arr (t,f,g) -> pa (Printf.sprintf "%s | %s -> %s" (to_string false t) (to_string false f) (to_string false g))
  | Coh (c,ps,t) ->
     if c = "" then
       Printf.sprintf "coh (%s => %s)" (string_of_ps ps) (to_string false t)
     else
       c
  | Pi (x,t,u) -> pa (Printf.sprintf "(%s : %s) => %s" (string_of_var x) (to_string false t) (to_string false u))
  | Abs (x,t,e) -> pa (Printf.sprintf "\\(%s : %s) => %s" (string_of_var x) (to_string false t) (to_string false e))
  | App (f,e) -> pa (to_string false f ^ " " ^ to_string true e)
  | Clos (s,e) -> Printf.sprintf "[%s]" (to_string false e)

(** String representation of a meta-variable. *)
and string_of_evar ?(pa=false) = function
  | ENone(n,t) ->
     if !show_instances then "?"^string_of_int n else "_"
     (* Printf.sprintf "(?%d:%s)" n (to_string t) *)
  | ESome x -> to_string ~pa x
     (* "[" ^ to_string false x ^ "]" *)

(** String representation of a pasting scheme. *)
and string_of_ps = function
  | PNil (x,t) -> Printf.sprintf "(%s : %s)" (string_of_var x) (to_string t)
  | PCons (ps,(x,t),(y,u)) -> Printf.sprintf "%s (%s : %s) (%s : %s)" (string_of_ps ps) (string_of_var x) (to_string t) (string_of_var y) (to_string u)
  | PDrop ps -> string_of_ps ps ^ " ! "

let string_of_evarref x = string_of_evar !x

let string_of_expr = to_string

(** Pasting schemes. *)
module PS = struct
  (** A pasting scheme. *)
  type t = ps

  (** String representation. *)
  let to_string = string_of_ps

  (** Dangling variable. *)
  let rec marker ps =
    (* Printf.printf "marker: %s\n%!" (to_string ps); *)
    match ps with
    | PNil (x,t) -> x,t
    | PCons (ps,_,f) -> f
    | PDrop ps ->
       let f,tf = marker ps in
       match tf.desc with
       | Arr (_,x,{desc = Var y}) ->
          let t =
            let rec aux = function
              | PNil (x,t) -> assert (x = y); t
              | PCons (ps,(y',ty),(f,tf)) ->
                 if y' = y then ty
                 else if f = y then tf
                 else aux ps
              | PDrop ps -> aux ps
            in
            aux ps
          in
          y,t
       | _ -> assert false

  (** Free variables. *)
  let rec free_vars = function
    | PNil (x,t) -> [x]
    | PCons (ps,(y,_),(f,_)) -> f::y::(free_vars ps)
    | PDrop ps -> free_vars ps

  (** Create from a context. *)
  let make l : t =
    (* Printf.printf "make: %s\n%!" (String.concat_map " " (fun (x,t) -> Printf.sprintf "(%s : %s)" (string_of_var x) (string_of_expr t)) l); *)
    let x0,t0,l =
      match l with
      | (x,t)::l ->
         if not !parametric_schemes then assert (t.desc = Obj);
         x,t,l
      | [] -> error "pasting scheme cannot be empty"
    in
    let rec aux ps = function
      | (y,ty)::(f,tf)::l ->
         begin
           match tf.desc with
           | Arr (_, {desc = Var fx}, {desc = Var fy}) ->
              (* Printf.printf "check: %s:?->%s\n%!" (string_of_var f) (string_of_var y); *)
              if (y <> fy) then error ~pos:tf.pos "not a pasting scheme (following types do not match)";
              let x,tx = marker ps in
              if x = fx then
                let fvps = free_vars ps in
                assert (not (List.mem f fvps));
                assert (not (List.mem y fvps));
                let ps = PCons (ps,(y,ty),(f,tf)) in
                aux ps l
              else
                aux (PDrop ps) ((y,ty)::(f,tf)::l)
           | _ -> error ~pos:tf.pos "not a pasting scheme (types do not match)"
         end
      | [_] -> error "not a pasting scheme (invalid parity)"
      | [] -> ps
    in
    aux (PNil(x0,t0)) l

  (** Height of a pasting scheme. *)
  let rec height = function
    | PNil _ -> 0
    | PCons (ps,_,_) -> height ps + 1
    | PDrop ps -> height ps - 1

  (** Dimension of a pasting scheme. *)
  let rec dim = function
    | PNil _ -> 0
    | PCons (ps,_,_) -> max (dim ps) (height ps + 1)
    | PDrop ps -> dim ps

  (** Source of a pasting scheme. *)
  let source i ps =
    assert (i >= 0);
    let rec aux = function
      | PNil _ as ps -> ps
      | PCons (ps,_,_) when height ps >= i -> aux ps
      | PCons (ps,y,f) -> PCons (aux ps,y,f)
      | PDrop ps when height ps > i -> aux ps
      | PDrop ps -> PDrop (aux ps)
    in
    aux ps

  (** Target of a pasting scheme. *)
  let target i ps =
    assert (i >= 0);
    let replace g = function
      | PNil x -> PNil g
      | PCons (ps,y,f) -> PCons (ps,y,g)
      | _ -> assert false
    in
    let rec aux = function
      | PNil _ as ps -> ps
      | PCons (ps,_,_) when height ps > i -> aux ps
      | PCons (ps,y,f) when height ps = i -> replace y (aux ps)
      | PCons (ps,y,f) -> PCons (aux ps,y,f)
      | PDrop ps when height ps > i -> aux ps
      | PDrop ps -> PDrop (aux ps)
    in
    aux ps

  let rec exists f = function
    | PNil x -> f x
    | PCons (ps,x,y) -> exists f ps || f x || f y
    | PDrop ps -> exists f ps

  let rec map f = function
    | PNil x -> PNil (f x)
    | PCons (ps,x,y) ->
       let ps = map f ps in
       let x = f x in
       let y = f y in
       PCons (ps,x,y)
    | PDrop ps -> PDrop (map f ps)

  let rec fold_left f s = function
    | PNil x -> f s x
    | PCons (ps,x,y) ->
       let s = fold_left f s ps in
       let s = f s x in
       f s y
    | PDrop ps -> fold_left f s ps

  let rec fold_left2 f s ps1 ps2 =
    match ps1, ps2 with
    | PNil x1, PNil x2 -> f s x1 x2
    | PCons (ps1,y1,f1), PCons(ps2,y2,f2) ->
       let s = fold_left2 f s ps1 ps2 in
       let s = f s y1 y2 in
       f s f1 f2
    | PDrop ps1, PDrop ps2 -> fold_left2 f s ps1 ps2
    | (PNil _  | PCons _ | PDrop _), _ -> assert false

  let rec fold_right f ps s =
    match ps with
    | PNil x -> f x s
    | PCons (ps,x,y) ->
       let s = f y s in
       let s = f x s in
       fold_right f ps s
    | PDrop ps -> fold_right f ps s
end

(** {2 Variables} *)

(** Generate a fresh variable name. *)
let fresh_var =
  let count = ref [] in
  (fun x ->
    let x =
      match x with
      | VIdent x -> x
      | VFresh (x,_) -> x
    in
    let n =
      try
        let n = List.assoc x !count in
        count := List.remove_assoc x !count;
        count := (x,n+1) :: !count;
        n
      with
      | Not_found ->
         count := (x,1) :: !count;
         0
    in
    VFresh (x,n))

let fresh_inevar =
  let n = ref (-1) in
  fun ?t () ->
  let t =
    match t with
    | Some t -> t
    | None -> mk (EVar (ref (ENone ((incr n; !n), mk Type))))
  in
  ref (ENone ((incr n; !n), t))

(** Generate a fresh meta-variable. *)
let fresh_evar ?pos ?t () =
  mk ?pos (EVar (fresh_inevar ?t ()))

(** Whether a meta-variable occurs in a term. *)
let occurs_evar v e =
  let x =
    match v.desc with
    | EVar ({contents = ENone _} as x) -> x
    | _ -> assert false
  in
  let rec aux e =
    match e.desc with
    | Var _ -> false
    | EVar (x') -> x' == x
    | Type -> false
    | Abs (x,t,e) -> aux t || aux e
    | App (f,e) -> aux f || aux e
    | Pi (x,t,u) -> aux t || aux u
    | HomType -> false
    | Obj -> false
    | Arr (t,f,g) -> aux t || aux f || aux g
    | Coh (_,ps,e) -> PS.exists (fun (x,t) -> aux t) ps || aux e
    | Clos (s,e) ->
       (* List.exists (fun (x,e) -> aux e) s || aux e *)
       assert false
  in
  aux e

(** Ensure that linked evars do not occur at toplevel. *)
let rec unevar e =
  match e.desc with
  | EVar {contents = ESome e} -> unevar e
  | _ -> e

(** Free meta-variables. *)
(* Note we could compare contents, but it is safer to compare evars by comparing
their references. *)
let rec free_evar e =
  match (unevar e).desc with
  | EVar x -> [x]
  | Var _ | Type | HomType | Obj -> []
  | Abs (_,t,e) -> List.diffq (free_evar e) (free_evar t)
  | App (e1,e2) -> List.unionq (free_evar e1) (free_evar e2)
  | Arr (t, f, g) -> List.unionq (free_evar t) (List.unionq (free_evar f) (free_evar g))
  | Pi (_,t,u) -> List.unionq (free_evar t) (free_evar u)
  | Coh (_,ps,t) -> PS.fold_left (fun l (x,t) -> List.unionq (free_evar t) l) (free_evar t) ps
  | Clos _ -> assert false

(** Replace EVars by fresh ones. *)
(* TODO: use levels? *)
let instantiate e =
  let g = ref [] in
  let rec aux e =
    let desc =
      let e = unevar e in
      match e.desc with
      | Var _ -> e.desc
      | EVar x ->
         let x' =
           try
             List.assq x !g
           with
           | Not_found ->
              let x' = fresh_inevar () in
              g := (x,x') :: !g;
              x'
         in
         EVar x'
      | Type -> Type
      | Abs (x,t,e) -> Abs (x, aux t, aux e)
      | App (f,e) -> App (aux f, aux e)
      | Pi (x,t,u) -> Pi (x, aux t, aux u)
      | HomType | Obj as e -> e
      | Coh (c,ps,t) ->
         let ps = PS.map (fun (x,t) -> x,aux t) ps in
         let t = aux t in
         Coh (c,ps,t)
      | Arr (t,f,g) -> Arr (aux t, aux f, aux g)
      | Clos (s,e) ->
         let s = List.map (fun (x,e) -> x,aux e) s in
         let e = aux e in
         Clos (s,e)
    in
    mk ~pos:e.pos desc
  in
  aux e

(** Free variables. *)
let rec free_vars e =
  (* Printf.printf "free_vars: %s\n%!" (to_string e); *)
  match (unevar e).desc with
  | Var x -> [x]
  | EVar x ->
     if !parametric_schemes then [] else
       error ~pos:e.pos "don't know how to compute free variables in meta-variables"
  | Type | HomType | Obj -> []
  | Arr (t,f,g) -> (free_vars t)@(free_vars f)@(free_vars g)
  | App (f,x) -> (free_vars f)@(free_vars x)
  | Pi (x,t,u) -> (free_vars t)@(List.remove x (free_vars u))
  | Abs (x,t,e) -> (free_vars t)@(List.remove x (free_vars e))
  | Coh (c,ps,t) -> PS.fold_right (fun (x,t) l -> (free_vars t)@List.remove x l) ps (free_vars t)
  | Clos _ -> assert false

(*
(** Typing environments. *)
module Env = struct
  (** A typing environment assign to each variable, its value (when known, which
  should be in normal form) and its type. *)
  type t = (var * (expr option * expr)) list

  (** String representation. *)
  let to_string (env:t) =
    let f (x, (e, t)) =
      let x = string_of_var x in
      match e with
      | Some e ->
         let pad = String.make (String.length x) ' ' in
         Printf.sprintf "%s = %s\n%s : %s\n" x (to_string e) pad (to_string t)
      | None ->
         Printf.sprintf "%s : %s\n" x (to_string t)
    in
    String.concat "\n" (List.map f (List.rev env))

  (** Empty environment. *)
  let empty : t = []

  (** Type of an expression in an environment. *)
  let typ (env:t) x = snd (List.assoc x env)

  (** Value of an expression in an environment. *)
  let value (env:t) x = fst (List.assoc x env)

  let add (env:t) x ?value t : t = (x,(value,t))::env

  let add_ps env ps = List.fold_left (fun env (x,t) -> add env x t) env ps
end
*)

(** {2 Reduction and typing} *)

(** Create a closure. *)
let closure s e =
  if s = [] then e else mk ~pos:e.pos (Clos (s,e))

(** Remove top-level closure. *)
let unclosure e =
  match (unevar e).desc with
  | Clos (s,e) -> s,e
  | _ -> [],e

(** Compute the weak head normal form of a value. *)
let rec normalize env e =
  let closure s e = (closure s e).desc in
  (* Printf.printf "normalize: %s\n%!" (to_string e); *)
  let desc =
    match (unevar e).desc with
    | Var x ->
       begin
         try
           (List.assoc x env).desc
         with
         | Not_found -> error ~pos:e.pos "unknown identifier %s" (string_of_var x)
       end
    | EVar x as e -> e
    | App (f, e) ->
       let f = normalize env f in
       let e = normalize env e in
       let s,f = unclosure f in
       let env = s@env in
       begin
         match f.desc with
         | Abs (x,t,f) ->
            let env = (x,e)::env in
            closure env f
         | _ ->
            closure env (mk ~pos:e.pos (App (f, e)))
       end
    | Arr (t,f,g) ->
       let t = normalize env t in
       let f = normalize env f in
       let g = normalize env g in
       Arr (t,f,g)
    | Clos (s,e) ->
       let env = s@env in
       (normalize env e).desc
    | Type -> Type
    | HomType -> HomType
    | Obj -> Obj
    | Pi _ | Abs _ | Coh _ -> closure env e
  in
  mk ~pos:e.pos desc

(** Type inference. *)
let rec infer_type env tenv e =
  (* Printf.printf "env: %s\n" (String.concat " " (List.map string_of_var (List.map fst env))); *)
  (* Printf.printf "infer_type: %s\n%!" (to_string e); *)
  (* let infer_type env e = *)
  (* let t = infer_type env e in *)
  (* Printf.printf "infer_type: %s : %s\n%!" (to_string e) (to_string t); *)
  (* t *)
  (* in *)
  match e.desc with
  | Var x ->
     begin
       try
         let t = List.assoc x tenv in
         if List.mem_assoc x env then instantiate t else t
       with
       | Not_found -> error ~pos:e.pos "unknown identifier %s" (string_of_var x)
     end
  | EVar x -> (match !x with ENone (n,t) -> t | ESome e -> infer_type env tenv e)
  | Type -> mk Type
  | Pi (x,t,u) ->
     check_type env tenv t (mk Type);
     let x' = mk (Var (fresh_var x)) in
     let env = (x,x')::env in
     let tenv = (x,closure env t)::tenv in
     check_type env tenv u (mk Type);
     mk Type
  | Abs (x,t,e) ->
     (* TODO: check this *)
     check_type env tenv t (mk Type);
     let x' = fresh_var x in
     let env = (x,mk (Var x'))::env in
     let tenv = (x,closure env t)::tenv in
     let u = infer_type env tenv e in
     mk (Pi (x',t,u))
  | App (f,e) ->
     let t = infer_type env tenv f in
     let t,u =
       let s,t = unclosure t in
       match (unevar t).desc with
       | Pi (x,t,u) -> (closure s t),(closure ((x,e)::s) u)
       | _ -> error ~pos:f.pos "got %s : %s, but a function is expected" (to_string f) (to_string t)
     in
     let te = infer_type env tenv e in
     if not (leq env te t) then error ~pos:e.pos "got %s, but %s is expected" (to_string te) (to_string t);
     u
  | HomType -> mk Type
  | Obj -> mk HomType
  | Coh (c,ps,t) ->
     (* Normalize types in order to reveal hidden variables. *)
     (* TODO: we should refresh variable names *)
     let tenv = ref tenv in
     let ps =
       PS.map
         (fun (x,t) ->
           let t = normalize env t in
           check_type env !tenv t (mk HomType);
           tenv := (x,t) :: !tenv;
           x,t
         ) ps
     in
     let tenv = !tenv in
     let t = normalize env t in
     check_type env tenv t (mk HomType);
     (* Printf.printf "COH: %s\n%!" (to_string (mk (Coh(c,ps,t)))); *)
     (* Printf.printf "env:\n\n%s\n%!" (Env.to_string env); *)
     (* Printf.printf "type: %s\n%!" (to_string t); *)
     (* Printf.printf "type: %s\n%!" (to_string (normalize env t)); *)
     (* debug "check pasting scheme %s" (PS.to_string ps); *)
     if not !groupoid then
       begin
         let f,g =
           match (unevar t).desc with
           | Arr (_,f,g) -> f,g
           | _ -> assert false
         in
         let fv = PS.free_vars ps in
         let rec close_vars f =
           match (unevar (infer_type env tenv f)).desc with
           | Arr (_,x,y) -> List.union (close_vars x) (List.union (close_vars y) (free_vars f))
           | t ->
              if not !parametric_schemes then assert (t = Obj);
              free_vars f
         in
         let fvf = close_vars f in
         let fvg = close_vars g in
         if not (List.included fv fvf && List.included fv fvg) then
           begin
             let i = PS.dim ps in
             (* debug "checking decompositions"; *)
             let pss = PS.source (i-1) ps in
             let pst = PS.target (i-1) ps in
             (* Printf.printf "ps : %s\n%!" (PS.to_string ps); *)
             (* Printf.printf "dim: %d\n%!" i; *)
             (* Printf.printf "src: %s\n%!" (PS.to_string pss); *)
             (* Printf.printf "tgt: %s\n%!" (PS.to_string pst); *)
             let fvs = PS.free_vars pss in
             let fvt = PS.free_vars pst in
             if i < 1
                || not (List.included fvs fvf)
                || not (List.included fvt fvg)
             then
               let bad = List.union (List.diff fvs fvf) (List.diff fvt fvg) in
               let bad = String.concat ", " (List.map string_of_var bad) in
               error ~pos:t.pos "not algebraic: %s not used in %s" bad (to_string (mk (Coh (c,ps,t))));
           end;
       end;
     PS.fold_right (fun (x,t) u -> mk (Pi (x,t,u))) ps t
  | Arr (t,f,g) ->
     check_type env tenv t (mk HomType);
     check_type env tenv f t;
     check_type env tenv g t;
     mk HomType
  | Clos(s,e) ->
     let env = s@env in
     infer_type env tenv e

(** Check that an expression has given type. *)
and check_type env tenv e t =
  Printf.printf "check_type: %s : %s\n%!" (to_string e) (to_string t);
  let te = infer_type env tenv e in
  Printf.printf "checked: %s\n%!" (to_string e);
  if not (leq env te t) then error ~pos:e.pos "got %s, but %s is expected" (to_string te) (to_string t)

(** Subtype relation between expressions. *)
and leq env e1 e2 =
  let rec leq e1 e2 =
    Printf.printf "leq\n%s\n%s\n\n" (to_string e1) (to_string e2);
    let s1,e1 = unclosure e1 in
    let s2,e2 = unclosure e2 in
    match e1.desc, e2.desc with
    (* We could use unclose, but this is safer. *)
    | Pi (x1,t1,u1), Pi (x2,t2,u2) ->
       let t1 = normalize s1 t1 in
       let t2 = normalize s2 t2 in
       let x' = mk (Var (fresh_var x1)) in
       let u1 = normalize ((x1,x')::s1) u1 in
       let u2 = normalize ((x2,x')::s2) u2 in
       leq t2 t1 && leq u1 u2
    | Abs (x1,t1,e1), Abs (x2,t2,e2) ->
       let t1 = normalize s1 t1 in
       let t2 = normalize s2 t2 in
       let x' = mk (Var (fresh_var x1)) in
       let e1 = normalize ((x1,x')::s1) e1 in
       let e2 = normalize ((x2,x')::s2) e2 in
       leq t2 t1 && leq e1 e2
    | Var x1, Var x2 ->
       assert (s1 = [] && s2 = []);
       x1 = x2
    | App (f1,e1), App (f2,e2) ->
       assert (s1 = [] && s2 = []);
       leq f1 f2 && leq e1 e2
    | Type, Type -> true
    | HomType, HomType -> true
    | HomType, Type -> true
    | Obj, Obj -> true
    | Coh(_,ps1,t1), Coh(_,ps2,t2) ->
       let s1 = ref s1 in
       let s2 = ref s2 in
       let ans =
         PS.fold_left2
           (fun ans (x1,t1) (x2,t2) ->
             let x' = mk (Var (fresh_var x1)) in
             s1 := (x1,x') :: !s1;
             s2 := (x2,x') :: !s2;
             let t1 = normalize !s1 t1 in
             let t2 = normalize !s2 t2 in
             ans && leq t1 t2
           ) true ps1 ps2
       in
       let t1 = normalize !s1 t1 in
       let t2 = normalize !s2 t2 in
       ans && leq t1 t2
    | Arr (t1,f1,g1), Arr (t2,f2,g2) -> leq t1 t2 && leq f1 f2 && leq g1 g2
    | EVar x1, EVar x2 when x1 == x2 -> true
    | EVar ({contents = ENone (n,t)} as x), _ ->
       if occurs_evar e1 e2 then false
       (* TODO: add tenv to be able to perform this check *)
       (* else if not (leq (infer_type env e2) t) then false *)
       else (x := ESome e2; leq e1 e2)
    | _, EVar({contents = ENone (n,t)} as x) ->
       if occurs_evar e2 e1 then false
       (* TODO: add tenv to be able to perform this check *)
       (* else if not (leq (infer_type env e1) t) then false *)
       else (x := ESome e1; leq e1 e2)
    | (Var _ | Abs _ | App _ | Type | HomType | Pi _ | Obj | Arr _ | Coh _), _ -> false
    | EVar _, _ -> assert false
    | Clos _, _ -> assert false
  in
  leq (normalize env e1) (normalize env e2)

(** {2 Programs} *)

(** A command. *)
type cmd =
  | Decl of var * expr * expr (** Declare a variable with given type and value. *)
  | Axiom of var * expr (** Declare an axiom of given type. *)
  | Check of expr (** Check the type of an expression. *)
  | Eval of expr (** Evaluate an expression. *)
  | Env (** Display the environment. *)
  | Set of string * string (** Set an option. *)

(** String representation of a command. *)
let string_of_cmd = function
  | Decl (x,t,e) ->
     let t =
       match (unevar t).desc with
       | EVar _ -> ""
       | _ -> " : " ^ to_string t
     in
     Printf.sprintf "let %s%s = %s" (string_of_var x) t (to_string e)
  | Axiom (x,e) -> Printf.sprintf "ax %s : %s" (string_of_var x) (to_string e)
  | Check e -> Printf.sprintf "check %s" (to_string e)
  | Eval e -> Printf.sprintf "eval %s" (to_string e)
  | Set (x,v) -> Printf.sprintf "set %s = %s" x v
  | Env -> "env"

(** A program. *)
type prog = cmd list

(** Execute a command. *)
let exec_cmd (env,tenv) cmd =
  command "%s" (string_of_cmd cmd);
  match cmd with
  | Decl (x,t,e) ->
     Printf.printf "decl t: %s\n%!" (to_string t);
     check_type env [] t (mk Type);
     Printf.printf "decl e: %s\n%!" (to_string e);
     (* let t = infer_type env e in *)
     check_type env tenv e t;
     (* Try to resolve meta-variables. *)
     let mv = free_evar e in
     let mv =
       List.filter
         (fun x -> match !x with ENone (n,t) -> (unevar t).desc <> HomType | ESome _ -> assert false) mv
     in
     if not !unsafe_evars && mv <> [] then
       (
         let s x = string_of_evarref x in
         (* let s x = *)
           (* let t = *)
             (* match !x with *)
             (* | ENone (_,t) -> t *)
             (* | _ -> assert false *)
           (* in *)
           (* string_of_evarref x ^ " : " ^ to_string t *)
         (* in *)
         let mv = String.concat ", " (List.map s mv) in
         error ~pos:e.pos "expression %s has meta-variables %s" (to_string e) mv
       );
     let env = (x,e)::env in
     let tenv = (x,t)::tenv in
     env,tenv
  | Axiom (x,t) ->
     check_type env tenv t (mk Type);
     let env = (x,mk (Var x))::env in
     let tenv = (x,t)::tenv in
     env,tenv
  | Check e ->
     let t = infer_type env tenv e in
     printf "%s\n%!" (to_string t);
     env,tenv
  | Eval e ->
     let e0 = e in
     let e = normalize env e in
     let t = infer_type env tenv e in
     printf "    %s\n    = %s\n    : %s\n%!" (to_string e0) (to_string e) (to_string t);
     env,tenv
  | Env ->
     print_endline ("\n" ^ String.concat_map " , " (fun (x,e) -> Printf.sprintf "%s=%s" x (to_string e)) env);
     env
  | Set (o,v) ->
     let bool () =
       if v = "true" then true
       else if v = "false" then false
       else error "unknown value %s for option %s" v o
     in
     if o = "groupoid" then
       (* Switch groupoid mode. *)
       groupoid := bool ()
     else if o = "unsafe-evars" then
       unsafe_evars := bool ()
     else if o = "show-instances" then
       show_instances := bool ()
     else if o = "exit" then
       exit 0
     else
       error "unknown option %s" o;
     env,s

(** Execute a program. *)
let exec envs prog =
  List.fold_left exec_cmd envs prog
