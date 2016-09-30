(** Core part of the language. *)

(* This is partly inspired of
http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/ *)

open Stdlib
open Common

(** Do we want the theory of groupoids? *)
let groupoid = ref false
(** Do we allow unsafe uses of meta-variables? *)
let unsafe_evars = ref false

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
and desc =
  | Var of var
  | EVar of (evar ref * subst) (** expression, substition *)
  | Type
  | HomType
  | Obj
  | Arr of expr * expr * expr
  | Pi of var * expr * expr
  | Abs of var * expr * expr
  | App of expr * expr
 (** A pasting scheme. *)
 and ps =
   (var * expr) list
 (** A substitution. *)
 and subst = (var * expr) list
 and evar =
   | ENone of int * expr (** unknown variable with given number and type *)
   | ESome of expr

let mk ?pos desc =
  let pos = Option.default Pos.dummy pos in
  { desc; pos }

let string_of_var = function
  | VIdent x -> x
  | VFresh (x,n) -> x ^ "." ^ string_of_int n

(** String representation. *)
let rec to_string ?(pa=false) e =
  let string_of_evar x = string_of_evar ~pa x in
  let to_string pa e = to_string ~pa e in
  let pa s = if pa then "("^s^")" else s in
  match e.desc with
  | Var x -> string_of_var x
  | EVar (x,_) -> string_of_evar !x
  | Type -> "Type"
  | HomType -> "HomType"
  | Obj -> "*"
  | Arr (t,f,g) -> pa (Printf.sprintf "%s | %s -> %s" (to_string false t) (to_string false f) (to_string false g))
  | Pi (x,t,u) -> pa (Printf.sprintf "(%s : %s) => %s" (string_of_var x) (to_string false t) (to_string false u))
  | Abs (x,t,e) -> pa (Printf.sprintf "\\(%s : %s) => %s" (string_of_var x) (to_string false t) (to_string false e))
  | App (f,e) -> pa (to_string false f ^ " " ^ to_string true e)

and string_of_evar ?(pa=false) = function
  | ENone(n,t) ->
     "?"^string_of_int n
     (* Printf.sprintf "(?%d:%s)" n (to_string t) *)
  | ESome x -> to_string ~pa x
(* "[" ^ to_string false x ^ "]" *)

let string_of_evarref x = string_of_evar !x

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
  fun () ->
  let t = mk (EVar (ref (ENone ((incr n; !n), mk Type)), [])) in
  ref (ENone ((incr n; !n), t))

(** Generate a fresh meta-variable. *)
let fresh_evar ?pos () =
  mk ?pos (EVar (fresh_inevar (), []))

(** Whether a meta-variable occurs in a term. *)
let occurs_evar v e =
  let x =
    match v.desc with
    | EVar ({contents = ENone _} as x, _) -> x
    | _ -> assert false
  in
  let rec aux e =
    match e.desc with
    | Var _ -> false
    | EVar (x', _) -> x' == x
    | Type -> false
    | Abs (x,t,e) -> aux t || aux e
    | App (f,e) -> aux f || aux e
    | Pi (x,t,u) -> aux t || aux u
    | HomType -> false
    | Obj -> false
    | Arr (t,f,g) -> aux t || aux f || aux g
  in
  aux e

(** Apply a parallel substitution. *)
let rec subst (s:subst) e =
  (* Printf.printf "subst: %s[%s]\n%!" (to_string e) (String.concat "," (List.map (fun (x,e) -> to_string e ^ "/" ^ x) s)); *)
  let desc =
    match e.desc with
    | Var x ->
       begin
         try
           (List.assoc x s).desc
         with
         | Not_found -> e.desc
       end
    | EVar (x,s') -> (match !x with ENone _ -> EVar (x,s'@s) | ESome e -> (subst (s'@s) e).desc)
    | Type -> Type
    | HomType -> HomType
    | Obj -> Obj
    | Arr (t,x,y) -> Arr (subst s t, subst s x, subst s y)
    | App (f,x) -> App (subst s f, subst s x)
    | Abs (x,t,e) ->
       let t = subst s t in
       let x' = fresh_var x in
       let s = (x,mk ~pos:e.pos (Var x'))::s in
       let e = subst s e in
       Abs (x',t,e)
    | Pi (x,t,u) ->
       let t = subst s t in
       let x' = fresh_var x in
       let s = (x,mk ~pos:e.pos (Var x'))::s in
       let u = subst s u in
       Pi (x',t,u)
  in
  mk ~pos:e.pos desc

(** Ensure that linked evars do not occur at toplevel. *)
let rec unevar e =
  match e.desc with
  | EVar ({contents = ESome e}, s) -> unevar (subst s e)
  | _ -> e

(** Free meta-variables. *)
(* Note we could compare contents, but it is safer to compare evars by comparing
their references. *)
let rec free_evar e =
  match (unevar e).desc with
  | EVar (x,_) -> [x]
  | Var _ | Type | HomType | Obj -> []
  | Abs (_,t,e) -> List.diffq (free_evar e) (free_evar t)
  | App (e1,e2) -> List.unionq (free_evar e1) (free_evar e2)
  | Arr (t, f, g) -> List.unionq (free_evar t) (List.unionq (free_evar f) (free_evar g))
  | Pi (_,t,u) -> List.unionq (free_evar t) (free_evar u)

(** Replace EVars by fresh ones. *)
(* TODO: use levels? *)
let instantiate e =
  let g = ref [] in
  let rec aux e =
    let desc =
      let e = unevar e in
      match e.desc with
      | Var _ -> e.desc
      | EVar (x, s) ->
         let x' =
           try
             List.assq x !g
           with
           | Not_found ->
              let x' = fresh_inevar () in
              g := (x,x') :: !g;
              x'
         in
         EVar (x', s)
      | Type -> Type
      | Abs (x,t,e) -> Abs (x, aux t, aux e)
      | App (f,e) -> App (aux f, aux e)
      | Pi (x,t,u) -> Pi (x, aux t, aux u)
      | HomType | Obj as e -> e
      | Arr (t,f,g) -> Arr (aux t, aux f, aux g)
    in
    mk ~pos:e.pos desc
  in
  aux e

(** Free variables. *)
let rec free_vars e =
  (* Printf.printf "free_vars: %s\n%!" (to_string e); *)
  match (unevar e).desc with
  | Var x -> [x]
  | EVar (x,s) -> error ~pos:e.pos "don't know how to compute free variables in meta-variables"
  | Type | HomType | Obj -> []
  | Arr (t,f,g) -> (free_vars t)@(free_vars f)@(free_vars g)
  | App (f,x) -> (free_vars f)@(free_vars x)
  | Pi (x,t,u) -> (free_vars t)@(List.remove x (free_vars u))
  | Abs (x,t,e) -> (free_vars t)@(List.remove x (free_vars e))

(** Typing environment. *)
module Env = struct
  (** A typing environment assign to each variable, its value (when known, which
  should be in normal form) and its type. *)
  type t = (var * (expr option * expr)) list

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

  let empty : t = []

  let typ (env:t) x = snd (List.assoc x env)

  let value (env:t) x = fst (List.assoc x env)

  let add (env:t) x ?value t : t = (x,(value,t))::env

  let add_ps env ps = List.fold_left (fun env (x,t) -> add env x t) env ps
end

(** Normalize a value. *)
let rec normalize env e =
  (* Printf.printf "normalize: %s\n%!" (to_string e); *)
  let desc =
    match (unevar e).desc with
    | Var x ->
       begin
         try
           match Env.value env x with
           | Some e -> (normalize env (instantiate e)).desc
           | None -> Var x
         with
         | Not_found -> error ~pos:e.pos "unknown identifier %s" (string_of_var x)
       end
    | EVar (x,s) as e -> (match !x with ENone _ -> e | ESome e -> assert false)
    | App (f, e) ->
       let f = normalize env f in
       let e = normalize env e in
       begin
         match f.desc with
         | Abs (x,t,f) -> (subst [x,e] f).desc (* TODO: use environment? *)
         | _ -> App (f, e)
       end
    | Type -> Type
    | HomType -> HomType
    | Pi (x,t,u) ->
       let t = normalize env t in
       let u = normalize (Env.add env x t) u in
       Pi (x,t,u)
    | Abs (x,t,e) ->
       let t = normalize env t in
       let e = normalize (Env.add env x t) e in
       Abs (x,t,e)
    | Obj -> Obj
    | Arr (t,f,g) ->
       let t = normalize env t in
       let f = normalize env f in
       let g = normalize env g in
       Arr (t,f,g)
  in
  mk ~pos:e.pos desc

(** Pasting schemes. *)
module PS = struct
  type t = ps

  let to_string (ps:t) =
    String.concat " " (List.map (fun (x,t) -> "(" ^ string_of_var x ^ " : " ^ to_string t ^ ")") ps)

  (** Check that a pasting scheme is well-formed. *)
  let check l =
    let x0,l =
      match l with
      | (x,t)::l ->
         assert (t.desc = Obj);
         x,l
      | [] -> error "pasting scheme cannot be empty"
    in
    let marker = function
      | (f,_)::_ -> f
      | _ -> assert false
    in
    let drop ps =
      match ps with
      | (f, {desc = Arr(_, {desc = Var x}, {desc = Var y})})::_ -> (y, List.assoc x ps)::ps
      | _::_ -> assert false
      | [] -> assert false
    in
    let rec aux ps = function
      | (y,ty)::(f,tf)::l ->
         begin
           match tf.desc with
           | Arr (_, {desc = Var fx}, {desc = Var fy}) ->
              if (y <> fy) then error "not a pasting scheme (following types do not match)";
              if fx = marker ps then
                let ps_fv = List.map fst ps in
                assert (not (List.mem f ps_fv));
                assert (not (List.mem y ps_fv));
                let ps = (f,tf)::ps in
                aux ps l
              else
                aux (drop ps) ((y,ty)::(f,tf)::l)
           | _ -> error "not a pasting scheme (types do not match)"
         end
      | [_] -> error "not a pasting scheme (invalid parity)"
      | [] -> ()
    in
    aux [x0,mk Obj] l

  (** Free variables. *)
  let free_vars (ps:t) = List.map fst ps

  (** Dimensions of generators. *)
  let dims (ps:t) =
    let rec aux env = function
      | (x,{desc = Obj})::ps ->
         let env = (x,0)::env in
         aux env ps
      | (x,{desc = Arr (_, {desc = Var f}, {desc = Var g})})::ps ->
         let d = List.assoc f env in
         let env = (x,d+1)::env in
         aux env ps
      | _::_ -> assert false
      | [] -> env
    in
    aux [] ps

  (** Dimension of a pasting scheme. *)
  let dim ps =
    List.fold_left (fun m (x,d) -> max m d) (-1) (dims ps)

  (** Source of a pasting scheme. *)
  let source i ps =
    assert (i >= 0);
    let dims = dims ps in
    let dim x = List.assoc x dims in
    let targets = List.filter (fun (x,t) -> dim x = i+1) ps in
    let targets = List.map (fun (x,t) -> match t.desc with Arr (_, {desc = Var f}, {desc = Var g}) -> g | _ -> assert false) targets in
    List.filter (fun (x,t) -> dim x < i || (dim x = i && not (List.mem x targets))) ps

  (** Target of a pasting scheme. *)
  let target i ps =
    assert (i >= 0);
    let dims = dims ps in
    let dim x = List.assoc x dims in
    let sources = List.filter (fun (x,t) -> dim x = i+1) ps in
    let sources = List.map (fun (x,t) -> match t.desc with Arr (_, {desc = Var f}, {desc = Var g}) -> f | _ -> assert false) sources in
    List.filter (fun (x,t) -> dim x < i || (dim x = i && not (List.mem x sources))) ps
end

(** Type inference. *)
let rec infer_type env e =
  (* Printf.printf "env: %s\n" (String.concat " " (List.map fst env)); *)
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
         let t = Env.typ env x in
         if Env.value env x <> None then instantiate t else t
       with
       | Not_found -> error ~pos:e.pos "unknown identifier %s" (string_of_var x)
     end
  | EVar (x,s) -> (match !x with ENone (n,t) -> t | ESome e -> infer_type env (subst s e))
  | Type -> mk Type
  | Pi (x,t,u) ->
     check_type env t (mk Type);
     check_type (Env.add env x t) u (mk Type);
     mk Type
  | Abs (x,t,e) ->
     check_type env t (mk Type);
     let u = infer_type (Env.add env x t) e in
     mk (Pi (x,t,u))
  | App (f,e) ->
     let t = infer_type env f in
     let x,t,u =
       match (unevar t).desc with
       | Pi (x,t,u) -> x,t,u
       | _ -> error ~pos:f.pos "got %s : %s, but a function is expected" (to_string f) (to_string t)
     in
     let te = infer_type env e in
     if not (leq env te t) then error ~pos:e.pos "got %s, but %s is expected" (to_string te) (to_string t);
     subst [x,e] u
  | HomType -> mk Type
  | Obj -> mk HomType
  | Arr (t,f,g) ->
     check_type env t (mk HomType);
     check_type env f t;
     check_type env g t;
     mk HomType

and check_type env e t =
    let te = infer_type env e in
    if not (leq env te t) then error "got %s, but %s is expected" (to_string te) (to_string t)

(** Subtype relation between expressions. *)
and leq env e1 e2 =
  let rec leq e1 e2 =
    (* Printf.printf "leq\n%s\n%s\n\n" (to_string e1) (to_string e2); *)
    let e1 = unevar e1 in
    let e2 = unevar e2 in
    match e1.desc, e2.desc with
    | Var x1, Var x2 -> x1 = x2
    | Pi (x1,t1,u1), Pi (x2,t2,u2) -> leq t2 t1 && leq u1 (subst [x2,mk (Var x1)] u2)
    | Abs (x1,t1,e1), Abs (x2,t2,e2) -> leq t2 t1 && leq e1 (subst [x2,mk (Var x1)] e2)
    | App (f1,e1), App (f2,e2) -> leq f1 f2 && leq e1 e2
    | Type, Type -> true
    | HomType, HomType -> true
    | HomType, Type -> true
    | Obj, Obj -> true
    | Arr (t1,f1,g1), Arr (t2,f2,g2) -> leq t1 t2 && leq f1 f2 && leq g1 g2
    | EVar (x1, _), EVar (x2, _) when x1 == x2 -> true
    (* | EVar ({contents = ESome t}, s), _ -> leq (subst s t) t2 *)
    (* | _, EVar ({contents = ESome t}, s) -> leq t1 (subst s t) *)
    | EVar ({contents = ENone (n,t)} as x, s), _ ->
       if occurs_evar e1 e2 then false
       (* else if not (eq t (infer_type env (subst s t2))) then false *)
       else (x := ESome e2; leq e1 e2)
    | _, EVar({contents = ENone (n,t)} as x, s) ->
       if occurs_evar e2 e1 then false
       (* else if not (eq t (infer_type env (subst s t1))) then false *)
       else (x := ESome e1; leq e1 e2)
    | (Var _ | Abs _ | App _ | Type | HomType | Pi _ | Obj | Arr _), _ -> false
    | EVar _, _ -> assert false
  in
  leq (normalize env e1) (normalize env e2)

(** A command. *)
type cmd =
  | Decl of var * expr
  | Coh of var * ps * expr
  | Axiom of var * expr
  | Check of expr
  | Eval of expr
  | Env (** Display the environment. *)
  | Set of string * string

let string_of_cmd = function
  | Decl (x,e) -> Printf.sprintf "let %s = %s" (string_of_var x) (to_string e)
  | Coh (x,ps,e) -> Printf.sprintf "coh %s %s : %s" (string_of_var x) (PS.to_string ps) (to_string e)
  | Axiom (x,e) -> Printf.sprintf "ax %s : %s" (string_of_var x) (to_string e)
  | Check e -> Printf.sprintf "check %s" (to_string e)
  | Eval e -> Printf.sprintf "eval %s" (to_string e)
  | Set (x,v) -> Printf.sprintf "set %s = %s" x v
  | Env -> "env"

(** A program. *)
type prog = cmd list

(** Running environment. *)
module Envs = struct
  type t = Env.t * subst

  let empty : t = Env.empty, []
end

(** Execute a command. *)
let exec_cmd ((env,s):Envs.t) cmd : Envs.t =
  command "%s" (string_of_cmd cmd);
  match cmd with
  | Decl (x,e) ->
     let e = subst s e in
     let t = infer_type env e in
     (* let e = normalize env e in *)
     (* let t = infer_type env e in *)
     let x' = fresh_var x in
     info "%s = %s\n    : %s" (string_of_var x') (to_string e) (to_string t);
     (* Try to resolve meta-vairables. *)
     (* if not mv then ignore (infer_type env (normalize env e)); *)
     if not !unsafe_evars && free_evar e <> [] then
       (
         let mv = String.concat ", " (List.map string_of_evarref (free_evar e)) in
         error "expression %s has meta-variables %s" (to_string e) mv
       );
     let env = Env.add env x' ~value:e t in
     let s = (x,mk (Var x'))::s in
     env,s
  | Coh (x,ps,t) ->
     (* Apply s. *)
     let ps, t =
       let s = ref s in
       let ps =
         List.map
           (fun (x,t) ->
             let x' = fresh_var x in
             let ans = x', subst !s t in
             s := (x,mk (Var x')) :: !s;
             ans
           ) ps
       in
       let t = subst !s t in
       ps, t
     in
     (* Normalize types in order to reveal hidden variables. *)
     let env =
       List.fold_left
         (fun env (x,t) ->
           let t = normalize env t in
           check_type env t (mk Type);
           Env.add env x t
         ) env ps
     in
     let t = normalize env t in
     check_type env t (mk Type);
     (* Printf.printf "env:\n\n%s\n%!" (Env.to_string env); *)
     (* Printf.printf "type: %s\n%!" (to_string t); *)
     (* Printf.printf "type: %s\n%!" (to_string (normalize env t)); *)
     (* debug "check pasting scheme %s" (PS.to_string ps); *)
     PS.check ps;
     if not !groupoid then
       begin
         let f,g =
           match (unevar t).desc with
           | Arr (_,f,g) -> f,g
           | _ -> assert false
         in
         let fv = PS.free_vars ps in
         let rec close_vars f =
           match (unevar (infer_type env f)).desc with
           | Arr (_,x,y) -> List.union (close_vars x) (List.union (close_vars y) (free_vars f))
           | Obj -> free_vars f
           | _ -> assert false
         in
         let fvf = close_vars f in
         let fvg = close_vars g in
         if not (List.included fv fvf && List.included fv fvg) then
           begin
             let i = PS.dim ps in
             debug "checking decompositions";
             let fvs = PS.free_vars (PS.source (i-1) ps) in
             let fvt = PS.free_vars (PS.target (i-1) ps) in
             if i < 1
                || not (List.included fvs fvf)
                || not (List.included fvt fvg)
             then
               let bad = List.union (List.diff fvs fvf) (List.diff fvt fvg) in
               let bad = String.concat ", " (List.map string_of_var bad) in
               error ~pos:t.pos "not algebraic: %s is not used" bad;
           end;
       end;
     let t = List.fold_right (fun (x,t) u -> mk (Pi (x,t,u))) ps t in
     let x' = fresh_var x in
     let env = Env.add env x' t in
     let s = (x,mk (Var x'))::s in
     info "%s : %s" (string_of_var x') (to_string t);
     env,s
  | Axiom (x,t) ->
     let t = subst s t in
     let x' = fresh_var x in
     check_type env t (mk Type);
     let env = Env.add env x' t in
     let s = (x,mk (Var x'))::s in
     env,s
  | Check e ->
     let e = subst s e in
     let t = infer_type env e in
     printf "%s\n%!" (to_string t);
     env,s
  | Eval e ->
     let e = subst s e in
     let e0 = e in
     let e = normalize env e in
     let t = infer_type env e in
     printf "    %s\n    = %s\n    : %s\n%!" (to_string e0) (to_string e) (to_string t);
     env,s
  | Env ->
     print_endline ("\n" ^ Env.to_string env);
     env,s
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
     else
       error "unknown option %s" o;
     env,s

(** Execute a program. *)
let exec envs prog =
  List.fold_left exec_cmd envs prog
