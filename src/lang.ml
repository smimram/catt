(** Core part of the language. *)

open Stdlib
open Common

(** Do we want the theory of groupoids? *)
let groupoid = ref false

(** An expression. *)
type expr =
  | Var of string
  | Coh of ps * expr (* the list is reversed *)
  | Type of int
  | Obj
  | Arr of expr * expr
  | Pi of string * expr * expr
  | Abs of string * expr * expr
  | App of expr * expr
 (** A pasting scheme. *)
 and ps =
   (string * expr) list

(** String representation. *)
let rec to_string = function
  | Var x -> x
  | Coh (p,t) ->
     let p = String.concat " " (List.map (fun (x,t) -> "(" ^ x ^ " : " ^ to_string t ^ ")") p) in
     let t = to_string t in
     "coh " ^ p ^ " => " ^ t
  | Type n -> "Type" ^ string_of_int n
  | Obj -> "*"
  | Arr (x,y) -> to_string x ^ " -> " ^ to_string y
  | Pi (x,t,u) -> Printf.sprintf "(%s : %s) => %s" x (to_string t) (to_string u)
  | Abs (x,t,e) -> Printf.sprintf "\\(%s : %s) => %s" x (to_string t) (to_string e)
  | App (f,e) -> to_string f ^ " " ^ to_string e

(** Free variables. *)
let rec free_vars = function
  | Var x -> [x]
  | Coh _ | Obj | Type _ -> []
  | Arr (s,t) -> (free_vars s)@(free_vars t)
  | App (f,x) -> (free_vars f)@(free_vars x)
  | Pi (x,t,u) -> (free_vars t)@(List.remove x (free_vars u))
  | Abs (x,t,e) -> (free_vars t)@(List.remove x (free_vars e))

(** Generate a fresh variable name. *)
let fresh_var =
  let n = ref 0 in
  (fun () -> incr n; Printf.sprintf "#x%d" !n)

(** Apply a substitution. *)
let rec subst s = function
  | Var x ->
     begin
       try
         List.assoc x s
       with
       | Not_found -> Var x
     end
  | Type n -> Type n
  | Obj -> Obj
  | Coh (ps,t) ->
     let ps = List.map (fun (x,t) -> x, subst s t) ps in
     let t = subst s t in
     Coh (ps,t)
  | Arr (x,y) -> Arr (subst s x, subst s y)
  | App (f,x) -> App (subst s f, subst s x)
  | Abs (x,t,e) ->
     let t = subst s t in
     let x' = fresh_var () in
     let s = (x,Var x')::s in
     let e = subst s e in
     Abs (x,t,e)
  | Pi (x,t,u) ->
     let t = subst s t in
     let x' = fresh_var () in
     let s = (x,Var x')::s in
     let u = subst s u in
     Pi (x',t,u)

(** Typing environment. *)
module Env = struct
  type t = (string * (expr option * expr)) list

  let to_string (env:t) =
    let f (x, (e, t)) =
      match e with
      | Some e ->
         let pad = String.make (String.length x) ' ' in
         Printf.sprintf "%s = %s\n%s : %s\n" x (to_string e) pad (to_string t)
      | None ->
         Printf.sprintf "%s : %s\n" x (to_string t)
    in
    String.concat "\n" (List.map f env)

  let empty : t = []

  let typ (env:t) x = snd (List.assoc x env)

  let value (env:t) x = fst (List.assoc x env)

  let add (env:t) x ?value t : t = (x,(value,t))::env
end

(** Normalize a value. *)
let rec normalize env = function
  | Var x ->
     begin
       try
         match Env.value env x with
         | Some e -> normalize env e
         | None -> Var x
       with
       | Not_found -> error "unknown identifier %s" x
     end
  | App (f, e) ->
     let f = normalize env f in
     let e = normalize env e in
     begin
       match f with
       | Abs (x,t,f) -> subst [x,e] f
       | _ -> App (f, e)
     end
  | Type n -> Type n
  | Pi (x,t,u) ->
     let t = normalize env t in
     let u = normalize (Env.add env x t) u in
     Pi (x,t,u)
  | Abs (x,t,e) ->
     let t = normalize env t in
     let e = normalize (Env.add env x t) e in
     Abs (x,t,e)
  | Obj -> Obj
  | Arr (f,g) ->
     let f = normalize env f in
     let g = normalize env g in
     Arr (f,g)
  | Coh (ps,t) ->
     let env, ps =
       List.fold_left
         (fun (env,ps) (x,t) ->
           let t = normalize env t in
           let ps = (x,t)::ps in
           let env = Env.add env x t in
           env,ps
         ) (env,[]) ps
     in
     let ps = List.rev ps in
     let t = normalize env t in
     Coh (ps,t)

(** Pasting schemes. *)
module PS = struct
  type t = ps

  let to_string ps =
    String.concat " " (List.map (fun (x,t) -> "(" ^ x ^ " : " ^ to_string t ^ ")") ps)

  (** Sort a list according to dependency order. *)
  let sort l =
    let lt (x,tx) (y,ty) =
      match ty with
      | Arr (x', _) when x = x' -> true
      | _ ->
         match tx with
         | Arr (_, y') when y' = y -> true
         | _ -> false
    in
    (* TODO *)let _ = lt in ()

  (** Check that a pasting scheme is well-formed. *)
  let check l =
    let x0,l =
      match l with
      | (x,t)::l ->
         assert (t = Obj);
         x,l
      | [] -> error "pasting scheme cannot be empty"
    in
    let marker = function
      | (f,_)::_ -> f
      | _ -> assert false
    in
    let drop ps =
      match ps with
      | (f, Arr(Var x, Var y))::_ -> (y, List.assoc x ps)::ps
      | _::_ -> assert false
      | [] -> assert false
    in
    let rec aux ps = function
      | (y,ty)::(f,tf)::l ->
         begin
           match tf with
           | Arr (Var fx, Var fy) ->
              assert (y = fy);
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
    aux [x0,Obj] l

  (** Free variables. *)
  let free_vars (ps:t) = List.map fst ps

  (** Dimensions of generators. *)
  let dims (ps:t) =
    let rec aux env = function
      | (x,Obj)::ps ->
         let env = (x,0)::env in
         aux env ps
      | (x,Arr (Var f, Var g))::ps ->
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
    let targets = List.map (fun (x,t) -> match t with Arr (Var f, Var g) -> g | _ -> assert false) targets in
    List.filter (fun (x,t) -> dim x < i || (dim x = i && not (List.mem x targets))) ps

  (** Target of a pasting scheme. *)
  let target i ps =
    assert (i >= 0);
    let dims = dims ps in
    let dim x = List.assoc x dims in
    let sources = List.filter (fun (x,t) -> dim x = i+1) ps in
    let sources = List.map (fun (x,t) -> match t with Arr (Var f, Var g) -> f | _ -> assert false) sources in
    List.filter (fun (x,t) -> dim x < i || (dim x = i && not (List.mem x sources))) ps
end

(** Type inference. *)
let rec infer_type env e =
  (* Printf.printf "env: %s\n" (String.concat " " (List.map fst env)); *)
  (* Printf.printf "infer_type: %s\n%!" (to_string e); *)
  match e with
  | Var x ->
     begin
       try
         Env.typ env x
       with
       | Not_found -> error "unknown identifier %s" x
     end
  | Type n -> Type (n+1)
  | Pi (x,t,u) ->
     let n1 = infer_univ env t in
     let n2 = infer_univ (Env.add env x t) u in
     Type (max n1 n2)
  | Abs (x,t,e) ->
     let u = infer_type (Env.add env x t) e in
     Pi (x,t,u)
  | App (f,e) ->
     let t = infer_type env f in
     let x,t,u =
       match t with
       | Pi (x,t,u) -> x,t,u
       | t -> error "got %s : %s, but a function is expected" (to_string f) (to_string t)
     in
     let t' = infer_type env e in
     if not (eq env t t') then error "got %s, but %s is expected" (to_string t') (to_string t);
     subst [x,e] u
  | Obj -> Type 0
  | Arr (f, g) ->
     let t = infer_type env f in
     let u = infer_type env g in
     begin
       match t, u with
       | Arr (x,y), Arr (x',y') ->
          if not (eq env x x' && eq env y y') then error "non parallel arrows"
       | Obj, Obj -> ()
       | (Arr _  | Obj ), (Arr _ | Obj) -> error "arrows of different dimension"
       | _ -> error "unexpected type for arrows"
     end;
     Type 0
  | Coh (ps,t) ->
     let env =
       List.fold_left
         (fun env (x,t) ->
           ignore (infer_univ env t);
           Env.add env x t
         ) env ps
     in
     ignore (infer_univ env t);
     PS.check ps;
     if not !groupoid then
       begin
         let f,g =
           match t with
           | Arr (f,g) -> f,g
           | _ -> assert false
         in
         let fv = PS.free_vars ps in
         let rec close_vars f =
           match infer_type env f with
           | Arr (x,y) -> List.union (close_vars x) (List.union (close_vars y) (free_vars f))
           | Obj -> free_vars f
           | _ -> assert false
         in
         let fvf = close_vars f in
         let fvg = close_vars g in
         if not (List.included fv fvf && List.included fv fvg) then
           begin
             let i = PS.dim ps in
             debug "checking decompositions";
             if i < 1
                || not (List.included (PS.free_vars (PS.source (i-1) ps)) fvf)
                || not (List.included (PS.free_vars (PS.target (i-1) ps)) fvg)
             then
               error "not algebraic";
           end;
       end;
     List.fold_right (fun (x,t) u -> Pi (x,t,u)) ps t

(** Type inference where a Type is expected. *)
and infer_univ env t =
  let u = infer_type env t in
  match normalize env u with
  | Type n -> n
  | u -> error "got %s, but type is expected" (to_string u)

(** Equality between expressions. *)
and eq env t1 t2 =
  let rec eq t1 t2 =
    match t1, t2 with
    | Var x1, Var x2 -> x1 = x2
    | Pi (x1,t1,u1), Pi (x2,t2,u2) -> eq t1 t2 && eq u1 (subst [x2,Var x1] u2)
    | Abs (x1,t1,e1), Abs (x2,t2,e2) -> eq t1 t2 && eq e1 (subst [x2,Var x1] e2)                               
    | App (f1,e1), App (f2,e2) -> eq f1 f2 && eq e1 e2
    | Type n1, Type n2 -> n1 = n2
    | Obj, Obj -> true
    | Arr (f1,g1), Arr (f2,g2) -> eq f1 f2 && eq g1 g2
    | Coh (ps1,t1), Coh (ps2,t2) ->
       List.length ps1 = List.length ps2
       && List.for_all2 (fun (x1,t1) (x2,t2) -> x1 = x2 && eq t1 t2) ps1 ps2
       && eq t1 t2
    | (Var _ | Abs _ | App _ | Type _ | Pi _ | Obj | Arr _ | Coh _), _ -> false
  in
  eq (normalize env t1) (normalize env t2)

(** A command. *)
type cmd =
  | Decl of string * expr
  | Set of string * string

(** A program. *)
type prog = cmd list

(** Execute a command. *)
let exec_cmd env = function
  | Decl (x,e) ->
     let t = infer_type env e in
     info "%s = %s\n    : %s" x (to_string e) (to_string t);
     let x' = fresh_var () in
     let env = Env.add env x' ~value:e t in
     let env = Env.add env x ~value:(Var x') t in
     env
  | Set (o,v) ->
     if o = "groupoid" then
       (* Switch groupoid mode. *)
       if v = "true" then groupoid := true
       else if v = "false" then groupoid := false
       else error "unknown value %s for option %s" v o
     else
       error "unknown option %s" o;
     env

(** Execute a program. *)
let exec env prog =
  List.fold_left exec_cmd env prog
