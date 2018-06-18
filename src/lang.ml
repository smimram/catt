(** Core part of the language. *)

open Stdlib
open Common

(** {2 Global options} *)

(** Do we want the theory of groupoids? *)
let groupoid = ref false
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
   | Type
   | HomType (** a type of hom set *)
   | Obj (** type of 0-cells *)
   | Arr of expr * expr * expr (** arrow type *)
   | Pi of var * expr * expr
   | Abs of var * expr * expr
   | App of expr * expr
   | Coh of string * ps * expr * int (** coherence (name, source, target, shifting) *)
   | Daimon (** of any type... *)

 (** A pasting scheme. *)
 and ps =
   | PNil of (var * expr) (** start *)
   | PCons of ps * (var * expr) * (var * expr) (** extend *)
   | PDrop of ps (** drop *)

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
  let pa s = if pa then "("^s^")" else s in
  match e.desc with
  | Var x -> string_of_var x
  | Type -> "Type"
  | HomType -> "HomType"
  | Obj -> "*"
  | Arr (t,f,g) -> pa (Printf.sprintf "%s | %s -> %s" (to_string false t) (to_string false f) (to_string false g))
  | Coh (c,ps,t,n) ->
     if c = "" then
       Printf.sprintf "coh%d (%s => %s)" n (string_of_ps ps) (to_string false t)
     else
       c
  | Pi (x,t,u) -> pa (Printf.sprintf "(%s : %s) => %s" (string_of_var x) (to_string false t) (to_string false u))
  | Abs (x,t,e) -> pa (Printf.sprintf "\\(%s : %s) => %s" (string_of_var x) (to_string false t) (to_string false e))
  | App (f,e) -> pa (to_string false f ^ " " ^ to_string true e)
  | Daimon -> "†"

(** String representation of a pasting scheme. *)
and string_of_ps = function
  | PNil (x,t) -> Printf.sprintf "(%s : %s)" (string_of_var x) (to_string t)
  | PCons (ps,(x,t),(y,u)) -> Printf.sprintf "%s (%s : %s) (%s : %s)" (string_of_ps ps) (string_of_var x) (to_string t) (string_of_var y) (to_string u)
  | PDrop ps -> string_of_ps ps ^ " ! "

(** Pasting schemes. *)
module PS = struct
  (** A pasting scheme. *)
  type t = ps

  (** String representation. *)
  let to_string = string_of_ps

  exception Invalid

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
       | _ -> raise Invalid

  (** Free variables. *)
  let rec free_vars = function
    | PNil (x,t) -> [x]
    | PCons (ps,(y,_),(f,_)) -> f::y::(free_vars ps)
    | PDrop ps -> free_vars ps

  (** Height of a pasting scheme. *)
  let rec height = function
    | PNil _ -> 0
    | PCons (ps,_,_) -> height ps + 1
    | PDrop ps -> height ps - 1

  (** Create from a context. *)
  let make l : t =
    (* Printf.printf "make: %s\n%!" (String.concat_map " " (fun (x,t) -> Printf.sprintf "(%s : %s)" (string_of_var x) (string_of_expr t)) l); *)
    let x0,t0,l =
      match l with
      | (x,t)::l ->
         if t.desc <> Obj then error ~pos:t.pos "pasting scheme must begin with *";
         x,t,l
      | [] -> error "pasting scheme cannot be empty"
    in
    let rec aux ps = function
      | (y,ty)::(f,tf)::l ->
         begin
           try
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
           with
           | Invalid ->
              (* TODO: better position *)
              error ~pos:tf.pos "not a pasting scheme"
         end
      | [x,tx] -> error ~pos:tx.pos "not a pasting scheme (invalid parity)"
      | [] -> ps
    in
    let ps = aux (PNil(x0,t0)) l in
    let ps = ref ps in
    while height !ps > 0 do ps := PDrop !ps done;
    !ps

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

  (** Maxima of the pasting scheme. *)
  let max = function
    | PNil x -> [x]
    | ps ->
      let rec aux = function
        | PNil x -> []
        | PDrop (PCons (ps,y,f)) -> f::(aux ps)
        | PDrop ps -> aux ps
        | PCons (ps,_,_) -> aux ps
      in
      aux ps

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
    | Type -> Type
    | HomType -> HomType
    | Obj -> Obj
    | Arr (t,x,y) -> Arr (subst s t, subst s x, subst s y)
    | Coh (c,ps,t,n) ->
       let s = ref s in
       let ps =
         PS.map
           (fun (x,t) ->
             let x' = fresh_var x in
             let t = subst !s t in
             s := (x,mk (Var x')) :: !s;
             x',t
           ) ps
       in
       let t = subst !s t in
       Coh (c,ps,t,n)
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
    | Daimon -> Daimon
  in
  mk ~pos:e.pos desc

(** Free variables. *)
let rec free_vars e =
  (* Printf.printf "free_vars: %s\n%!" (to_string e); *)
  match e.desc with
  | Var x -> [x]
  | Type | HomType | Obj -> []
  | Arr (t,f,g) -> (free_vars t)@(free_vars f)@(free_vars g)
  | App (f,x) -> (free_vars f)@(free_vars x)
  | Pi (x,t,u) -> (free_vars t)@(List.remove x (free_vars u))
  | Abs (x,t,e) -> (free_vars t)@(List.remove x (free_vars e))
  | Coh (c,ps,t,n) -> PS.fold_right (fun (x,t) l -> (free_vars t)@List.remove x l) ps (free_vars t)
  | Daimon -> assert false

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

(** {2 Reduction and typing} *)

(** Normalize a value. *)
let rec normalize env e =
  (* Printf.printf "normalize: %s\n%!" (to_string e); *)
  let desc =
    match e.desc with
    | Var x ->
       begin
         try
           match Env.value env x with
           | Some e -> (normalize env e).desc
           | None -> Var x
         with
         | Not_found -> error ~pos:e.pos "unknown identifier %s" (string_of_var x)
       end
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
    | Coh (c,ps,t,n) ->
       let env = ref env in
       let ps =
         PS.map
           (fun (x,t) ->
             let t = normalize !env t in
             env := Env.add !env x t;
             x,t
           ) ps
       in
       let t = normalize !env t in
       Coh (c,ps,t,n)
    | Arr (t,f,g) ->
       let t = normalize env t in
       let f = normalize env f in
       let g = normalize env g in
       Arr (t,f,g)
    | Daimon -> Daimon
  in
  mk ~pos:e.pos desc

(** Type inference. *)
let rec infer_type env e =
  (* Printf.printf "env: %s\n" (String.concat " " (List.map fst env)); *)
  (* Printf.printf "infer_type: %s\n%!" (to_string e); *)
  (* let infer_type env e = *)
  (* let t = infer_type env e in *)
  (* Printf.printf "infer_type: %s : %s\n%!" (to_string e) (to_string t); *)
  (* t *)
  (* in *)
  let desc, t =
    match e.desc with
    | Var x ->
       begin
         try
           Var x, Env.typ env x
         with
         | Not_found -> error ~pos:e.pos "unknown identifier %s" (string_of_var x)
       end
    | Type -> Type, mk Type
    | Pi (x,t,u) ->
       let t = check_type env t (mk Type) in
       let u = check_type (Env.add env x t) u (mk Type) in
       Pi (x,t,u), mk Type
    | Abs (x,t,e) ->
       let t = check_type env t (mk Type) in
       let e,u = infer_type (Env.add env x t) e in
       Abs (x,t,e), mk (Pi (x,t,u))
    (* | App (Coh(c,ps,t,0),e) -> *)
    | App (f,e) ->
       let f,t = infer_type env f in
       let x,t,u =
         match t.desc with
         | Pi (x,t,u) -> x,t,u
         | _ -> error ~pos:f.pos "got %s : %s, but a function is expected" (to_string f) (to_string t)
       in
       let e,te = infer_type env e in
       if not (leq env te t) then error ~pos:e.pos "got %s, but %s is expected" (to_string te) (to_string t);
       App(f,e), subst [x,e] u
    | HomType -> HomType, mk Type
    | Obj -> Obj, mk HomType
    | Coh (c,ps,t,n) ->
       assert (n = 0);
       (* Normalize types in order to reveal hidden variables. *)
       let env = ref env in
       let ps =
         PS.map
           (fun (x,t) ->
             let t = normalize !env t in
             let t = check_type !env t (mk HomType) in
             env := Env.add !env x t;
             x,t
           ) ps
       in
       let env = !env in
       let t = normalize env t in
       let t = check_type env t (mk HomType) in
       (* Printf.printf "COH: %s\n%!" (to_string (mk (Coh(c,ps,t)))); *)
       (* Printf.printf "env:\n\n%s\n%!" (Env.to_string env); *)
       (* Printf.printf "type: %s\n%!" (to_string t); *)
       (* Printf.printf "type: %s\n%!" (to_string (normalize env t)); *)
       (* debug "check pasting scheme %s" (PS.to_string ps); *)
       if not !groupoid then
         begin
           let f,g =
             match t.desc with
             | Arr (_,f,g) -> f,g
             | _ -> assert false
           in
           let fv = PS.free_vars ps in
           (*
           let rec close_vars f =
             match (infer_type env f).desc with
             | Arr (_,x,y) -> List.union (close_vars x) (List.union (close_vars y) (free_vars f))
             | t ->
                (* if not !parametric_schemes then assert (t = Obj); *)
                (* TODO: shift!! *)
                assert (t = Obj);
                free_vars f
           in
           let fvf = close_vars f in
           let fvg = close_vars g in
            *)
           (* TODO..... *)
           let fvf = [] in
           let fvg = [] in
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
                 error ~pos:t.pos "not algebraic: %s not used in %s" bad (to_string (mk (Coh (c,ps,t,n))));
             end;
         end;
    (* PS.fold_right (fun (x,t) u -> mk (Pi (x,t,u))) ps t *)
       assert false
    | Arr ({desc = Daimon}, f, g) ->
       let f, t = infer_type env f in
       let g = check_type env g t in
       Arr (t,f,g), mk HomType
    | Arr (t,f,g) ->
       let t = check_type env t (mk HomType) in
       let f = check_type env f t in
       let g = check_type env g t in
       Arr (t,f,g), mk HomType
    | Daimon -> assert false
  in
  { desc; pos = e.pos }, t

(** Check that an expression has given type. *)
and check_type env e t =
  let e, te = infer_type env e in
  if not (leq env te t) then error ~pos:e.pos "got %s, but %s is expected" (to_string te) (to_string t);
  e

(** Subtype relation between expressions. *)
and leq env e1 e2 =
  let rec leq e1 e2 =
    (* Printf.printf "leq\n%s\n%s\n\n" (to_string e1) (to_string e2); *)
    match e1.desc, e2.desc with
    | Var x1, Var x2 -> x1 = x2
    | Pi (x1,t1,u1), Pi (x2,t2,u2) -> leq t2 t1 && leq u1 (subst [x2,mk (Var x1)] u2)
    | Abs (x1,t1,e1), Abs (x2,t2,e2) -> leq t2 t1 && leq e1 (subst [x2,mk (Var x1)] e2)
    | App (f1,e1), App (f2,e2) -> leq f1 f2 && leq e1 e2
    | Type, Type -> true
    | HomType, HomType -> true
    | HomType, Type -> true
    | Obj, Obj -> true
    | Coh(_,ps1,t1,n1), Coh(_,ps2,t2,n2) ->
       (*
       let rec aux l1 s l2 =
         match l1,l2 with
         | [],[] -> leq t1 (subst s t2)
         | (x1,t1)::l1, (x2,t2)::l2 ->
            let t2 = subst s t2 in
            let s = (x2,mk (Var x1))::s in
            leq t1 t2 && aux l1 s l2
         | _ -> false
       in
       aux ps1 [] ps2
        *)
       let s = ref [] in
       let ans =
         PS.fold_left2
           (fun ans (x1,t1) (x2,t2) ->
             let t2 = subst !s t2 in
             s := (x2,mk (Var x1)) :: !s;
             ans && leq t1 t2
           ) true ps1 ps2
       in
       n1 = n2 && ans && leq t1 (subst !s t2)
    | Arr (t1,f1,g1), Arr (t2,f2,g2) -> leq t1 t2 && leq f1 f2 && leq g1 g2
    | (Var _ | Abs _ | App _ | Type | HomType | Pi _ | Obj | Arr _ | Coh _), _ -> false
    | Daimon, _ -> assert false
  in
  leq (normalize env e1) (normalize env e2)

(** {2 Programs} *)

(** A command. *)
type cmd =
  | Decl of var * expr (** Declare a variable. *)
  | Axiom of var * expr (** Declare an axiom of given type. *)
  | Check of expr (** Check the type of an expression. *)
  | Eval of expr (** Evaluate an expression. *)
  | Env (** Display the environment. *)
  | Set of string * string (** Set an option. *)

(** String representation of a command. *)
let string_of_cmd = function
  | Decl (x,e) -> Printf.sprintf "let %s = %s" (string_of_var x) (to_string e)
  | Axiom (x,e) -> Printf.sprintf "ax %s : %s" (string_of_var x) (to_string e)
  | Check e -> Printf.sprintf "check %s" (to_string e)
  | Eval e -> Printf.sprintf "eval %s" (to_string e)
  | Set (x,v) -> Printf.sprintf "set %s = %s" x v
  | Env -> "env"

(** A program. *)
type prog = cmd list

(** Running environment. *)
module Envs = struct
  (** A running environment. *)
  type t = Env.t * subst

  (** Empty running environment. *)
  let empty : t = Env.empty, []
end

(** Execute a command. *)
let exec_cmd ((env,s):Envs.t) cmd : Envs.t =
  command "%s" (string_of_cmd cmd);
  match cmd with
  | Decl (x,e) ->
     let e = subst s e in
     let e, t = infer_type env e in
     let x' = fresh_var x in
     info "%s = %s\n    : %s" (string_of_var x') (to_string e) (to_string t);
     let env = Env.add env x' ~value:e t in
     let s = (x,mk (Var x'))::s in
     env,s
  | Axiom (x,t) ->
     let t = subst s t in
     let x' = fresh_var x in
     let t = check_type env t (mk Type) in
     let env = Env.add env x' t in
     let s = (x,mk (Var x'))::s in
     env,s
  | Check e ->
     let e = subst s e in
     let e, t = infer_type env e in
     printf "%s\n%!" (to_string t);
     env,s
  | Eval e ->
     let e = subst s e in
     let e0 = e in
     let e = normalize env e in
     let e, t = infer_type env e in
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
