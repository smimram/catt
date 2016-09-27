module Enum = struct
  type 'a t = unit -> 'a

  exception End

  let empty : 'a t = fun () -> raise End

  let once x : 'a t =
    let dead = ref false in
    fun () -> if !dead then raise End else (dead := true; x)

  let get (e : 'a t) = e ()

  let map f e : 'a t = fun () -> f (get e)

  let rec may_map f e = fun () ->
    match f (get e) with
    | Some x -> x
    | None -> get (may_map f e)

  let rec filter f e = fun () ->
    let x = get e in
    if f x then x else get (filter f e)

  let append e1 e2 : 'a t =
    fun () ->
    try
      get e1
    with
    | End -> get e2

  let rec flatten e = fun () ->
    get (append (get e) (flatten e))

  let of_list l =
    let l = ref l in
    fun () ->
    match !l with
    | x::t -> l := t; x
    | [] -> raise End

  let rec to_list e =
    try
      let x = get e in
      x::(to_list e)
    with
    | End -> []
end

module List = struct
  include List

  let remove x l =
    filter (fun y -> y <> x) l

  let included l1 l2 =
    for_all (fun x -> mem x l2) l1

  let union l1 l2 =
    fold_left (fun l x -> if not (mem x l) then x::l else l) l2 l1

  let diff l1 l2 =
    filter (fun x -> not (mem x l2)) l1

  let bind f l =
    flatten (List.map f l)

  let bind_nd f =
    append (f true) (f false)
end

module Option = struct
  let map f = function
    | Some x -> Some (f x)
    | None -> None

  let default x = function
    | Some x -> x
    | None -> x
end
