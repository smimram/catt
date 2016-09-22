module List = struct
  include List

  let remove x l =
    List.filter (fun y -> y <> x) l

  let included l1 l2 =
    List.for_all (fun x -> mem x l2) l1

  let union l1 l2 =
    List.fold_left (fun l x -> if not (mem x l) then x::l else l) l2 l1

  let bind f l =
    List.flatten (List.map f l)

  let bind_nd f =
    List.append (f true) (f false)
end
