let debug e = Printf.ksprintf (fun s -> Printf.printf "[DD]: %s.\n%!" s) e

let info e = Printf.ksprintf (fun s -> Printf.printf "[II]: %s.\n\n%!" s) e

(* let error e = Printf.ksprintf (fun s -> Printf.printf "[EE]: %s.\n%!" s; exit 1) e *)

let error e = Printf.ksprintf (fun s -> failwith s) e
         
