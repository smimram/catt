(** Main for CATT. *)

let parse_file f =
  let sin =
    let fi = open_in f in
    let flen = in_channel_length fi in
    let buf = Bytes.create flen in
    really_input fi buf 0 flen;
    close_in fi;
    buf
  in
  Prover.parse (Bytes.to_string sin)

let usage = "catt [options] [file]"
let interactive = ref false

let () =
  Printexc.record_backtrace true;
  let file_in = ref [] in
  Arg.parse
    [
      "-i", Arg.Set interactive, " Interactive mode."
    ]
    (fun s -> file_in := s::!file_in)
    usage;
  let envs = Lang.Envs.empty in
  let envs =
    match !file_in with
    | [f] -> Lang.exec envs (parse_file f)
    | _ -> envs
  in

  (* let ps = Parser.ps Lexer.token (Lexing.from_string "(x:*\)(y:*\)(f:x->y)(z:*\)(g:y->z)") in *)
  (* Lang.PS.check ps; *)
  (* let envps = Lang.Env.add_ps (fst envs) ps in *)
  (* let ps = LangExt.Subst.of_ps ps in *)
  (* let ss = LangExt.Subst.match_app envps ps (Lang.subst (snd envs) (Lang.Var (Lang.VIdent "id2"))) in *)
  (* print_endline ("len: "^string_of_int (List.length ss)); *)
  (* List.iter (fun ps -> print_endline (Lang.to_string ps)) ss; *)

  if !interactive then Prover.loop envs
