open Slc

module M = Map.Make (String)

let usage_msg = "slc <options> <files>"

let input_files = ref []

(* ordinary flags *)
let entry_module = ref None
let entry_module_setter v =
  entry_module := Some v

(* internal flags (-X prefixed) *)
let dump_hir = ref false
let dump_lir = ref false

let anon_fun filename =
  input_files := filename :: !input_files

let speclist =
  [ ("-entry", Arg.String entry_module_setter, "Mark a module as an entry point")
  ; ("-Xdump-hir", Arg.Set dump_hir, "Dump HIR (for debugging purposes)")
  ; ("-Xdump-lir", Arg.Set dump_lir, "Dump LIR (for debugging purposes)")
  ]

module type Transform = sig
  val transform : Hir.term -> unit
end

let transform_program mname prog =
  let transforms : (string * (module Transform)) list =
    [ "Simplify", (module PassSimplify)
    ; "Arity", (module PassArity)
    ; "Simplify", (module PassSimplify)
    ; "Contification", (module PassContify)
    ; "Closure Conversion", (module PassCC)
    ] in

  if !dump_hir then begin
    print_endline "Original";
    Hir.dump prog;
    print_endline "";
    print_endline "";
  end;

  List.iter (fun (name, (module T : Transform)) ->
    T.transform prog;
    if !dump_hir then begin
      print_endline name;
      Hir.dump prog;
      print_endline "";
      print_endline ""
    end) transforms;

  let prog = PassEmit.lower prog in

  if !dump_lir then begin
    print_endline "Lower to LIR";
    Lir.dump prog
  end;

  let chan = Out_channel.open_text (mname ^ ".s") in
  let is_entry = match !entry_module with
    | Some name when name = mname -> true
    | _ -> false in
  PassLower.lower ~is_entry chan prog;
  Out_channel.close_noerr chan

let get_module_name fname =
  try
    let start = fname
      |> Filename.basename
      |> Filename.remove_extension in

    (* it has to be a UNAME following lexical analysis *)
    let lbuf = Lexing.from_string start in
    match Lexer.read lbuf with
      | Parser.UNAME name -> begin
        match Lexer.read lbuf with
          | Parser.EOF -> Some name
          | _ -> None
      end
      | _ -> None
  with _ -> None

let () =
  Arg.parse speclist anon_fun usage_msg;

  let modules = List.map (fun filename ->
    match get_module_name filename with
      | None ->
        failwith ("File name is not resolve in a valid module name: " ^ filename)
      | Some mname ->
        let chan = In_channel.open_text filename in
        let lbuf = Lexing.from_channel chan in
        Lexing.set_filename lbuf filename;

        let result = Driver.parse Parser.Incremental.prog lbuf in
        In_channel.close_noerr chan;
        (mname, result)) !input_files in

  let modules = List.map (fun (mname, m) ->
    (mname, Result.bind m (fun m ->
      try
        Result.bind (Sem.check m) (fun export ->
          Result.bind (Sem.lower m) (fun m ->
            Ok (m, export)))
      with Failure e -> Error e))) modules in

  let (modules, errored) = List.fold_left (fun (map, flag) (mname, m) ->
    match m with
      | Error e ->
        Printf.printf "Error in module %s:\n" mname;
        Printf.printf "%s\n" e;
        (M.empty, true)
      | Ok (m, export) ->
        (M.add mname (m, export) map, flag)) (M.empty, false) modules in

  if not errored then begin
    match !entry_module with
      | Some v when not (M.mem v modules) ->
        Printf.printf "Entry module %s is not present\n" v
      | _ ->
        M.iter (fun mname (m, _) ->
          transform_program mname m) modules
  end
