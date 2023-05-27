open Slc
open Printf

module M = Map.Make (String)

let usage_msg = "slc <options> <files>"

let input_files = ref []

(* ordinary flags *)
let entry_module = ref None
let entry_module_setter v =
  entry_module := Some v

let module_lookup_dirs = ref []
let module_lookup_dirs_setter v =
  module_lookup_dirs := v :: !module_lookup_dirs

(* internal flags (-X prefixed) *)
let dump_hir = ref false
let dump_lir = ref false

let anon_fun filename =
  input_files := filename :: !input_files

let speclist =
  [ ("-entry", Arg.String entry_module_setter, "Mark a module as an entry point")
  ; ("-I", Arg.String module_lookup_dirs_setter, "Include a directory when searching for modules")
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
    ; "Simplify", (module PassSimplify)
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

  let prog = PassEmit.lower mname prog in

  if !dump_lir then begin
    print_endline "Lower to LIR";
    Lir.dump prog
  end;

  let chan = Out_channel.open_text (mname ^ ".s") in
  PassLower.lower chan prog;
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

let find_moddir_file fname =
  let rec loop = function
    | [] -> None
    | dir :: xs ->
      let fname = Filename.concat dir fname in
      if Sys.file_exists fname then Some fname
      else loop xs in
  loop !module_lookup_dirs

let stop_after f =
  f ();
  exit 0

type walkstate =
  | Pending
  | Processing
  | Done

type source_module =
  { name : string
  ; mutable walk : walkstate
  ; mutable inpt : bool
  ; mutable prog : Ast.prog option
  ; mutable defn : Sem.modsig_t option
  }

let parse_sl_file filename =
  let chan = In_channel.open_text filename in
  let lbuf = Lexing.from_channel chan in
  Lexing.set_filename lbuf filename;

  let result = Driver.parse Parser.Incremental.prog lbuf in
  In_channel.close_noerr chan;
  result

let () =
  Arg.parse speclist anon_fun usage_msg;

  let input_files =
    let v = !input_files in
    input_files := [];  (* garbage collection hint? *)
    v in

  let g = Hashtbl.create 32 in
  let fetch_module_map name =
    match Hashtbl.find_opt g name with
      | Some v -> v
      | None ->
        let v = { name; walk = Pending
                ; inpt = false; prog = None; defn = None
                } in
        Hashtbl.add g name v;
        v in

  (* process the file list *)
  let pending = List.rev_map (fun filename ->
    let fail () =
      stop_after (fun () ->
        let filename = Filename.basename filename in
        printf "File name does not conform to a valid input file name: %s\n" filename) in
    if Filename.extension filename <> ".sl" then fail ()
    else
      match get_module_name filename with
        | None -> fail ()
        | Some mname ->
          let result = parse_sl_file filename in
          match result with
            | Error e ->
              stop_after (fun () ->
                printf "Error in module %s:\n%s\n" mname e)
            | Ok m ->
              let node = fetch_module_map mname in
              if node.prog <> None then
                stop_after (fun () ->
                  printf "Module %s appears in the list of files multiple times\n" mname);
              node.inpt <- true;
              node.prog <- Some m;
              node
      ) input_files in

  (* perform DFS to obtain the dependencies and the initialization order *)
  let rec dfs_walk acc = function
    | [] -> acc
    | { walk = Done; _ } :: xs -> dfs_walk acc xs
    | { walk = Processing; name; _ } :: _ ->
      stop_after (fun () ->
        printf "Error in module %s\nIt forms a circular dependency\n" name)
    | x :: xs ->
      let acc = collect_deps acc [] x in
      dfs_walk acc xs

  and collect_deps acc deps node =
    node.walk <- Processing;
    let m = match node.prog with
      | Some m -> m
      | None ->
        match find_moddir_file (node.name ^ ".sl") with
          | None ->
            stop_after (fun () ->
              printf "Cannot find external module %s\n" node.name)
          | Some filename ->
            let result = parse_sl_file filename in
            match result with
              | Error e ->
                stop_after (fun () ->
                  printf "Error in module %s:\n%s\n" node.name e)
              | Ok m ->
                node.prog <- Some m;
                m in

    (* traverse the dependencies *)
    let s = Sem.resolve_module_deps m in
    let acc = deps
      |> Sem.S.fold (fun dep acc -> fetch_module_map dep :: acc) s
      |> dfs_walk acc in

    node.walk <- Done;
    node :: acc in

  let init_order = match !entry_module with
    | None -> dfs_walk [] pending
    | Some m ->
      let node = Hashtbl.find_opt g m in
      match node with
        | None ->
          stop_after (fun () ->
            printf "Entry module %s is not (explicitly) present during compilation\n" m)
        | Some node ->
          (* if there is an entry point, then we need to make sure it is
           * initialized last / it depends on all other modules *)
          let deps = Hashtbl.fold (fun _ other acc ->
            if other == node then acc else other :: acc) g [] in
          collect_deps [] deps node in
  let init_order = List.rev init_order in

  (* compute the modules in initialization order *)
  let lookup_modsig name =
    let m = Hashtbl.find g name in
    Option.get m.defn in

  List.iter (fun node ->
    let m = Option.get node.prog in
    match Sem.check lookup_modsig m with
      | exception Failure e | Error e ->
        stop_after (fun () ->
          printf "Error in module %s\n%s\n" node.name e)
      | Ok exports ->
        node.defn <- Some exports) init_order;

  Hashtbl.reset g; (* garbage collection hint? *)

  let init_order = List.map (fun node ->
    if not node.inpt then (node.name, None)
    else
      match Sem.lower (Option.get node.prog) with
        | exception Failure e | Error e ->
          stop_after (fun () ->
            printf "Error in module %s\n%s\n" node.name e)
        | Ok m -> (node.name, Some m)) init_order in

  List.iter (fun (name, m) ->
      match m with
        | None -> ()
        | Some m -> transform_program name m) init_order;

  if !entry_module <> None then begin
    let chan = Out_channel.open_text ("_driver.s") in
    PassLower.emit_driver chan (init_order
      |> List.to_seq
      |> Seq.map (fun (n, _) ->
        PassEmit.mangle_globl_name n "INIT"));
    Out_channel.close_noerr chan
  end
