open Slc
open Printf

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

let stop_after f =
  f ();
  exit 0

type source_module =
  { name : string
  ; mutable prog : Ast.prog option
  ; mutable defn : Sem.modsig_t option
  }

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
        let m = { name; prog = None; defn = None } in
        let v = Tarjan.new_vertex m in
        Hashtbl.add g name v;
        v in

  (* parse + construct dependency graph (of the modules) *)

  List.iter (fun filename ->
    match get_module_name filename with
      | None ->
        stop_after (fun () ->
          printf "File name does not begin with a valid module name: %s\n" filename)
      | Some mname ->
        let chan = In_channel.open_text filename in
        let lbuf = Lexing.from_channel chan in
        Lexing.set_filename lbuf filename;

        let result = Driver.parse Parser.Incremental.prog lbuf in
        In_channel.close_noerr chan;
        match result with
          | Error e ->
            stop_after (fun () ->
              printf "Error in module %s:\n%s\n" mname e)
          | Ok m ->
            let node = fetch_module_map mname in
            let info = Tarjan.get_info node in
            if info.prog <> None then
              stop_after (fun () ->
                printf "Module %s appears in the list of files multiple times\n" mname);
            info.prog <- Some m;
            let deps = Sem.resolve_module_deps m in
            if Sem.S.mem mname deps then
              stop_after (fun () ->
                printf "Error in module %s:\nIt explicitly references itself and it shouldn't\n" mname);
            Sem.S.iter (fun dep ->
              let needs = fetch_module_map dep in
              Tarjan.add_edge node needs) deps) input_files;

  (* a module node may either be:
   * -  explicitly present (as all file names listed should)
   * -  implicitly present (say library Option is used by input file Foo.sl)
   *)

  let () = match !entry_module with
    | None -> ()
    | Some m ->
      let fail () =
        stop_after (fun () ->
          printf "Entry module %s is not (explicitly) present during compilation\n" m) in
      let node = Hashtbl.find_opt g m in
      match node with
        | None -> fail ()
        | Some node ->
          let info = Tarjan.get_info node in
          if info.prog = None then fail ()
          else
            (* being the entry means to be initialized last (and no one
             * depends on it). we represent this by adding dependence edges to
             * every other module *)
            Hashtbl.iter (fun _ other ->
              if other != node then
                Tarjan.add_edge node other) g in

  let scc = g |> Hashtbl.to_seq_values |> Tarjan.compute_scc in
  let scc = List.fold_left (function
    | x :: (_ :: _ as xs) ->
      (* we must have some sort of circular dependency *)
      stop_after (fun () ->
        printf "Error in module %s\n" (Tarjan.get_info x).name;
        printf "It forms a circular dependency with %d other module(s)\n" (List.length xs))
    | [x] -> fun xs -> x :: xs
    | [] -> fun x -> x) [] scc in
  let scc = List.rev scc in

  (* compute the module signature in dependency graph order *)
  let lookup_modsig name =
    let m = Hashtbl.find g name in
    let m = Tarjan.get_info m in
    Option.get m.defn in

  List.iter (fun node ->
    let info = Tarjan.get_info node in
    match info.prog with
      | None ->
        (* TODO: obtain the signature of a precompiled module *)
        failwith "TODO: Support precompiled modules"
      | Some m ->
        match Sem.check lookup_modsig m with
          | exception Failure e | Error e ->
            stop_after (fun () ->
              printf "Error in module %s\n%s\n" info.name e)
          | Ok exports ->
            info.defn <- Some exports) scc;

  let scc = List.map (fun node ->
    let info = Tarjan.get_info node in
    match info.prog with
      | None -> (info.name, None)
      | Some m ->
        match Sem.lower m with
          | exception Failure e | Error e ->
            stop_after (fun () ->
              printf "Error in module %s\n%s\n" info.name e)
          | Ok m -> (info.name, Some m)) scc in

  List.iter (fun (mname, m) ->
    match m with
      | None -> ()
      | Some m -> transform_program mname m) scc;

  if !entry_module <> None then begin
    let chan = Out_channel.open_text ("_driver.s") in
    PassLower.emit_driver chan (scc
      |> List.to_seq
      |> Seq.map (fun (n, _) ->
        PassEmit.mangle_globl_name n "INIT"));
    Out_channel.close_noerr chan
  end
