open Slc

module type Transform = sig
  val transform : Hir.term -> unit
end

let transform_program program =
  let transforms : (string * (module Transform)) list =
    [ "Simplify", (module PassSimplify)
    ; "Arity", (module PassArity)
    ; "Simplify", (module PassSimplify)
    ; "Contification", (module PassContify)
    ; "Closure Conversion", (module PassCC)
    ] in

  print_endline "Original";
  Hir.dump program;
  print_endline "";
  print_endline "";

  List.iter (fun (name, (module T : Transform)) ->
    print_endline name;
    T.transform program;
    Hir.dump program;
    print_endline "";
    print_endline "") transforms;

  print_endline "Lower to LIR";
  let program = PassEmit.lower program in
  Lir.dump program;

  print_endline "Lower to x86-64";
  PassLower.lower program

let () =
  let lexbuf = Lexing.from_channel stdin in
  match Driver.parse Parser.Incremental.prog lexbuf with
    | Error e -> print_endline e
    | Ok m ->
      match Sem.check m with
        | Error e -> print_endline e
        | Ok ext ->
          Sem.M.iter (fun n t ->
            Printf.printf "val %s : %s\n" n (Type.to_string t)) ext;
          match Sem.lower m with
            | Error e -> print_endline e
            | Ok m -> transform_program m |> ignore
