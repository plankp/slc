open Ast
open Printf

module M = Map.Make (Int)

let rec collect_locals acc = function
  | LetFun (_, _, _, _, e) ->
    (* functions are not considered local, hence we don't look at the body *)
    collect_locals acc !e

  | LetCont (_, args, body, e) ->
    (* continuations are compiled as goto's, so everything is local *)
    collect_locals (collect_locals (List.rev_append args acc) !body) !e

  | LetProj (v, _, _, e)
  | LetPack (v, _, e) ->
    collect_locals (v :: acc) !e

  | Export _ | Jmp _ | App _ -> acc

  | _ -> failwith "UNHANDLED LOWERING"

let rec lower_function q f args k body =
  let buf = Buffer.create 32 in
  bprintf buf "void *v%d(" f;
  let () = match args with
    | [] -> ()
    | x :: xs ->
      bprintf buf "void *v%d" x;
      List.iter (bprintf buf ", void *v%d") xs in
  bprintf buf ") {\n";
  let () = match collect_locals [] !body with
    | [] -> ()
    | x :: xs ->
      bprintf buf "  void *v%d" x;
      List.iter (bprintf buf ", *v%d") xs;
      bprintf buf ";\n\n" in
  let (q, _) = lower_value q M.empty buf k !body in
  bprintf buf "}";
  buf :: q

and lower_value q kctx buf k = function
  | LetFun (f, args, k', body, e) ->
    let q = lower_function q f args k' body in
    lower_value q kctx buf k !e

  | LetCont (j, args, body, e) ->
    let kctx = M.add j args kctx in
    let (q, xs1) = lower_value q kctx buf k !e in
    bprintf buf "j%d:\n" j;
    let (q, xs2) = lower_value q kctx buf k !body in
    (q, List.rev_append xs2 xs1)

  | LetProj (v, i, t, e) ->
    bprintf buf "  v%d = ((void **) v%d)[%d];\n" v t i;
    lower_value q kctx buf k !e

  | LetPack (v, [], e) ->
    bprintf buf "  v%d = (void *) 0;\n" v;
    lower_value q kctx buf k !e

  | LetPack (v, elts, e) ->
    bprintf buf "  v%d = GC_MALLOC(%d * sizeof (void *));\n" v (List.length elts);
    List.iteri (fun i e ->
      bprintf buf "  ((void **) v%d)[%d] = v%d;\n" v i e) elts;
    lower_value q kctx buf k !e

  | Export xs ->
    List.iter (fun (n, v) ->
      bprintf buf "  G_%s = v%d;\n" n v) xs;
    (q, xs)

  | Jmp (j, [v]) when j = k ->
    bprintf buf "  return v%d;\n" v;
    (q, [])

  | Jmp (j, args) ->
    (* Jmp (j, [a1; a2; ...]) ~~>
     *
     * t1 = a1;   <-- copy is needed in case of screwy swapping loops
     * t2 = a2;
     * ...
     * p1 = t1;   <-- ps come from j
     * p2 = t2;
     * ...
     * goto j; *)
    bprintf buf "{\n";
    List.iteri (bprintf buf "  void *t%d = v%d;\n") args;
    let params = M.find j kctx in
    List.iteri (fun i p -> bprintf buf "  v%d = t%d;\n" p i) params;
    bprintf buf "  goto j%d;\n}\n" j;
    (q, [])

  | App (f, args, j) when j = k ->
    (* we cheat by using clang's musttail *)
    bprintf buf "  __attribute__((musttail)) return ((void *(*)(";
    let () = match args with
      | [] -> ()
      | _ :: xs ->
        bprintf buf "void *";
        List.iter (fun _ -> bprintf buf ", void *") xs in
    bprintf buf ")) v%d)(" f;
    let () = match args with
      | [] -> ()
      | x :: xs ->
        bprintf buf "v%d" x;
        List.iter (bprintf buf ", v%d") xs in
    bprintf buf ");\n";
    (q, [])

  | App (f, args, j) -> begin
    match M.find j kctx with
      | [p] ->
        bprintf buf "  v%d = ((void *(*)(" p;
        let () = match args with
          | [] -> ()
          | _ :: xs ->
            bprintf buf "void *";
            List.iter (fun _ -> bprintf buf ", void *") xs in
        bprintf buf ")) v%d)(" f;
        let () = match args with
          | [] -> ()
          | x :: xs ->
            bprintf buf "v%d" x;
            List.iter (bprintf buf ", v%d") xs in
        bprintf buf ");\n";
        bprintf buf "  goto j%d;\n" j;
        (q, [])

      | _ -> failwith "INVALID CONTINUATION ARITY"
  end

  | _ -> failwith "UNKNOWN VALUE TO LOWER"

let lower e =
  let _ = PassReindex.reindex e in
  match e with
    | Module m ->
      let buf = Buffer.create 32 in
      bprintf buf "void INIT(void) {\n";
      let () = match collect_locals [] !m with
        | [] -> ()
        | x :: xs ->
          bprintf buf "  void *v%d" x;
          List.iter (bprintf buf ", *v%d") xs;
          bprintf buf ";\n\n" in
      let q, gsym = lower_value [] M.empty buf ~-1 !m in
      bprintf buf "}";
      let q = List.rev_append q [buf] in

      printf "#include \"gc.h\"\n\n";
      let () = match gsym with
        | [] -> ()
        | (n, _) :: xs ->
          printf "void *G_%s" n;
          List.iter (fun (n, _) -> printf ", *G_%s" n) xs;
          printf ";\n\n" in
      List.iter (fun buf ->
        Buffer.output_buffer stdout buf;
        printf "\n\n") q

    | _ -> failwith "INVALID TERM ANCHOR"
