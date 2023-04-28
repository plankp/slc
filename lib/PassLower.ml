open Hir
open Printf

module M = Map.Make (Int)

let rec lower_function q f args k h body id =
  let buf = Buffer.create 32 in
  bprintf buf "define tailcc ptr @f%d(" f;
  let sv = match args with
    | [] -> M.empty
    | x :: xs ->
      bprintf buf "ptr %%v%d" x;
      let sv = M.singleton x (sprintf "%%v%d" x) in
      List.fold_left (fun sv x ->
        bprintf buf ", ptr %%v%d" x;
        M.add x (sprintf "%%v%d" x) sv) sv xs in
  bprintf buf ") personality ptr @__gxx_personality_v0 {\n";
  bprintf buf "_0:\n";
  let (q, id) = lower_value q "_0" (Some k) (Some h) sv M.empty id buf !body in
  bprintf buf "}";
  buf :: q, id

and lower_value q label k h sv sk id buf = function
  | LetFun ((f, args, k', h', body), e) ->
    let (q, id) = lower_function q f args k' h' body id in
    lower_value q label k h (M.add f (sprintf "@f%d" f) sv) sk id buf !e

  | LetCont (bs, e) ->
    let sk = List.fold_left (fun sk (j, args, _) ->
      let slots = List.map (fun _ -> ref []) args in
      M.add j slots sk) sk bs in
    let (q, id) = lower_value q label k h sv sk id buf !e in
    let (xs, q, id) = List.fold_left (fun (xs, q, id) (j, args, body) ->
      let buf = Buffer.create 32 in
      let sv = List.fold_left (fun sv a ->
        M.add a (sprintf "%%v%d" a) sv) sv args in
      let (q, id) = lower_value q (sprintf "k%d" j) k h sv sk id buf !body in
      ((j, args, buf) :: xs, q, id)) ([], q, id) bs in

    List.iter (fun (j, args, blq) ->
      bprintf buf "k%d:\n" j;
      List.iter2 (fun a p ->
        bprintf buf "  %%v%d = phi ptr" a;
        let () = match !p with
          | [] -> ()  (* shouldn't happen *)
          | (v, j) :: xs ->
            bprintf buf " [%s, %%%s]" v j;
            List.iter (fun (v, j) ->
              bprintf buf ", [%s, %%%s]" v j) xs in
        bprintf buf "\n") args (M.find j sk);
      Buffer.add_buffer buf blq) xs;
    (q, id)

  | LetPack (v, [], e) ->
    (* we use NULL for this *)
    lower_value q label k h (M.add v "null" sv) sk id buf !e

  | LetPack (v, elts, e) ->
    let width = List.length elts |> Int64.of_int |> Int64.mul 8L in
    bprintf buf "  %%v%d = call ptr @GC_MALLOC(i64 noundef %Ld)\n" v width;
    let (id, _) = List.fold_left (fun (id, i) e ->
      bprintf buf "  %%v%d.%Lu = getelementptr ptr, ptr %%v%d, i64 %d\n" v id v i;
      bprintf buf "  store ptr %s, ptr %%v%d.%Lu\n" (M.find e sv) v id;
      (Int64.succ id, i + 1)) (id, 0) elts in
    lower_value q label k h (M.add v (sprintf "%%v%d" v) sv) sk id buf !e

  | LetCons (v, i, elts, e) ->
    (* 32-bit tag + a 64-bit pointer for each element *)
    let width = List.length elts |> Int64.of_int |> Int64.mul 8L in
    let width = if width = 0L then 4L else Int64.add width 8L in
    bprintf buf "  %%v%d = call ptr @GC_MALLOC(i64 noundef %Ld)\n" v width;
    bprintf buf "  %%v%d.t = getelementptr i32, ptr %%v%d, i64 0\n" v v;
    bprintf buf "  store i32 %d, ptr %%v%d.t\n" i v;
    let (id, _) = List.fold_left (fun (id, i) e ->
      bprintf buf "  %%v%d.%Lu = getelementptr ptr, ptr %%v%d, i64 %d\n" v id v i;
      bprintf buf "  store ptr %s, ptr %%v%d.%Lu\n" (M.find e sv) v id;
      (Int64.succ id, i + 1)) (id, 1) elts in
    lower_value q label k h (M.add v (sprintf "%%v%d" v) sv) sk id buf !e

  | LetProj (v, i, t, e) ->
    bprintf buf "  %%v%d.%Lu = getelementptr ptr, ptr %s, i64 %d\n" v id (M.find t sv) i;
    bprintf buf "  %%v%d = load ptr, ptr %%v%d.%Lu\n" v v id;
    lower_value q label k h (M.add v (sprintf "%%v%d" v) sv) sk (Int64.succ id) buf !e

  | Export xs ->
    List.iter (fun (n, v) ->
      bprintf buf "  store ptr %s, ptr @G_%s, align 8\n" (M.find v sv) n) xs;
    q, id

  (* return *)
  | Jmp (j, [v]) when k = Some j ->
    bprintf buf "  ret ptr %s\n" (M.find v sv);
    q, id

  (* throw / raise an exception *)
  | Jmp (j, [v]) when h = Some j ->
    bprintf buf "  %%q.%Lu = call ptr @__cxa_allocate_exception(i64 8)\n" id;
    bprintf buf "  store ptr %s, ptr %%q.%Lu\n" (M.find v sv) id;
    bprintf buf "  call void @__cxa_throw(ptr %%q.%Lu, ptr @_ZTIPv, ptr null)\n" id;
    bprintf buf "  unreachable\n";
    q, Int64.succ id

  (* goto / branch to block *)
  | Jmp (j, args) ->
    let params = M.find j sk in
    List.iter2 (fun p a -> p := (M.find a sv, label) :: !p) params args;
    bprintf buf "  br label %%k%d\n" j;
    q, id

  | Case (v, cases) ->
    let v = M.find v sv in
    bprintf buf "  %%tag.%Lu = load i32, ptr %s\n" id v;
    bprintf buf "  switch i32 %%tag.%Lu, label %%case.%Lu.else [\n" id id;
    let has_default = ref false in
    Hir.M.iter (fun i _ ->
      match i with
        | Some i -> bprintf buf "    i32 %d, label %%case.%Lu.%d\n" i id i
        | _ -> has_default := true) cases;
    bprintf buf "  ]\n";

    if not !has_default then begin
      (* assume a lack of explicit default case means it is unreachable! *)
      bprintf buf "case.%Lu.else:\n" id;
      bprintf buf "  unreachable\n"
    end;
    let id = Hir.M.fold (fun i j fresh ->
      let label = match i with
        | Some i -> sprintf "case.%Lu.%d" id i
        | _ -> sprintf "case.%Lu.else" id in
      bprintf buf "%s:\n" label;

      (* like in Jmp, handle the three possibilities *)
      if Some j = k then begin
        bprintf buf "  %%q.%Lu.p = getelementptr ptr, ptr %s, i64 1\n" fresh v;
        bprintf buf "  %%q.%Lu.v = load ptr, ptr %%q.%Lu.p\n" fresh fresh;
        bprintf buf "  ret ptr %%q.%Lu.v" fresh;
        Int64.succ fresh
      end else if Some j = h then begin
        bprintf buf "  %%q.%Lu.p = getelementptr ptr, ptr %s, i64 1\n" fresh v;
        bprintf buf "  %%q.%Lu.v = load ptr, ptr %%q.%Lu.p\n" fresh fresh;
        bprintf buf "  %%q.%Lu = call ptr @__cxa_allocate_exception(i64 8)\n" fresh;
        bprintf buf "  store ptr %%q.%Lu.v, ptr %%q.%Lu\n" fresh fresh;
        bprintf buf "  call void @__cxa_throw(ptr %%q.%Lu, ptr @_ZTIPv, ptr null)\n" fresh;
        bprintf buf "  unreachable\n";
        Int64.succ fresh
      end else begin
        let params = M.find j sk in
        let _ = List.fold_left (fun offs p ->
          bprintf buf "  %%q.%Lu.l%d = getelementptr ptr, ptr %s, i64 %d\n" fresh offs v offs;
          bprintf buf "  %%q.%Lu.v%d = load ptr, ptr %%q.%Lu.l%d\n" fresh offs fresh offs;
          p := (sprintf "%%q.%Lu.v%d" fresh offs, label) :: !p;
          offs + 1) 1 params in
        bprintf buf "  br label %%k%d\n" j;
        fresh
      end) cases (Int64.succ id) in
    q, id

  (* function calls, which is either
   * a tail call, an ordinary call, or a call with an exception handler *)
  | App (f, args, j1, j2) ->
    let is_tail_call = k = Some j1 && h = Some j2 in
    let needs_ehandler = h <> Some j2 in

    let specifier =
      if is_tail_call then "musttail call"
      else if needs_ehandler then "invoke"
      else "call" in
    bprintf buf "  %%q.%Lu = %s tailcc ptr %s(" id specifier (M.find f sv);
    let () = match args with
      | [] -> ()
      | x :: xs ->
        bprintf buf "ptr %s" (M.find x sv);
        List.iter (fun x -> bprintf buf ", ptr %s" (M.find x sv)) xs in
    bprintf buf ")\n";

    let id = Int64.succ id in
    let id = if is_tail_call then begin
      bprintf buf "  ret ptr %%q.%Lu\n" id;
      id
    end else begin
      (* regardless of whether a handler is needed, the continuation k needs
       * it's incoming phi edges hooked-up *)
      let params = M.find j1 sk in
      List.iter2 (fun p a -> p := a :: !p) params
        [sprintf "%%q.%Lu" id, label];

      if not needs_ehandler then begin
        bprintf buf "  br label %%k%d\n" j1;
        id
      end else begin
        (* the success continuation is done setup, but we need to also deal
         * with the handler. here we synthesize a dummy landing pad that will
         * extract the caught value and jump to the continuation h. *)
        bprintf buf "  to label %%k%d unwind label %%lpad.%Lu\n" j1 id;
        bprintf buf "lpad.%Lu:\n" id;
        bprintf buf "  %%info.%Lu = landingpad { ptr, i32 } catch ptr @_ZTIPv\n" id;
        bprintf buf "  %%except.%Lu = extractvalue { ptr, i32 } %%info.%Lu, 0\n" id id;
        bprintf buf "  %%selector.%Lu = extractvalue { ptr, i32 } %%info.%Lu, 1\n" id id;
        bprintf buf "  %%typeid.%Lu = call i32 @llvm.eh.typeid.for(ptr @_ZTIPv)\n" id;
        bprintf buf "  %%match.%Lu = icmp eq i32 %%selector.%Lu, %%typeid.%Lu\n" id id id;
        bprintf buf "  br i1 %%match.%Lu, label %%catch.%Lu, label %%end.%Lu \n" id id id;
        bprintf buf "catch.%Lu:\n" id;
        bprintf buf "  %%thrown.%Lu = call ptr @__cxa_begin_catch(ptr %%except.%Lu)\n" id id;
        bprintf buf "  call void @__cxa_end_catch()\n";
        bprintf buf "  br label %%k%d\n" j2;
        bprintf buf "end.%Lu:\n" id;
        bprintf buf "  resume { ptr, i32 } %%info.%Lu\n" id;

        let params = M.find j2 sk in
        List.iter2 (fun p a -> p := a :: !p) params
          [sprintf "%%thrown.%Lu" id, sprintf "catch.%Lu" id];
        Int64.succ id
      end
    end in
    q, id

  | _ -> failwith "Unsupported lowering"

let lower e =
  let _ = PassReindex.reindex e in
  match e with
    | Module (v, m) ->
      let buf = Buffer.create 32 in
      bprintf buf "define void @INIT() personality ptr @__gxx_personality_v0 {\n";
      bprintf buf "_0:\n";
      let (q, _) = lower_value [] "_0" None None M.empty M.empty 1L buf !m in
      bprintf buf "  ret void\n";
      bprintf buf "}";

      printf "declare ptr @GC_MALLOC(i64)\n";
      printf "declare ptr @__cxa_allocate_exception(i64)\n";
      printf "declare void @__cxa_throw(ptr, ptr, ptr)\n";
      printf "declare ptr @__cxa_begin_catch(ptr)\n";
      printf "declare ptr @__cxa_end_catch()\n";
      printf "declare i32 @llvm.eh.typeid.for(ptr)\n";
      printf "declare i32 @__gxx_personality_v0(...)\n";
      printf "\n";
      printf "@_ZTIPv = external constant ptr\n";
      printf "\n";
      List.iter (printf "@G_%s = global ptr null, align 8\n") v;
      printf "\n";

      let q = List.rev_append q [buf] in
      List.iter (fun buf ->
        Buffer.output_buffer stdout buf;
        printf "\n\n") q
    | _ -> failwith "INVALID TERM ANCHOR"
