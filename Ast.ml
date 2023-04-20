type term =
  | Module of term ref
  | Export of (string * int) list
  | LetCont of int * int list * term ref * term ref
  | LetFun of int * int list * int * term ref * term ref
  | LetRec of (int * int list * int * term ref) list * term ref
  | Jmp of int * int list
  | App of int * int list * int
  | LetPack of int * int list * term ref
  | LetProj of int * int * int * term ref

let rec dump' (n : int) (t : term) : unit =
  let dump_prefix () =
    for _ = 1 to n do
      Printf.printf "  "
    done in
  match t with
    | Module m ->
      dump_prefix ();
      Printf.printf "module =\n";
      dump' (n + 1) !m

    | Export xs ->
      dump_prefix ();
      Printf.printf "export";
      List.iter (fun (n, i) ->
        Printf.printf " %s, %%v%d" n i) xs

    | LetCont (k, args, body, e) ->
      dump_prefix ();
      Printf.printf "letcont %%k%d" k;
      List.iter (fun v ->
        Printf.printf " %%v%d" v) args;
      Printf.printf " =\n";
      dump' (n + 1) !body;
      Printf.printf " in\n";
      dump' n !e

    | LetFun (f, args, k, body, e) ->
      dump_prefix ();
      Printf.printf "letfun %%v%d" f;
      List.iter (fun v ->
        Printf.printf " %%v%d" v) args;
      Printf.printf " %%k%d =\n" k;
      dump' (n + 1) !body;
      Printf.printf " in\n";
      dump' n !e

    | LetRec ([], e) ->
      dump' n !e

    | LetRec ((f, args, k, body) :: bs, e) ->
      dump_prefix ();

      Printf.printf "letrec %%v%d" f;
      List.iter (fun v ->
        Printf.printf " %%v%d" v) args;
      Printf.printf " %%k%d =\n" k;
      dump' (n + 1) !body;

      List.iter (fun (f, args, k, body) ->
        Printf.printf "\n";
        dump_prefix ();
        Printf.printf "and    %%v%d" f;
        List.iter (fun v ->
          Printf.printf " %%v%d" v) args;
        Printf.printf " %%k%d =\n" k;
        dump' (n + 1) !body) bs;

      Printf.printf " in\n";
      dump' n !e

    | Jmp (j, args) ->
      dump_prefix ();
      Printf.printf "Jmp %%k%d" j;
      List.iter (fun v ->
        Printf.printf " %%v%d" v) args

    | App (f, args, j) ->
      dump_prefix ();
      Printf.printf "App %%v%d" f;
      List.iter (fun v ->
        Printf.printf " %%v%d" v) args;
      Printf.printf " %%k%d" j

    | LetPack (v, elts, e) ->
      dump_prefix ();
      Printf.printf "let %%v%d = pack" v;
      List.iter (fun v ->
        Printf.printf " %%v%d" v) elts;
      Printf.printf " in\n";
      dump' n !e

    | LetProj (v, i, p, e) ->
      dump_prefix ();
      Printf.printf "let %%v%d = project %d %%v%d in\n" v i p;
      dump' n !e

let dump t =
  dump' 0 t
