module M = Map.Make (struct
  type t = int option
  let compare = Option.compare Int.compare
end)

type term =
  | Module of string list * term ref
  | Export of (string * int) list
  | LetCont of (int * int list * term ref) list * term ref
  | LetFun of funval * term ref
  | LetRec of funval list * term ref
  | Jmp of int * int list
  | App of int * int list * int * int
  | LetCons of int * int * int list * term ref
  | LetPack of int * int list * term ref
  | LetProj of int * int * int * term ref
  | Case of int * int M.t

and funval =
  int * int list * int * int * term ref

let rec dump' (n : int) (t : term) : unit =
  let dump_prefix () =
    for _ = 1 to n do
      Printf.printf "  "
    done in

  let dump_funval (f, args, k, h, body) =
    Printf.printf "%%v%d" f;
    List.iter (fun v ->
      Printf.printf " %%v%d" v) args;
    Printf.printf " %%k%d %%k%d =\n" k h;
    dump' (n + 1) !body in

  match t with
    | Module (v, m) ->
      dump_prefix ();
      Printf.printf "module";
      List.iter (Printf.printf " %s") v;
      Printf.printf " =\n";
      dump' (n + 1) !m

    | Export xs ->
      dump_prefix ();
      Printf.printf "export";
      List.iter (fun (n, i) ->
        Printf.printf " %s, %%v%d" n i) xs

    | LetCont ([], e) ->
      dump' n !e

    | LetCont ((k, args, body) :: bs, e) ->
      dump_prefix ();

      Printf.printf "letcont %%k%d" k;
      List.iter (fun v ->
        Printf.printf " %%v%d" v) args;
      Printf.printf " =\n";
      dump' (n + 1) !body;

      List.iter (fun (k, args, body) ->
        Printf.printf "and     %%k%d" k;
        List.iter (fun v ->
          Printf.printf " %%v%d" v) args;
        Printf.printf " =\n";
        dump' (n + 1) !body) bs;

      Printf.printf " in\n";
      dump' n !e

    | LetFun (f, e) ->
      dump_prefix ();
      Printf.printf "letfun ";
      dump_funval f;
      Printf.printf " in\n";
      dump' n !e

    | LetRec ([], e) ->
      dump' n !e

    | LetRec (f :: fs, e) ->
      dump_prefix ();

      Printf.printf "letrec ";
      dump_funval f;

      List.iter (fun f ->
        Printf.printf "\n";
        dump_prefix ();
        Printf.printf "and    ";
        dump_funval f) fs;

      Printf.printf " in\n";
      dump' n !e

    | Jmp (j, args) ->
      dump_prefix ();
      Printf.printf "Jmp %%k%d" j;
      List.iter (fun v ->
        Printf.printf " %%v%d" v) args

    | App (f, args, k, h) ->
      dump_prefix ();
      Printf.printf "App %%v%d" f;
      List.iter (fun v ->
        Printf.printf " %%v%d" v) args;
      Printf.printf " %%k%d %%k%d" k h

    | LetCons (v, i, elts, e) ->
      dump_prefix ();
      Printf.printf "let %%v%d = cons %d" v i;
      List.iter (fun v ->
        Printf.printf " %%v%d" v) elts;
      Printf.printf " in\n";
      dump' n !e

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

    | Case (v, cases) ->
      dump_prefix ();
      Printf.printf "Case %%v%d of {" v;
      M.iter (fun i k ->
        match i with
          | Some i -> Printf.printf " %d -> %%k%d;" i k
          | _ -> Printf.printf " _ -> %%k%d;" k) cases;
      Printf.printf " }"

let dump t =
  dump' 0 t
