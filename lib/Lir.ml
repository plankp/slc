module M = Map.Make (String)

type prog = value M.t

and value =
  | Local of string
  | Globl of string
  | Label of label
  | Tuple of value list
  | Int64 of int64
  | Flt64 of float

and label = string list * string * block M.t

and block = string list * instr Cnode.t

and instr =
  | ICall of string * value * value list
  | IOffs of string * value * int64
  | IPack of string * value list
  | ILoad of string * value
  | IStore of value * value
  | KDead
  | KRetv of value
  | KJump of string * value list
  | KCall of value * value list
  | KCase of value * string * (int64 * string) list
  | KCatch of value * string * string * value list
  | KThrow of value

let get_dst_name = function
  | ICall (n, _, _) | IOffs (n, _, _) | IPack (n, _) | ILoad (n, _) ->
    Some n
  | IStore _
  | KDead | KRetv _ | KJump _ | KCall _ | KCase _ | KCatch _ | KThrow _ ->
    None

let rec dump (p : prog) =
  M.iter (fun k v ->
    Printf.printf "def @%s = " k;
    dump_value v;
    Printf.printf "\n\n") p

and dump_value = function
  | Label v -> dump_label v
  | Local n -> Printf.printf "$%s" n
  | Globl n -> Printf.printf "@%s" n
  | Tuple [] -> Printf.printf "{ }"
  | Tuple args ->
    Printf.printf "{ ";
    dump_csv args;
    Printf.printf " }"
  | Int64 v -> Printf.printf "#%Lu" v
  | Flt64 v -> Printf.printf "#%e" v

and dump_label (args, entry, blocks) =
  Printf.printf "(";
  let () = match args with
    | [] -> ()
    | x :: xs ->
      Printf.printf "$%s" x;
      List.iter (fun v -> Printf.printf ", $%s" v) xs in
  Printf.printf ") {\n";
  Printf.printf "  jmp .%s\n" entry;
  M.iter (fun k v -> dump_block k v; Printf.printf "\n") blocks;
  Printf.printf "}"

and dump_block n (args, instrs) =
  Printf.printf ".%s" n;
  let () = match args with
    | [] -> ()
    | x :: xs ->
      Printf.printf "($%s" x;
      List.iter (fun v -> Printf.printf ", $%s" v) xs;
      Printf.printf ")" in
  Printf.printf ":";
  Cnode.iter (fun v -> Printf.printf "\n"; dump_instr v.info) instrs

and dump_instr = function
  | ICall (d, f, args) ->
    Printf.printf "  $%s = " d;
    dump_value f;
    Printf.printf "(";
    dump_csv args;
    Printf.printf ")"
  | IOffs (d, v, i) ->
    Printf.printf "  $%s = &" d;
    dump_value v;
    Printf.printf "[%Lu]" i
  | IPack (d, args) ->
    Printf.printf "  $%s = pack " d;
    dump_csv args;
  | ILoad (d, m) ->
    Printf.printf "  $%s = *" d;
    dump_value m
  | IStore (v, m) ->
    Printf.printf "  *";
    dump_value m;
    Printf.printf " = ";
    dump_value v
  | KDead ->
    Printf.printf "  unreachable";
  | KRetv v ->
    Printf.printf "  ret "; dump_value v
  | KJump (l, []) ->
    Printf.printf "  jmp .%s" l
  | KJump (l, args) ->
    Printf.printf "  jmp .%s(" l;
    dump_csv args;
    Printf.printf ")"
  | KCall (v, args) ->
    Printf.printf "  tailcall ";
    dump_value v;
    Printf.printf "(";
    dump_csv args;
    Printf.printf ")"
  | KCase (v, k, s) ->
    Printf.printf "  switch ";
    dump_value v;
    Printf.printf ", _ .%s" k;
    List.iter (fun (v, k) -> Printf.printf ", %Lu .%s" v k) s
  | KCatch (f, k, h, args) ->
    Printf.printf "  catchcall ";
    dump_value f;
    Printf.printf " .%s, .%s (" k h;
    dump_csv args;
    Printf.printf ")"
  | KThrow x ->
    Printf.printf "  throw ";
    dump_value x

and dump_csv = function
  | [] -> ()
  | x :: xs ->
    dump_value x;
    List.iter (fun v -> Printf.printf ", " ; dump_value v) xs
