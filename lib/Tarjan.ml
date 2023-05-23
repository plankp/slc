type 'a vertex =
  { mutable info : 'a
  ; mutable deps : 'a vertex list
  ; mutable index : int option
  ; mutable lowlink : int
  ; mutable onstack : bool
  }

let new_vertex info =
  { info; deps = []; index = None; lowlink = ~-1; onstack = false }

let add_edge src dst =
  src.deps <- dst :: src.deps

let reset_edges src =
  src.deps <- []

let has_edge src dst =
  List.memq dst src.deps

let get_edges src =
  src.deps

let get_info { info; _ } = info

let set_info n v =
  n.info <- v

let update_info n f =
  n.info <- f n.info

let reset_state node =
  node.index <- None;
  node.lowlink <- ~-1;
  node.onstack <- false

let compute_scc g =
  (* use Tarjan's scc *)
  let index = ref 0 in
  let stack = ref [] in
  let rebuild = ref [] in

  let rec connect v =
    v.index <- Some !index;
    v.lowlink <- !index;
    v.onstack <- true;
    index := !index + 1;
    stack := v :: !stack;

    List.iter (fun w ->
      match w.index with
        | None ->
          connect w;
          v.lowlink <- min v.lowlink w.lowlink
        | Some w_index ->
          if w.onstack then
            v.lowlink <- min v.lowlink w_index) v.deps;

    if Some v.lowlink = v.index then begin
      let rec loop scc =
        match !stack with
          | [] -> failwith "INVALID STATE"
          | w :: xs ->
            stack := xs;
            w.onstack <- false;
            let scc = w :: scc in
            if w != v then loop scc
            else rebuild := scc :: !rebuild in
      loop []
    end in

  Seq.iter (fun v -> if v.index = None then connect v) g;
  !rebuild
