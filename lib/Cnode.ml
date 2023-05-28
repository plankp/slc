(* a mutable circular doubly linked list *)

type 'a t =
  { mutable info : 'a
  ; mutable next : 'a t
  ; mutable prev : 'a t
  }

let new_node info =
  let rec self = { info; next = self; prev = self } in
  self

let get_next node =
  node.next

let get_prev node =
  node.prev

let link_after self ptr =
  let self_last = self.prev in
  let ptr_next = ptr.next in

  ptr_next.prev <- self_last;
  self_last.next <- ptr_next;
  self.prev <- ptr;
  ptr.next <- self

let link_before self ptr =
  link_after self ptr.prev

let unlink node =
  let prev = node.prev in
  let next = node.next in
  node.prev <- node;
  node.next <- node;
  prev.next <- next;
  next.prev <- prev

let add_after self values =
  let rec loop = function
    | [] -> ()
    | x :: xs ->
      let node = new_node x in
      link_after node self;
      loop xs in
  loop values

let add_before self values =
  let rec loop = function
    | [] -> ()
    | x :: xs ->
      let node = new_node x in
      link_before node self;
      loop xs in
  loop values

let of_list = function
  | [] -> None
  | x :: xs ->
    let self = new_node x in
    add_after self xs;
    Some self

let is_singleton node =
  node.next == node

let get_info node =
  node.info

let set_info node info' =
  node.info <- info'

let iter f node =
  let last = node.prev in
  let rec loop node =
    let () = f node in
    if node != last then loop node.next in
  loop node

let fold_left f acc node =
  let last = node.prev in
  let rec loop acc node =
    let acc = f acc node in
    if node == last then acc else loop acc node.next in
  loop acc node

let fold_right f node acc =
  let first = node in
  let rec loop acc node =
    let acc = f node acc in
    if node == first then acc else loop acc node.prev in
  loop acc node.prev
