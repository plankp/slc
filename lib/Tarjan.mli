type 'a vertex

val new_vertex : 'a -> 'a vertex

val add_edge : 'a vertex -> 'a vertex -> unit
val reset_edges : 'a vertex -> unit
val has_edge : 'a vertex -> 'a vertex -> bool
val get_edges : 'a vertex -> 'a vertex list

val set_info : 'a vertex -> 'a -> unit
val get_info : 'a vertex -> 'a

val reset_state : 'a vertex -> unit

val compute_scc : 'a vertex Seq.t -> 'a vertex list list
