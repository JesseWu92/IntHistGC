val world : int ref
val maxdepth : int ref
val c_cache : int ref
val c_bjump : int ref

val set_to_buf : MiscSolver.FSet.t -> Buffer.t
val output_seq : Sequent.sequent -> out_channel -> unit
val print_node : int -> Sequent.sequent -> out_channel -> unit
val print_edge : int -> int -> int -> out_channel -> unit
val print_false : int -> out_channel -> unit
val mainl : Sequent.sequent -> int -> int -> Sequent.sequent -> out_channel -> bool -> bool
val prove : Sequent.sequent -> out_channel -> bool
