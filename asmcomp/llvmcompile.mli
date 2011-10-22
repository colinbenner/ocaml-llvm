open Cmm

val compile_fundecl : fundecl -> unit

val data : data_item list -> unit

val emit_function_declarations : unit -> unit
val emit_constant_declarations : unit -> unit
val emit_header : unit -> unit
val instructions : unit -> string
