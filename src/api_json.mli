val axioms : unit -> string
val success : Proof_session.session -> string
val step : Proof_session.session -> has_qed:bool -> string
val error : line:int -> string -> string
