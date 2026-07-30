(** Constructor-only conversion between the parser syntax and the named
    syntax extracted from Coq. *)

val to_kernel : Syntax.formula -> Zfcert_kernel.formula
val of_kernel : Zfcert_kernel.formula -> Syntax.formula
