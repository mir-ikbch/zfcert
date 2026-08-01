(** Constructor-only conversion between the parser syntax and the named
    syntax extracted from Coq. *)

val to_kernel : Syntax.formula -> Zfcert_kernel.formula
val to_kernel_term : Syntax.term -> Zfcert_kernel.named_term
val of_kernel : Zfcert_kernel.formula -> Syntax.formula
val of_kernel_term : Zfcert_kernel.named_term -> Syntax.term
