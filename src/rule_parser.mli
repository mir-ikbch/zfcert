exception Error of string

(** Split command parameters while preserving whitespace within function terms. *)
val term_words : string -> string list

val parse :
  parse_formula:(string -> Syntax.formula) ->
  string ->
  Zfcert_kernel.rule_request

val description : string -> string
