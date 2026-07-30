exception Error of string

val parse :
  parse_formula:(string -> Syntax.formula) ->
  string ->
  Zfcert_kernel.rule_request

val description : string -> string
