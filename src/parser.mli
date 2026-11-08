exception Parse_error of int * string
exception Statement_error of int * string

val parse_formula : string -> Syntax.formula
val parse_term : string -> Syntax.term
val split_statements : string -> (int * string) list
