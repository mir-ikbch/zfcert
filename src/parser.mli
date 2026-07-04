exception Parse_error of int * string
exception Statement_error of int * string

val parse_formula : string -> Syntax.formula
val split_statements : string -> (int * string) list
