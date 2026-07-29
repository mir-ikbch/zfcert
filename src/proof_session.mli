type axiom = {
  key : string;
  title : string;
  statement : string;
  note : string;
  parsed : Syntax.formula option;
}

type display_goal = {
  context : (string * Syntax.formula) list;
  target : Syntax.formula;
}

type proposition_definition = {
  definition_name : string;
  parameters : string list;
  body : Syntax.formula;
}

type session

exception Proof_error of int * string

val axioms : axiom list
val find_axiom : string -> axiom option
val analyze_script : string -> session * bool
val check_script : string -> session

val theorem_name : session -> string
val theorem : session -> Syntax.formula
val definitions : session -> proposition_definition list
val goals : session -> display_goal list
val step_count : session -> int
val is_complete : session -> bool
