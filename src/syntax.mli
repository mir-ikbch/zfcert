type formula =
  | Bottom
  | Named of string * string list
  | Eq of term * term
  | Mem of term * term
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imp of formula * formula
  | Iff of formula * formula
  | Forall of string * formula
  | Exists of string * formula

and term =
  | Name of string
  | App of string * term list

module StringSet : Set.S with type elt = string

val formula_to_string : ?outer:int -> formula -> string
val term_to_string : term -> string
val term_free_vars : term -> StringSet.t
val free_vars : formula -> StringSet.t
val all_vars : formula -> StringSet.t
val fresh_name : string -> StringSet.t -> string
val rename_bound : string -> string -> formula -> formula
val subst : string -> term -> formula -> formula
val alpha_equal : formula -> formula -> bool
