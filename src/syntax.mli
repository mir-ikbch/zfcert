type formula =
  | Bottom
  | Named of string * string list
  | Eq of string * string
  | Mem of string * string
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imp of formula * formula
  | Iff of formula * formula
  | Forall of string * formula
  | Exists of string * formula

module StringSet : Set.S with type elt = string

val formula_to_string : ?outer:int -> formula -> string
val free_vars : formula -> StringSet.t
val all_vars : formula -> StringSet.t
val fresh_name : string -> StringSet.t -> string
val rename_bound : string -> string -> formula -> formula
val subst : string -> string -> formula -> formula
val alpha_equal : formula -> formula -> bool
