
val app : 'a1 list -> 'a1 list -> 'a1 list

module Nat :
 sig
 end

val nth_error : 'a1 list -> int -> 'a1 option

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

type formula =
| Falsum
| Equal of int * int
| Member of int * int
| Conj of formula * formula
| Disj of formula * formula
| Impl of formula * formula
| All of formula
| Ex of formula

val formula_eq_dec : formula -> formula -> bool

val formula_eqb : formula -> formula -> bool

val neg : formula -> formula

val iff : formula -> formula -> formula

val up : (int -> int) -> int -> int

val rename : (int -> int) -> formula -> formula

val lift : formula -> formula

val subst_zero : int -> int -> int

val instantiate : int -> formula -> formula

type goal = { assumptions : formula list; conclusion : formula }

type proof_state = goal list

val start : formula -> proof_state

val state_goals : proof_state -> goal list

type rule =
| RAxiom
| RHypothesis of int
| RFalsumElim
| RImplIntro
| RImplElim of formula
| RConjIntro
| RConjElimL of formula
| RConjElimR of formula
| RDisjIntroL
| RDisjIntroR
| RDisjElim of formula * formula
| RAllIntro
| RAllElim of formula * int
| RExIntro of int
| RExElim of formula
| REqualRefl
| REqualElim of formula * int * int
| RCut of formula

type tactic =
| TacRule of rule
| TacIntro
| TacExact of int
| TacApply of int
| TacSpecialize of int * int
| TacSplit
| TacLeft
| TacRight
| TacUse of int
| TacRefl
| TacContradiction
| TacCases of int

type step_error =
| NoGoals
| HypothesisNotFound
| FormulaMismatch
| WrongGoalShape

type 'a outcome =
| Success of 'a
| Failure of step_error

val rule_step_focus : (formula -> bool) -> rule -> goal -> goal list outcome

val contains_formula : formula -> formula list -> bool

val contradictory : formula list -> bool

val step_focus : (formula -> bool) -> tactic -> goal -> goal list outcome

val step : (formula -> bool) -> tactic -> proof_state -> proof_state outcome

val run :
  (formula -> bool) -> tactic list -> proof_state -> proof_state outcome

val rule_step :
  (formula -> bool) -> rule -> proof_state -> proof_state outcome

val rule_run :
  (formula -> bool) -> rule list -> proof_state -> proof_state outcome

val empty_set_axiom : formula

val extensionality_axiom : formula

val pairing_axiom : formula

val union_axiom : formula

val power_set_axiom : formula

val foundation_axiom : formula

val infinity_axiom : formula

val insert_subset : int -> int

val separation_instance : formula -> formula

val replacement_alternate : int -> int

val replacement_image : int -> int

val replacement_instance : formula -> formula

val choice_axiom : formula
