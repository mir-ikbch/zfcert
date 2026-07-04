type formula =
  | Falsum
  | Equal of int * int
  | Member of int * int
  | Conj of formula * formula
  | Disj of formula * formula
  | Impl of formula * formula
  | All of formula
  | Ex of formula

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

type error =
  | NoGoals
  | HypothesisNotFound
  | FormulaMismatch
  | WrongGoalShape

type state

type goal_view = {
  assumptions : formula list;
  conclusion : formula;
}

type fixed_axiom =
  | EmptySet
  | Extensionality
  | Pairing
  | Union
  | PowerSet
  | Foundation
  | Infinity
  | Choice

type axiom

val start : formula -> state
val goals : state -> goal_view list
val solved : state -> bool

val step : tactic -> state -> (state, error) result
val run : tactic list -> state -> (state, error) result

val rule_step :
  axioms:axiom list -> rule -> state -> (state, error) result

val rule_run :
  axioms:axiom list -> rule list -> state -> (state, error) result

val fixed_axiom : fixed_axiom -> axiom
val separation_axiom : formula -> axiom
val replacement_axiom : formula -> axiom

val instantiate : int -> formula -> formula
val separation_instance : formula -> formula
val replacement_instance : formula -> formula
