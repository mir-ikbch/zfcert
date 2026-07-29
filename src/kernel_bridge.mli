(** The only application module connected to the Coq-extracted kernel.

    The proof-language layer uses named variables.  The extracted kernel uses
    de Bruijn indices.  This module exposes the kernel operations and owns that
    representation conversion. *)

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

type fixed_axiom =
  | EmptySet
  | Extensionality
  | Pairing
  | Union
  | PowerSet
  | Foundation
  | Infinity
  | Choice

type state
type axiom

type source_goal = {
  assumptions : Syntax.formula list;
  conclusion : Syntax.formula;
  environment : string list;
}

val encode_formula :
  bound:string list ->
  environment:string list ->
  Syntax.formula ->
  (formula, string) result

val start : formula -> state
val solved : state -> bool

val checked_step :
  tactic ->
  state ->
  expected:source_goal list ->
  (state, string) result

val checked_rule_run :
  axioms:axiom list ->
  rule list ->
  state ->
  expected:source_goal list ->
  (state, string) result

val fixed_axiom : fixed_axiom -> axiom
val separation_axiom : formula -> axiom
val replacement_axiom : formula -> axiom

val instantiate : int -> formula -> formula
val separation_instance : formula -> formula
val replacement_instance : formula -> formula
