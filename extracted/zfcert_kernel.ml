module Raw = Proof_state

type formula = Raw.formula =
  | Falsum
  | Equal of int * int
  | Member of int * int
  | Conj of formula * formula
  | Disj of formula * formula
  | Impl of formula * formula
  | All of formula
  | Ex of formula

type rule = Raw.rule =
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

type tactic = Raw.tactic =
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

type error = Raw.step_error =
  | NoGoals
  | HypothesisNotFound
  | FormulaMismatch
  | WrongGoalShape

type state = Raw.proof_state

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

type axiom = formula

let start = Raw.start

let goals state =
  Raw.state_goals state
  |> List.map (fun goal ->
       {
         assumptions = goal.Raw.assumptions;
         conclusion = goal.Raw.conclusion;
       })

let solved state = Raw.state_goals state = []

let outcome = function
  | Raw.Success state -> Ok state
  | Raw.Failure error -> Error error

let checker axioms candidate =
  List.exists (fun axiom -> Raw.formula_eqb axiom candidate) axioms

let step tactic state =
  Raw.step (fun _ -> false) tactic state |> outcome

let run tactics state =
  Raw.run (fun _ -> false) tactics state |> outcome

let rule_step ~axioms rule state =
  Raw.rule_step (checker axioms) rule state |> outcome

let rule_run ~axioms rules state =
  Raw.rule_run (checker axioms) rules state |> outcome

let fixed_axiom = function
  | EmptySet -> Raw.empty_set_axiom
  | Extensionality -> Raw.extensionality_axiom
  | Pairing -> Raw.pairing_axiom
  | Union -> Raw.union_axiom
  | PowerSet -> Raw.power_set_axiom
  | Foundation -> Raw.foundation_axiom
  | Infinity -> Raw.infinity_axiom
  | Choice -> Raw.choice_axiom

let separation_axiom predicate =
  Raw.separation_instance predicate

let replacement_axiom predicate =
  Raw.replacement_instance predicate

let instantiate = Raw.instantiate
let separation_instance = Raw.separation_instance
let replacement_instance = Raw.replacement_instance
