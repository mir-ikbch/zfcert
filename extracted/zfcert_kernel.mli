type named_term =
  | NName of string
  | NApp of string * named_arguments

and named_arguments =
  | NNNil
  | NNCons of named_term * named_arguments

type formula =
  | NFalsum
  | NEqual of named_term * named_term
  | NMember of named_term * named_term
  | NConj of formula * formula
  | NDisj of formula * formula
  | NImpl of formula * formula
  | NNeg of formula
  | NIff of formula * formula
  | NAll of string * formula
  | NEx of string * formula

type rule =
  | NRAxiom
  | NRHypothesis of string
  | NRFalsumElim
  | NRImplIntro of string
  | NRImplElim of formula
  | NRConjIntro
  | NRConjElimL of formula
  | NRConjElimR of formula
  | NRDisjIntroL
  | NRDisjIntroR
  | NRDisjElim of formula * formula * string * string
  | NRAllIntro of string
  | NRAllElim of named_term * formula
  | NRExIntro of named_term
  | NRExElim of string * string * formula
  | NREqualRefl
  | NREqualElim of string * string * formula
  | NRCut of string * formula

type rule_request =
  | NPrimitiveRule of rule
  | NDefaultAllIntroRule
  | NFixedAxiomRule
  | NSeparationAxiomRule of string * string * formula
  | NReplacementAxiomRule of string * string * string * formula

type error =
  | NoGoals
  | HypothesisNotFound of string option
  | HypothesisAlreadyUsed of string
  | VariableAlreadyUsed of string
  | UnknownVariable of string
  | FormulaMismatch
  | WrongGoalShape
  | MetadataMismatch

type state
type environment
type axiom
type certificate_step
type certificate

type goal_view = {
  variables : string list;
  assumptions : (string * formula) list;
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

val start : formula -> (state, error) result
val start_with_constants : string list -> formula -> (state, error) result
val empty_environment : environment
val environment_constants : environment -> string list
val environment_facts : environment -> (string * formula) list

val start_in_environment :
  environment -> formula -> (state, error) result

val declare_choice :
  constant:string ->
  fact:string ->
  source:formula ->
  proof:certificate ->
  environment ->
  (environment, error) result

val declare_fact :
  fact:string ->
  source:formula ->
  proof:certificate ->
  environment ->
  (environment, error) result

val declare_skolem :
  function_name:string ->
  fact:string ->
  source:formula ->
  proof:certificate ->
  environment ->
  (environment, error) result

val goals : state -> (goal_view list, error) result
val solved : state -> bool

val certificate_step :
  axioms:axiom list ->
  rule ->
  certificate_step

val run_certificate :
  certificate_step list ->
  state ->
  (state, error) result

val rule_step :
  axioms:axiom list ->
  rule ->
  state ->
  (state, error) result

val rule_run :
  axioms:axiom list ->
  rule list ->
  state ->
  (state, error) result

val default_all_intro_rule_step :
  state ->
  (state, error) result

val fixed_axiom_rule_step :
  state ->
  (state, error) result

val separation_axiom_rule_step :
  source:string ->
  element:string ->
  formula ->
  state ->
  (state, error) result

val replacement_axiom_rule_step :
  source:string ->
  input:string ->
  output:string ->
  formula ->
  state ->
  (state, error) result

val separation_tactic_step :
  fact:string ->
  source:string ->
  element:string ->
  formula ->
  state ->
  (state, error) result

val separation_term_tactic_step :
  fact:string ->
  source:named_term ->
  element:string ->
  formula ->
  state ->
  (state, error) result

val replacement_tactic_step :
  fact:string ->
  source:string ->
  input:string ->
  output:string ->
  formula ->
  state ->
  (state, error) result

val execute_rule :
  rule_request ->
  state ->
  (state, error) result

val finalize :
  state ->
  (certificate, error) result

val certificate_rules : certificate -> rule list
val current_certificate_rules : state -> rule list

val fixed_axiom : fixed_axiom -> axiom

val classical_axiom : formula -> axiom

val separation_axiom :
  source:string ->
  element:string ->
  formula ->
  axiom

val replacement_axiom :
  input:string ->
  output:string ->
  formula ->
  axiom
