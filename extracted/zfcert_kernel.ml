(** Thin OCaml facade over the Coq-extracted named proof state. *)

module Raw = Proof_state

type formula = Raw.named_formula =
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

and named_term = Raw.named_term =
  | NName of string
  | NApp of string * named_arguments

and named_arguments = Raw.named_arguments =
  | NNNil
  | NNCons of named_term * named_arguments

type rule = Raw.named_rule =
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

type rule_request = Raw.named_rule_request =
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

type state = Raw.certified_state
type environment = Raw.global_environment
type axiom = Raw.named_axiom
type certificate_step = Raw.certificate_step
type certificate = Raw.certificate

type goal_view = {
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

let error = function
  | Raw.NCoreError Raw.NoGoals -> NoGoals
  | Raw.NCoreError Raw.HypothesisNotFound ->
      HypothesisNotFound None
  | Raw.NCoreError Raw.FormulaMismatch -> FormulaMismatch
  | Raw.NCoreError Raw.WrongGoalShape -> WrongGoalShape
  | Raw.NUnknownVariable name -> UnknownVariable name
  | Raw.NHypothesisNotFound name ->
      HypothesisNotFound (Some name)
  | Raw.NHypothesisAlreadyUsed name ->
      HypothesisAlreadyUsed name
  | Raw.NVariableAlreadyUsed name ->
      VariableAlreadyUsed name
  | Raw.NMetadataMismatch -> MetadataMismatch
  | Raw.NWrongNamedShape -> WrongGoalShape

let outcome = function
  | Raw.NOk value -> Ok value
  | Raw.NError failure -> Error (error failure)

let start formula =
  Raw.certified_start formula |> outcome

let start_with_constants constants formula =
  Raw.certified_start_with_constants constants formula |> outcome

let empty_environment = Raw.empty_global_environment

let environment_constants environment =
  environment.Raw.global_constants

let environment_facts environment =
  List.map
    (fun hypothesis ->
       (hypothesis.Raw.named_hypothesis_name,
        hypothesis.Raw.named_hypothesis_formula))
    environment.Raw.global_named_facts

let start_in_environment environment formula =
  Raw.global_start environment formula |> outcome

let declare_choice ~constant ~fact ~source ~proof environment =
  Raw.global_declare_choice constant fact source proof environment |> outcome

let declare_fact ~fact ~source ~proof environment =
  Raw.global_declare_fact fact source proof environment |> outcome

let declare_skolem ~function_name ~fact ~source ~proof environment =
  Raw.global_declare_skolem function_name fact source proof environment |> outcome

let goals state =
  match Raw.certified_goals state with
  | Raw.NError failure -> Error (error failure)
  | Raw.NOk goals ->
      Ok
        (List.map
           (fun goal ->
              {
                assumptions =
                  List.map
                    (fun hypothesis ->
                       (hypothesis.Raw.named_hypothesis_name,
                        hypothesis.Raw.named_hypothesis_formula))
                    goal.Raw.named_assumptions;
                conclusion = goal.Raw.named_conclusion;
              })
           goals)

let solved = Raw.certified_solved

let certificate_step ~axioms rule =
  Raw.one_step axioms rule

let run_certificate steps state =
  Raw.certified_run steps state |> outcome

let rule_step ~axioms rule state =
  Raw.certified_step (Raw.one_step axioms rule) state |> outcome

let rule_run ~axioms rules state =
  rules
  |> List.map (Raw.one_step axioms)
  |> fun steps -> Raw.certified_run steps state
  |> outcome

let default_all_intro_rule_step state =
  Raw.certified_execute_rule Raw.NDefaultAllIntroRule state |> outcome

let fixed_axiom_rule_step state =
  Raw.certified_execute_rule Raw.NFixedAxiomRule state |> outcome

let separation_axiom_rule_step ~source ~element predicate state =
  Raw.certified_execute_rule
    (Raw.NSeparationAxiomRule (source, element, predicate)) state
  |> outcome

let replacement_axiom_rule_step ~source ~input ~output predicate state =
  Raw.certified_execute_rule
    (Raw.NReplacementAxiomRule (source, input, output, predicate)) state
  |> outcome

let separation_tactic_step ~fact ~source ~element predicate state =
  Raw.certified_separation_tactic
    fact source element predicate state
  |> outcome

let separation_term_tactic_step ~fact ~source ~element predicate state =
  Raw.certified_separation_term_tactic
    fact source element predicate state
  |> outcome

let replacement_tactic_step
    ~fact ~source ~input ~output predicate state =
  Raw.certified_replacement_tactic
    fact source input output predicate state
  |> outcome

let execute_rule request state =
  Raw.certified_execute_rule request state |> outcome

let finalize state =
  Raw.certified_finalize state |> outcome

let certificate_rules certificate =
  List.map
    (fun step -> step.Raw.certificate_rule)
    certificate

let current_certificate_rules state =
  Raw.certified_certificate state |> certificate_rules

let fixed_axiom = function
  | EmptySet -> Raw.NFixedAxiom Raw.NEmptySet
  | Extensionality -> Raw.NFixedAxiom Raw.NExtensionality
  | Pairing -> Raw.NFixedAxiom Raw.NPairing
  | Union -> Raw.NFixedAxiom Raw.NUnion
  | PowerSet -> Raw.NFixedAxiom Raw.NPowerSet
  | Foundation -> Raw.NFixedAxiom Raw.NFoundation
  | Infinity -> Raw.NFixedAxiom Raw.NInfinity
  | Choice -> Raw.NFixedAxiom Raw.NChoice

let classical_axiom predicate =
  Raw.NClassicalAxiom predicate

let separation_axiom ~source ~element predicate =
  Raw.NSeparationAxiom (source, element, predicate)

let replacement_axiom ~input ~output predicate =
  Raw.NReplacementAxiom (input, output, predicate)
