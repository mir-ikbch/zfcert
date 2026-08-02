
val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

val revapp : uint -> uint -> uint

val rev : uint -> uint

module Little :
 sig
  val succ : uint -> uint
 end

val add : int -> int -> int

val sub : int -> int -> int

module Nat :
 sig
  val ltb : int -> int -> bool

  val to_little_uint : int -> uint -> uint

  val to_uint : int -> uint
 end

val nth_error : 'a1 list -> int -> 'a1 option

val rev0 : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

type term =
| Var of int
| App of string * term_arguments
and term_arguments =
| TNil
| TCons of term * term_arguments

val term_eqb : term -> term -> bool

val term_arguments_eqb : term_arguments -> term_arguments -> bool

val term_eq_dec : term -> term -> bool

type formula =
| Falsum
| Equal of term * term
| Member of term * term
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

val rename_term : (int -> int) -> term -> term

val rename_arguments : (int -> int) -> term_arguments -> term_arguments

val rename : (int -> int) -> formula -> formula

val lift : formula -> formula

val lift_term : term -> term

val up_substitution : (int -> term) -> int -> term

val substitute_term : (int -> term) -> term -> term

val substitute_arguments : (int -> term) -> term_arguments -> term_arguments

val substitute : (int -> term) -> formula -> formula

val subst_zero : term -> int -> term

val instantiate : term -> formula -> formula

type goal = { assumptions : formula list; conclusion : formula }

type proof_state = goal list

val start_with_assumptions : formula list -> formula -> proof_state

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
| RAllElim of formula * term
| RExIntro of term
| RExElim of formula
| REqualRefl
| REqualElim of formula * term * term
| RCut of formula

type tactic =
| TacRule of rule
| TacIntro
| TacExact of int
| TacApply of int
| TacSpecialize of int * term
| TacSplit
| TacLeft
| TacRight
| TacUse of term
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

module NilEmpty :
 sig
  val string_of_uint : uint -> string
 end

type named_term =
| NName of string
| NApp of string * named_arguments
and named_arguments =
| NNNil
| NNCons of named_term * named_arguments

type named_formula =
| NFalsum
| NEqual of named_term * named_term
| NMember of named_term * named_term
| NConj of named_formula * named_formula
| NDisj of named_formula * named_formula
| NImpl of named_formula * named_formula
| NNeg of named_formula
| NIff of named_formula * named_formula
| NAll of string * named_formula
| NEx of string * named_formula

type named_hypothesis = { named_hypothesis_name : string;
                          named_hypothesis_formula : named_formula }

type named_goal = { named_assumptions : named_hypothesis list;
                    named_conclusion : named_formula }

type named_error =
| NCoreError of step_error
| NUnknownVariable of string
| NHypothesisNotFound of string
| NHypothesisAlreadyUsed of string
| NVariableAlreadyUsed of string
| NMetadataMismatch
| NWrongNamedShape

type 'a named_result =
| NOk of 'a
| NError of named_error

val named_bind :
  'a1 named_result -> ('a1 -> 'a2 named_result) -> 'a2 named_result

val string_mem : string -> string list -> bool

val string_index_from : string -> int -> string list -> int option

val string_index : string -> string list -> int option

val add_name : string list -> string -> string list

val remove_name : string -> string list -> string list

val merge_names : string list -> string list -> string list

val named_term_names : named_term -> string list

val named_arguments_names : named_arguments -> string list

val named_formula_names : named_formula -> string list

val named_term_subst : string -> string -> named_term -> named_term

val named_arguments_subst :
  string -> string -> named_arguments -> named_arguments

val filter_environment : string list -> string list -> string list

val shared_name : string list -> string list -> string option

val add_environment_name : string list -> string list -> string -> string list

val named_free_variables : named_formula -> string list

val named_binder_names : named_formula -> string list

val extend_environment :
  string list -> string list -> named_formula -> string list

val extend_environments :
  string list -> string list -> named_formula list -> string list

val variable_index : string list -> string list -> string -> int named_result

val elaborate_arguments :
  string list -> string list -> string list -> named_arguments ->
  term_arguments named_result

val elaborate_term :
  string list -> string list -> string list -> named_term -> term named_result

val elaborate :
  string list -> string list -> string list -> named_formula -> formula
  named_result

val nth_name : string list -> string list -> int -> string named_result

val reify_term : string list -> string list -> term -> named_term named_result

val reify_arguments :
  string list -> string list -> term_arguments -> named_arguments named_result

val nat_to_decimal_string : int -> string

val fresh_string_candidate : string -> int -> string

val fresh_string_with_fuel : int -> string -> int -> string list -> string

val fresh_string : string -> string list -> string

val named_separation_source_name :
  named_term -> string -> named_formula -> string

val choose_binder :
  string list -> string list -> string list -> string list -> string * string
  list

val reify_with_names :
  string list -> string list -> string list -> string list -> formula ->
  (named_formula * string list) named_result

val reify :
  string list -> string list -> string list -> formula -> named_formula
  named_result

type goal_metadata = { metadata_hypothesis_names : string list;
                       metadata_assumption_binders : string list list;
                       metadata_conclusion_binders : string list;
                       metadata_environment : string list;
                       metadata_constants : string list }

type named_state = { named_kernel_state : proof_state;
                     named_goal_metadata : goal_metadata list }

val initial_metadata_with_assumptions :
  string list -> string list -> named_hypothesis list -> named_formula ->
  goal_metadata

val named_start_with_environment :
  string list -> string list -> named_hypothesis list -> formula list ->
  named_formula -> named_state named_result

val named_start_with_constants :
  string list -> named_formula -> named_state named_result

val named_start : named_formula -> named_state named_result

val reify_assumptions :
  string list -> string list -> string list -> string list list -> formula
  list -> named_hypothesis list named_result

val reify_goal : goal_metadata -> goal -> named_goal named_result

val reify_goals :
  goal_metadata list -> goal list -> named_goal list named_result

val named_goals : named_state -> named_goal list named_result

val named_solved : named_state -> bool

type named_fixed_axiom =
| NEmptySet
| NExtensionality
| NPairing
| NUnion
| NPowerSet
| NFoundation
| NInfinity
| NChoice

type named_axiom =
| NFixedAxiom of named_fixed_axiom
| NClassicalAxiom of named_formula
| NSeparationAxiom of string * string * named_formula
| NSeparationTermAxiom of named_term * string * named_formula
| NReplacementAxiom of string * string * named_formula

val fixed_axiom_formula : named_fixed_axiom -> formula

val elaborate_schema_predicate :
  string list -> string list -> string list -> named_formula -> formula
  named_result

val compile_axiom :
  string list -> string list -> named_axiom -> formula named_result

val compile_axioms :
  string list -> string list -> named_axiom list -> formula list named_result

val formula_in : formula -> formula list -> bool

type named_rule =
| NRAxiom
| NRHypothesis of string
| NRFalsumElim
| NRImplIntro of string
| NRImplElim of named_formula
| NRConjIntro
| NRConjElimL of named_formula
| NRConjElimR of named_formula
| NRDisjIntroL
| NRDisjIntroR
| NRDisjElim of named_formula * named_formula * string * string
| NRAllIntro of string
| NRAllElim of named_term * named_formula
| NRExIntro of named_term
| NRExElim of string * string * named_formula
| NREqualRefl
| NREqualElim of string * string * named_formula
| NRCut of string * named_formula

type rule_plan = { planned_rule : rule;
                   planned_generated_metadata : goal_metadata list;
                   planned_environment : string list }

val metadata_with_conclusion :
  goal_metadata -> string list -> string list -> goal_metadata

val metadata_with_hypothesis :
  goal_metadata -> string -> string list -> string list -> string list ->
  goal_metadata

val ensure_hypothesis_fresh : goal_metadata -> string -> unit named_result

val ensure_variable_fresh : goal_metadata -> string -> unit named_result

val hypothesis_index : goal_metadata -> string -> int named_result

val find_named_hypothesis :
  string -> named_hypothesis list -> named_formula option

val elaborate_in_environment :
  string list -> string list -> named_formula -> formula named_result

val term_index : string list -> string list -> named_term -> term named_result

val extend_environment_term :
  string list -> string list -> named_term -> string list

val plan_named_rule :
  goal_metadata -> named_goal -> named_rule -> rule_plan named_result

val named_rule_step :
  named_axiom list -> named_rule -> named_state -> named_state named_result

val named_rule_run :
  named_axiom list -> named_rule list -> named_state -> named_state
  named_result

type named_tactic =
| NTacRule of named_rule
| NTacIntro of string
| NTacExact of string
| NTacApply of string
| NTacSpecialize of string * string * string
| NTacSplit
| NTacLeft
| NTacRight
| NTacUse of named_term
| NTacRefl
| NTacContradiction
| NTacCases of string * string * string

type tactic_plan = { planned_tactic : tactic;
                     tactic_generated_metadata : goal_metadata list;
                     tactic_environment : string list }

val plan_named_tactic :
  goal_metadata -> named_goal -> named_tactic -> tactic_plan named_result

val named_tactic_step :
  named_tactic -> named_state -> named_state named_result

val named_step :
  named_axiom list -> named_tactic -> named_state -> named_state named_result

val named_run :
  named_axiom list -> named_tactic list -> named_state -> named_state
  named_result

val named_all_variables : named_formula -> string list

val named_substitute_variable :
  string -> string -> named_formula -> named_formula

val named_separation_instance :
  string -> string -> named_formula -> named_formula

val named_separation_term_instance :
  named_term -> string -> named_formula -> named_formula

type named_replacement_parts = { named_replacement_functional : named_formula;
                                 named_replacement_image : named_formula;
                                 named_replacement_instance : named_formula }

val make_named_replacement_parts :
  string -> string -> string -> named_formula -> named_replacement_parts

val named_fixed_axioms : named_axiom list

val named_default_all_intro_rule_step :
  named_state -> named_state named_result

val named_fixed_axiom_rule_step : named_state -> named_state named_result

val named_separation_axiom_rule_step :
  string -> string -> named_formula -> named_state -> named_state named_result

val current_hypothesis_names : named_state -> string list

val replacement_internal_hypothesis : named_state -> string

val named_replacement_axiom_rule_step :
  string -> string -> string -> named_formula -> named_state -> named_state
  named_result

val named_separation_tactic_step :
  string -> string -> string -> named_formula -> named_state -> named_state
  named_result

val named_separation_term_tactic_step :
  string -> named_term -> string -> named_formula -> named_state ->
  named_state named_result

val named_replacement_tactic_step :
  string -> string -> string -> string -> named_formula -> named_state ->
  named_state named_result

type named_rule_request =
| NPrimitiveRule of named_rule
| NDefaultAllIntroRule
| NFixedAxiomRule
| NSeparationAxiomRule of string * string * named_formula
| NReplacementAxiomRule of string * string * string * named_formula

val named_execute_rule :
  named_rule_request -> named_state -> named_state named_result

type certificate_step = { certificate_axioms : named_axiom list;
                          certificate_rule : named_rule }

type certificate = certificate_step list

val run_certificate_step :
  certificate_step -> named_state -> named_state named_result

val replay_steps : certificate -> named_state -> named_state named_result

type certified_state = { certified_initial_formula : named_formula;
                         certified_constants : string list;
                         certified_initial_environment : string list;
                         certified_initial_named_assumptions : named_hypothesis
                                                               list;
                         certified_initial_core_assumptions : formula list;
                         certified_current_state : named_state;
                         certified_reverse_certificate : certificate }

val certified_start_with_environment :
  string list -> string list -> named_hypothesis list -> formula list ->
  named_formula -> certified_state named_result

val certified_start_with_constants :
  string list -> named_formula -> certified_state named_result

val certified_start : named_formula -> certified_state named_result

val certified_goals : certified_state -> named_goal list named_result

val certified_solved : certified_state -> bool

val certified_certificate : certified_state -> certificate

val certified_step :
  certificate_step -> certified_state -> certified_state named_result

val certified_run :
  certificate -> certified_state -> certified_state named_result

val replay_certificate_with_environment :
  string list -> string list -> named_hypothesis list -> formula list ->
  named_formula -> certificate -> named_state named_result

val replay_certificate_with_constants :
  string list -> named_formula -> certificate -> named_state named_result

val replay_certificate :
  named_formula -> certificate -> named_state named_result

val certified_finalize : certified_state -> certificate named_result

val one_step : named_axiom list -> named_rule -> certificate_step

val named_rule_request_program :
  named_rule_request -> named_state -> certificate named_result

val certified_execute_rule :
  named_rule_request -> certified_state -> certified_state named_result

val separation_tactic_program :
  string -> string -> string -> named_formula -> certificate

val certified_separation_tactic :
  string -> string -> string -> named_formula -> certified_state ->
  certified_state named_result

val separation_term_tactic_program :
  string -> named_term -> string -> named_formula -> certificate

val certified_separation_term_tactic :
  string -> named_term -> string -> named_formula -> certified_state ->
  certified_state named_result

val replacement_tactic_program :
  string -> string -> string -> string -> named_formula -> named_state ->
  certificate

val certified_replacement_tactic :
  string -> string -> string -> string -> named_formula -> certified_state ->
  certified_state named_result

type global_environment = { global_constants : string list;
                            global_named_facts : named_hypothesis list;
                            global_core_facts : formula list }

val named_arguments_of_names : string list -> named_arguments

val named_term_replace : string -> named_term -> named_term -> named_term

val named_arguments_replace :
  string -> named_term -> named_arguments -> named_arguments

val named_formula_replace :
  string -> named_term -> named_formula -> named_formula

val named_skolemize :
  string -> string list -> named_formula -> named_formula option

val empty_global_environment : global_environment

val global_fact_names : global_environment -> string list

val global_start :
  global_environment -> named_formula -> certified_state named_result

val global_replay :
  global_environment -> named_formula -> certificate -> named_state
  named_result

val global_declare_choice :
  string -> string -> named_formula -> certificate -> global_environment ->
  global_environment named_result

val global_declare_fact :
  string -> named_formula -> certificate -> global_environment ->
  global_environment named_result

val global_declare_skolem :
  string -> string -> named_formula -> certificate -> global_environment ->
  global_environment named_result
