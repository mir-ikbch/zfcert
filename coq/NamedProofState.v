(** A string-named facade for the de Bruijn proof kernel.

    The logical kernel remains [ProofState].  This module owns variable-name
    elaboration, hypothesis labels, goal reification, and the metadata changes
    associated with named rules and tactics.  Its extracted [named_state] is
    intended to be abstract on the OCaml side.
 *)

From Coq Require Import List Bool PeanoNat String.
From ZFCert Require Import FOL ProofState TacticCompleteness ZFC.
Import ListNotations.
Open Scope string_scope.

Set Implicit Arguments.

Inductive named_formula : Type :=
| NFalsum
| NEqual (left right : string)
| NMember (left right : string)
| NConj (left right : named_formula)
| NDisj (left right : named_formula)
| NImpl (left right : named_formula)
| NNeg (body : named_formula)
| NIff (left right : named_formula)
| NAll (binder : string) (body : named_formula)
| NEx (binder : string) (body : named_formula).

Record named_hypothesis : Type := NamedHypothesis {
  named_hypothesis_name : string;
  named_hypothesis_formula : named_formula
}.

Record named_goal : Type := NamedGoal {
  named_assumptions : list named_hypothesis;
  named_conclusion : named_formula
}.

Inductive named_error : Type :=
| NCoreError (error : step_error)
| NUnknownVariable (name : string)
| NHypothesisNotFound (name : string)
| NHypothesisAlreadyUsed (name : string)
| NVariableAlreadyUsed (name : string)
| NMetadataMismatch
| NWrongNamedShape.

Inductive named_result (A : Type) : Type :=
| NOk (value : A)
| NError (error : named_error).

Arguments NOk {A} _.
Arguments NError {A} _.

Definition named_bind {A B}
  (result : named_result A)
  (next : A -> named_result B) : named_result B :=
  match result with
  | NOk value => next value
  | NError error => NError error
  end.

Fixpoint string_mem (name : string) (names : list string) : bool :=
  match names with
  | [] => false
  | candidate :: rest =>
      if String.eqb name candidate then true else string_mem name rest
  end.

Fixpoint string_index_from
  (name : string) (index : nat) (names : list string) : option nat :=
  match names with
  | [] => None
  | candidate :: rest =>
      if String.eqb name candidate then Some index
      else string_index_from name (S index) rest
  end.

Definition string_index (name : string) (names : list string) : option nat :=
  string_index_from name 0 names.

Definition add_name (names : list string) (name : string) : list string :=
  if string_mem name names then names else names ++ [name].

Fixpoint remove_name (name : string) (names : list string) : list string :=
  match names with
  | [] => []
  | candidate :: rest =>
      if String.eqb name candidate
      then remove_name name rest
      else candidate :: remove_name name rest
  end.

Fixpoint merge_names (left right : list string) : list string :=
  match right with
  | [] => left
  | name :: rest => merge_names (add_name left name) rest
  end.

Fixpoint filter_environment
  (excluded environment : list string) : list string :=
  match environment with
  | [] => []
  | name :: rest =>
      if string_mem name excluded
      then filter_environment excluded rest
      else name :: filter_environment excluded rest
  end.

Fixpoint shared_name
  (left right : list string) : option string :=
  match left with
  | [] => None
  | name :: rest =>
      if string_mem name right
      then Some name
      else shared_name rest right
  end.

Definition add_environment_name
  (constants environment : list string) (name : string) : list string :=
  if string_mem name constants then environment else add_name environment name.

Fixpoint named_free_variables (source : named_formula) : list string :=
  match source with
  | NFalsum => []
  | NEqual first second
  | NMember first second => add_name [first] second
  | NConj first second
  | NDisj first second
  | NImpl first second
  | NIff first second =>
      merge_names
        (named_free_variables first)
        (named_free_variables second)
  | NNeg body => named_free_variables body
  | NAll binder body
  | NEx binder body =>
      remove_name binder (named_free_variables body)
  end.

Fixpoint named_binder_names (source : named_formula) : list string :=
  match source with
  | NFalsum
  | NEqual _ _
  | NMember _ _ => []
  | NConj first second
  | NDisj first second
  | NImpl first second
  | NIff first second =>
      named_binder_names first ++ named_binder_names second
  | NNeg body => named_binder_names body
  | NAll binder body
  | NEx binder body =>
      binder :: named_binder_names body
  end.

Definition extend_environment
  (constants environment : list string)
  (source : named_formula) : list string :=
  fold_left (add_environment_name constants)
    (named_free_variables source) environment.

Definition extend_environments
  (constants environment : list string)
  (sources : list named_formula) : list string :=
  fold_left (extend_environment constants) sources environment.

Definition variable_index
  (bound environment : list string)
  (name : string) : named_result nat :=
  match string_index name bound with
  | Some index => NOk index
  | None =>
      match string_index name environment with
      | Some index => NOk (List.length bound + index)
      | None => NError (NUnknownVariable name)
      end
  end.

Definition elaborate_term
  (constants bound environment : list string)
  (name : string) : named_result term :=
  match variable_index bound environment name with
  | NOk index => NOk (Var index)
  | NError _ =>
      if string_mem name constants
      then NOk (Const name)
      else NError (NUnknownVariable name)
  end.

Fixpoint elaborate
  (constants bound environment : list string)
  (source : named_formula) : named_result formula :=
  match source with
  | NFalsum => NOk Falsum
  | NEqual first second =>
      named_bind (elaborate_term constants bound environment first)
        (fun first_term =>
      named_bind (elaborate_term constants bound environment second)
        (fun second_term =>
      NOk (Equal first_term second_term)))
  | NMember first second =>
      named_bind (elaborate_term constants bound environment first)
        (fun first_term =>
      named_bind (elaborate_term constants bound environment second)
        (fun second_term =>
      NOk (Member first_term second_term)))
  | NConj first second =>
      named_bind (elaborate constants bound environment first) (fun first_formula =>
      named_bind (elaborate constants bound environment second) (fun second_formula =>
      NOk (Conj first_formula second_formula)))
  | NDisj first second =>
      named_bind (elaborate constants bound environment first) (fun first_formula =>
      named_bind (elaborate constants bound environment second) (fun second_formula =>
      NOk (Disj first_formula second_formula)))
  | NImpl first second =>
      named_bind (elaborate constants bound environment first) (fun first_formula =>
      named_bind (elaborate constants bound environment second) (fun second_formula =>
      NOk (Impl first_formula second_formula)))
  | NNeg body =>
      named_bind (elaborate constants bound environment body) (fun body_formula =>
      NOk (Neg body_formula))
  | NIff first second =>
      named_bind (elaborate constants bound environment first) (fun first_formula =>
      named_bind (elaborate constants bound environment second) (fun second_formula =>
      NOk (Iff first_formula second_formula)))
  | NAll binder body =>
      if string_mem binder constants
      then NError (NVariableAlreadyUsed binder)
      else
        named_bind (elaborate constants (binder :: bound) environment body)
          (fun body_formula => NOk (All body_formula))
  | NEx binder body =>
      if string_mem binder constants
      then NError (NVariableAlreadyUsed binder)
      else
        named_bind (elaborate constants (binder :: bound) environment body)
          (fun body_formula => NOk (Ex body_formula))
  end.

Definition elaborate_closed
  (constants : list string) (source : named_formula)
  : named_result formula :=
  elaborate constants []
    (filter_environment constants (named_free_variables source)) source.

Definition nth_name
  (bound environment : list string) (index : nat)
  : named_result string :=
  if Nat.ltb index (List.length bound)
  then
    match nth_error bound index with
    | Some name => NOk name
    | None => NError NMetadataMismatch
    end
  else
    match nth_error environment (index - List.length bound) with
    | Some name => NOk name
    | None => NError NMetadataMismatch
    end.

Definition reify_term
  (bound environment : list string) (source : term)
  : named_result string :=
  match source with
  | Var index => nth_name bound environment index
  | Const name => NOk name
  end.

Fixpoint fresh_string_with_fuel
  (fuel : nat) (candidate : string) (used : list string) : string :=
  match fuel with
  | 0 => candidate
  | S remaining =>
      if string_mem candidate used
      then fresh_string_with_fuel remaining (candidate ++ "'") used
      else candidate
  end.

Definition fresh_string (base : string) (used : list string) : string :=
  fresh_string_with_fuel (S (List.length used)) base used.

Definition choose_binder
  (constants bound environment preferred : list string)
  : string * list string :=
  let used := List.app constants (List.app bound environment) in
  match preferred with
  | candidate :: rest =>
      if string_mem candidate used
      then (fresh_string "x" used, rest)
      else (candidate, rest)
  | [] => (fresh_string "x" used, [])
  end.

Fixpoint reify_with_names
  (constants bound environment preferred : list string)
  (source : formula)
  : named_result (named_formula * list string) :=
  match source with
  | Falsum => NOk (NFalsum, preferred)
  | Equal first second =>
      named_bind (reify_term bound environment first) (fun first_name =>
      named_bind (reify_term bound environment second) (fun second_name =>
      NOk (NEqual first_name second_name, preferred)))
  | Member first second =>
      named_bind (reify_term bound environment first) (fun first_name =>
      named_bind (reify_term bound environment second) (fun second_name =>
      NOk (NMember first_name second_name, preferred)))
  | Conj first second =>
      match first, second with
      | Impl first_left first_right,
        Impl second_left second_right =>
          if formula_eqb first_left second_right
             && formula_eqb first_right second_left
          then
            named_bind
              (reify_with_names
                constants bound environment preferred first_left)
              (fun '(left_named, after_left) =>
            named_bind
              (reify_with_names
                constants bound environment after_left first_right)
              (fun '(right_named, after_right) =>
            NOk (NIff left_named right_named, after_right)))
          else
            named_bind
              (reify_with_names constants bound environment preferred first)
              (fun '(first_named, after_first) =>
            named_bind
              (reify_with_names constants bound environment after_first second)
              (fun '(second_named, after_second) =>
            NOk (NConj first_named second_named, after_second)))
      | _, _ =>
          named_bind
            (reify_with_names constants bound environment preferred first)
            (fun '(first_named, after_first) =>
          named_bind
            (reify_with_names constants bound environment after_first second)
            (fun '(second_named, after_second) =>
          NOk (NConj first_named second_named, after_second)))
      end
  | Disj first second =>
      named_bind
        (reify_with_names constants bound environment preferred first)
        (fun '(first_named, after_first) =>
      named_bind
        (reify_with_names constants bound environment after_first second)
        (fun '(second_named, after_second) =>
      NOk (NDisj first_named second_named, after_second)))
  | Impl body Falsum =>
      named_bind
        (reify_with_names constants bound environment preferred body)
        (fun '(body_named, after_body) =>
      NOk (NNeg body_named, after_body))
  | Impl first second =>
      named_bind
        (reify_with_names constants bound environment preferred first)
        (fun '(first_named, after_first) =>
      named_bind
        (reify_with_names constants bound environment after_first second)
        (fun '(second_named, after_second) =>
      NOk (NImpl first_named second_named, after_second)))
  | All body =>
      let '(binder, after_binder) :=
        choose_binder constants bound environment preferred
      in
      named_bind
        (reify_with_names
          constants (binder :: bound) environment after_binder body)
        (fun '(body_named, after_body) =>
      NOk (NAll binder body_named, after_body))
  | Ex body =>
      let '(binder, after_binder) :=
        choose_binder constants bound environment preferred
      in
      named_bind
        (reify_with_names
          constants (binder :: bound) environment after_binder body)
        (fun '(body_named, after_body) =>
      NOk (NEx binder body_named, after_body))
  end.

Definition reify
  (constants environment preferred : list string)
  (source : formula) : named_result named_formula :=
  named_bind (reify_with_names constants [] environment preferred source)
    (fun '(named, _) => NOk named).

Record goal_metadata : Type := GoalMetadata {
  metadata_hypothesis_names : list string;
  metadata_assumption_binders : list (list string);
  metadata_conclusion_binders : list string;
  metadata_environment : list string;
  metadata_constants : list string
}.

Record named_state : Type := NamedState {
  named_kernel_state : proof_state;
  named_goal_metadata : list goal_metadata
}.

Definition initial_metadata_with_assumptions
  (constants environment : list string)
  (named_assumptions : list named_hypothesis)
  (source : named_formula) : goal_metadata :=
  GoalMetadata
    (map named_hypothesis_name named_assumptions)
    (map (fun hypothesis =>
      named_binder_names (named_hypothesis_formula hypothesis))
      named_assumptions)
    (named_binder_names source)
    environment
    constants.

Definition initial_metadata
  (constants : list string) (source : named_formula) : goal_metadata :=
  initial_metadata_with_assumptions constants
    (filter_environment constants (named_free_variables source))
    [] source.

Definition named_start_with_environment
  (constants environment : list string)
  (named_assumptions : list named_hypothesis)
  (core_assumptions : list formula)
  (source : named_formula) : named_result named_state :=
  if Nat.eqb (List.length named_assumptions)
       (List.length core_assumptions)
  then
    named_bind (elaborate constants [] environment source) (fun core =>
    NOk (NamedState
      (start_with_assumptions core_assumptions core)
      [initial_metadata_with_assumptions
        constants environment named_assumptions source]))
  else NError NMetadataMismatch.

Definition named_start_with_constants
  (constants : list string) (source : named_formula)
  : named_result named_state :=
  named_start_with_environment constants
    (filter_environment constants (named_free_variables source))
    [] [] source.

Definition named_start (source : named_formula)
  : named_result named_state :=
  named_start_with_constants [] source.

Example elaborate_global_constant_example :
  elaborate_closed ["empty"] (NEqual "empty" "empty") =
  NOk (Equal (Const "empty") (Const "empty")).
Proof. reflexivity. Qed.

Example reject_constant_shadowing_example :
  elaborate_closed ["empty"] (NAll "empty" (NEqual "empty" "empty")) =
  NError (NVariableAlreadyUsed "empty").
Proof. reflexivity. Qed.

Fixpoint reify_assumptions
  (constants environment : list string)
  (names : list string)
  (binders : list (list string))
  (sources : list formula)
  : named_result (list named_hypothesis) :=
  match names, binders, sources with
  | [], [], [] => NOk []
  | name :: name_rest,
    preferred :: binder_rest,
    source :: source_rest =>
      named_bind (reify constants environment preferred source)
        (fun named_source =>
      named_bind
        (reify_assumptions
          constants environment name_rest binder_rest source_rest)
        (fun rest =>
      NOk (NamedHypothesis name named_source :: rest)))
  | _, _, _ => NError NMetadataMismatch
  end.

Definition reify_goal
  (metadata : goal_metadata) (source : goal)
  : named_result named_goal :=
  named_bind
    (reify_assumptions
      (metadata_constants metadata)
      (metadata_environment metadata)
      (metadata_hypothesis_names metadata)
      (metadata_assumption_binders metadata)
      (assumptions source))
    (fun named_context =>
  named_bind
    (reify
      (metadata_constants metadata)
      (metadata_environment metadata)
      (metadata_conclusion_binders metadata)
      (conclusion source))
    (fun named_target =>
  NOk (NamedGoal named_context named_target))).

Fixpoint reify_goals
  (metadata : list goal_metadata)
  (sources : list goal)
  : named_result (list named_goal) :=
  match metadata, sources with
  | [], [] => NOk []
  | names :: name_rest, source :: source_rest =>
      named_bind (reify_goal names source) (fun named_source =>
      named_bind (reify_goals name_rest source_rest) (fun rest =>
      NOk (named_source :: rest)))
  | _, _ => NError NMetadataMismatch
  end.

Definition named_goals (state : named_state)
  : named_result (list named_goal) :=
  reify_goals
    (named_goal_metadata state)
    (state_goals (named_kernel_state state)).

Definition named_solved (state : named_state) : bool :=
  match named_kernel_state state with
  | [] => true
  | _ => false
  end.

(** Named axioms are capabilities.  Schema predicates retain their local
    binder convention and are elaborated in the environment of the goal where
    [NRAxiom] is executed. *)

Inductive named_fixed_axiom : Type :=
| NEmptySet
| NExtensionality
| NPairing
| NUnion
| NPowerSet
| NFoundation
| NInfinity
| NChoice.

Inductive named_axiom : Type :=
| NFixedAxiom (kind : named_fixed_axiom)
| NSeparationAxiom
    (source element : string) (predicate : named_formula)
| NReplacementAxiom
    (input output : string) (predicate : named_formula).

Definition fixed_axiom_formula (kind : named_fixed_axiom) : formula :=
  match kind with
  | NEmptySet => empty_set_axiom
  | NExtensionality => extensionality_axiom
  | NPairing => pairing_axiom
  | NUnion => union_axiom
  | NPowerSet => power_set_axiom
  | NFoundation => foundation_axiom
  | NInfinity => infinity_axiom
  | NChoice => choice_axiom
  end.

Definition elaborate_schema_predicate
  (constants binders environment : list string)
  (predicate : named_formula) : named_result formula :=
  match shared_name binders constants with
  | Some name => NError (NVariableAlreadyUsed name)
  | None =>
      elaborate constants binders
        (filter_environment binders environment) predicate
  end.

Definition compile_axiom
  (constants environment : list string) (axiom : named_axiom)
  : named_result formula :=
  match axiom with
  | NFixedAxiom kind => NOk (fixed_axiom_formula kind)
  | NSeparationAxiom source element predicate =>
      named_bind
        (elaborate_schema_predicate
          constants [element; source] environment predicate)
        (fun core_predicate =>
      NOk (separation_instance core_predicate))
  | NReplacementAxiom input output predicate =>
      named_bind
        (elaborate_schema_predicate
          constants [output; input] environment predicate)
        (fun core_predicate =>
      NOk (replacement_instance core_predicate))
  end.

Fixpoint compile_axioms
  (constants environment : list string) (axioms : list named_axiom)
  : named_result (list formula) :=
  match axioms with
  | [] => NOk []
  | axiom :: rest =>
      named_bind (compile_axiom constants environment axiom) (fun core_axiom =>
      named_bind (compile_axioms constants environment rest) (fun core_rest =>
      NOk (core_axiom :: core_rest)))
  end.

Fixpoint formula_in (candidate : formula) (axioms : list formula) : bool :=
  match axioms with
  | [] => false
  | axiom :: rest =>
      formula_eqb axiom candidate || formula_in candidate rest
  end.

(** Every primitive rule carries precisely the names needed to reify its
    generated goals.  Logical formulas are still checked by the core rule. *)

Inductive named_rule : Type :=
| NRAxiom
| NRHypothesis (hypothesis : string)
| NRFalsumElim
| NRImplIntro (hypothesis : string)
| NRImplElim (premise : named_formula)
| NRConjIntro
| NRConjElimL (right : named_formula)
| NRConjElimR (left : named_formula)
| NRDisjIntroL
| NRDisjIntroR
| NRDisjElim
    (left right : named_formula)
    (left_hypothesis right_hypothesis : string)
| NRAllIntro (variable : string)
| NRAllElim (term : string) (universal : named_formula)
| NRExIntro (term : string)
| NRExElim
    (witness hypothesis : string)
    (existential : named_formula)
| NREqualRefl
| NREqualElim
    (left right : string)
    (predicate : named_formula)
| NRCut (hypothesis : string) (lemma : named_formula).

Record rule_plan : Type := RulePlan {
  planned_rule : rule;
  planned_generated_metadata : list goal_metadata;
  planned_environment : list string
}.

Definition metadata_with_conclusion
  (metadata : goal_metadata)
  (binders environment : list string) : goal_metadata :=
  GoalMetadata
    (metadata_hypothesis_names metadata)
    (metadata_assumption_binders metadata)
    binders
    environment
    (metadata_constants metadata).

Definition metadata_with_hypothesis
  (metadata : goal_metadata)
  (hypothesis : string)
  (hypothesis_binders conclusion_binders environment : list string)
  : goal_metadata :=
  GoalMetadata
    (hypothesis :: metadata_hypothesis_names metadata)
    (hypothesis_binders :: metadata_assumption_binders metadata)
    conclusion_binders
    environment
    (metadata_constants metadata).

Definition ensure_hypothesis_fresh
  (metadata : goal_metadata) (name : string)
  : named_result unit :=
  if string_mem name (metadata_hypothesis_names metadata)
  then NError (NHypothesisAlreadyUsed name)
  else NOk tt.

Definition ensure_variable_fresh
  (metadata : goal_metadata) (name : string)
  : named_result unit :=
  if string_mem name (metadata_constants metadata)
     || string_mem name (metadata_environment metadata)
  then NError (NVariableAlreadyUsed name)
  else NOk tt.

Definition hypothesis_index
  (metadata : goal_metadata) (name : string)
  : named_result nat :=
  match string_index name (metadata_hypothesis_names metadata) with
  | Some index => NOk index
  | None => NError (NHypothesisNotFound name)
  end.

Fixpoint find_named_hypothesis
  (name : string) (context : list named_hypothesis)
  : option named_formula :=
  match context with
  | [] => None
  | hypothesis :: rest =>
      if String.eqb name (named_hypothesis_name hypothesis)
      then Some (named_hypothesis_formula hypothesis)
      else find_named_hypothesis name rest
  end.

Definition elaborate_in_environment
  (constants environment : list string) (source : named_formula)
  : named_result formula :=
  elaborate constants [] environment source.

Definition term_index
  (constants environment : list string) (source : string)
  : named_result term :=
  elaborate_term constants [] environment source.

Definition plan_named_rule
  (metadata : goal_metadata)
  (view : named_goal)
  (primitive : named_rule)
  : named_result rule_plan :=
  let constants := metadata_constants metadata in
  let environment := metadata_environment metadata in
  let target := named_conclusion view in
  match primitive with
  | NRAxiom =>
      NOk (RulePlan RAxiom [] environment)
  | NRHypothesis hypothesis =>
      named_bind (hypothesis_index metadata hypothesis) (fun index =>
      NOk (RulePlan (RHypothesis index) [] environment))
  | NRFalsumElim =>
      NOk (RulePlan RFalsumElim
        [metadata_with_conclusion metadata [] environment]
        environment)
  | NRImplIntro hypothesis =>
      named_bind (ensure_hypothesis_fresh metadata hypothesis) (fun _ =>
      match target with
      | NImpl premise conclusion =>
          NOk (RulePlan RImplIntro
            [metadata_with_hypothesis metadata hypothesis
              (named_binder_names premise)
              (named_binder_names conclusion)
              environment]
            environment)
      | NNeg premise =>
          NOk (RulePlan RImplIntro
            [metadata_with_hypothesis metadata hypothesis
              (named_binder_names premise) [] environment]
            environment)
      | _ => NError NWrongNamedShape
      end)
  | NRImplElim premise =>
      let next_environment :=
        extend_environment constants environment premise in
      named_bind
        (elaborate_in_environment constants next_environment premise)
        (fun core_premise =>
      NOk (RulePlan (RImplElim core_premise)
        [metadata_with_conclusion metadata
           (named_binder_names premise
              ++ metadata_conclusion_binders metadata)
           next_environment;
         metadata_with_conclusion metadata
           (named_binder_names premise)
           next_environment]
        next_environment))
  | NRConjIntro =>
      match target with
      | NConj first second =>
          NOk (RulePlan RConjIntro
            [metadata_with_conclusion metadata
               (named_binder_names first) environment;
             metadata_with_conclusion metadata
               (named_binder_names second) environment]
            environment)
      | NIff first second =>
          NOk (RulePlan RConjIntro
            [metadata_with_conclusion metadata
               (named_binder_names
                 (NImpl first second)) environment;
             metadata_with_conclusion metadata
               (named_binder_names
                 (NImpl second first)) environment]
            environment)
      | _ => NError NWrongNamedShape
      end
  | NRConjElimL extra =>
      let next_environment :=
        extend_environment constants environment extra in
      named_bind (elaborate_in_environment constants next_environment extra)
        (fun core_extra =>
      NOk (RulePlan (RConjElimL core_extra)
        [metadata_with_conclusion metadata
           (metadata_conclusion_binders metadata
              ++ named_binder_names extra)
           next_environment]
        next_environment))
  | NRConjElimR extra =>
      let next_environment :=
        extend_environment constants environment extra in
      named_bind (elaborate_in_environment constants next_environment extra)
        (fun core_extra =>
      NOk (RulePlan (RConjElimR core_extra)
        [metadata_with_conclusion metadata
           (named_binder_names extra
              ++ metadata_conclusion_binders metadata)
           next_environment]
        next_environment))
  | NRDisjIntroL =>
      match target with
      | NDisj first _ =>
          NOk (RulePlan RDisjIntroL
            [metadata_with_conclusion metadata
               (named_binder_names first) environment]
            environment)
      | _ => NError NWrongNamedShape
      end
  | NRDisjIntroR =>
      match target with
      | NDisj _ second =>
          NOk (RulePlan RDisjIntroR
            [metadata_with_conclusion metadata
               (named_binder_names second) environment]
            environment)
      | _ => NError NWrongNamedShape
      end
  | NRDisjElim first second first_name second_name =>
      named_bind (ensure_hypothesis_fresh metadata first_name) (fun _ =>
      named_bind (ensure_hypothesis_fresh metadata second_name) (fun _ =>
      if String.eqb first_name second_name
      then NError (NHypothesisAlreadyUsed second_name)
      else
        let next_environment :=
          extend_environments constants environment [first; second]
        in
        named_bind
          (elaborate_in_environment constants next_environment first)
          (fun core_first =>
        named_bind
          (elaborate_in_environment constants next_environment second)
          (fun core_second =>
        NOk (RulePlan (RDisjElim core_first core_second)
          [metadata_with_conclusion metadata
             (named_binder_names (NDisj first second))
             next_environment;
           metadata_with_hypothesis metadata first_name
             (named_binder_names first)
             (metadata_conclusion_binders metadata)
             next_environment;
           metadata_with_hypothesis metadata second_name
             (named_binder_names second)
             (metadata_conclusion_binders metadata)
             next_environment]
          next_environment)))))
  | NRAllIntro variable =>
      named_bind (ensure_variable_fresh metadata variable) (fun _ =>
      match target with
      | NAll _ body =>
          let next_environment := variable :: environment in
          NOk (RulePlan RAllIntro
            [metadata_with_conclusion metadata
               (named_binder_names body) next_environment]
            next_environment)
      | _ => NError NWrongNamedShape
      end)
  | NRAllElim term universal =>
      match universal with
      | NAll binder body =>
          let next_environment :=
            add_environment_name constants
              (extend_environment constants environment universal) term
          in
          named_bind
            (elaborate constants [binder] next_environment body)
            (fun core_body =>
          named_bind (term_index constants next_environment term)
            (fun core_term =>
          NOk (RulePlan (RAllElim core_body core_term)
            [metadata_with_conclusion metadata
               (named_binder_names universal) next_environment]
            next_environment)))
      | _ => NError NWrongNamedShape
      end
  | NRExIntro term =>
      match target with
      | NEx _ body =>
          let next_environment :=
            add_environment_name constants environment term in
          named_bind (term_index constants next_environment term)
            (fun core_term =>
          NOk (RulePlan (RExIntro core_term)
            [metadata_with_conclusion metadata
               (named_binder_names body) next_environment]
            next_environment))
      | _ => NError NWrongNamedShape
      end
  | NRExElim witness hypothesis existential =>
      named_bind (ensure_hypothesis_fresh metadata hypothesis) (fun _ =>
      match existential with
      | NEx binder body =>
          let before_environment :=
            extend_environment constants environment existential
          in
          if string_mem witness constants
             || string_mem witness before_environment
          then NError (NVariableAlreadyUsed witness)
          else
            let generated_environment :=
              witness :: before_environment
            in
            named_bind
              (elaborate constants [binder] before_environment body)
              (fun core_body =>
            NOk (RulePlan (RExElim core_body)
              [metadata_with_conclusion metadata
                 (named_binder_names existential)
                 before_environment;
               metadata_with_hypothesis metadata hypothesis
                 (named_binder_names body)
                 (metadata_conclusion_binders metadata)
                 generated_environment]
              before_environment))
      | _ => NError NWrongNamedShape
      end)
  | NREqualRefl =>
      NOk (RulePlan REqualRefl [] environment)
  | NREqualElim first second predicate =>
      match predicate with
      | NAll binder body =>
          let next_environment :=
            add_environment_name constants
              (add_environment_name constants
                (extend_environment constants environment predicate) first)
              second
          in
          named_bind
            (elaborate constants [binder] next_environment body)
            (fun core_predicate =>
          named_bind (term_index constants next_environment first)
            (fun core_first =>
          named_bind (term_index constants next_environment second)
            (fun core_second =>
          NOk (RulePlan
            (REqualElim core_predicate core_first core_second)
            [metadata_with_conclusion metadata [] next_environment;
             metadata_with_conclusion metadata
               (named_binder_names body) next_environment]
            next_environment))))
      | _ => NError NWrongNamedShape
      end
  | NRCut hypothesis lemma =>
      named_bind (ensure_hypothesis_fresh metadata hypothesis) (fun _ =>
      let next_environment :=
        extend_environment constants environment lemma in
      named_bind
        (elaborate_in_environment constants next_environment lemma)
        (fun core_lemma =>
      NOk (RulePlan (RCut core_lemma)
        [metadata_with_conclusion metadata
           (named_binder_names lemma) next_environment;
         metadata_with_hypothesis metadata hypothesis
           (named_binder_names lemma)
           (metadata_conclusion_binders metadata)
           next_environment]
        next_environment)))
  end.

Definition named_rule_step
  (axioms : list named_axiom)
  (primitive : named_rule)
  (state : named_state) : named_result named_state :=
  match
    named_kernel_state state,
    named_goal_metadata state
  with
  | [], [] => NError (NCoreError NoGoals)
  | goal :: _, metadata :: metadata_rest =>
      named_bind (reify_goal metadata goal) (fun view =>
      named_bind (plan_named_rule metadata view primitive) (fun plan =>
      named_bind
        (compile_axioms
          (metadata_constants metadata)
          (planned_environment plan) axioms)
        (fun core_axioms =>
      match
        TacticCompleteness.rule_step
          (fun candidate => formula_in candidate core_axioms)
          (planned_rule plan)
          (named_kernel_state state)
      with
      | Success next =>
          NOk (NamedState next
            (planned_generated_metadata plan ++ metadata_rest))
      | Failure error => NError (NCoreError error)
      end)))
  | _, _ => NError NMetadataMismatch
  end.

Fixpoint named_rule_run
  (axioms : list named_axiom)
  (rules : list named_rule)
  (state : named_state) : named_result named_state :=
  match rules with
  | [] => NOk state
  | primitive :: rest =>
      named_bind (named_rule_step axioms primitive state)
        (fun next => named_rule_run axioms rest next)
  end.

Inductive named_tactic : Type :=
| NTacRule (primitive : named_rule)
| NTacIntro (name : string)
| NTacExact (hypothesis : string)
| NTacApply (hypothesis : string)
| NTacSpecialize
    (hypothesis term new_hypothesis : string)
| NTacSplit
| NTacLeft
| NTacRight
| NTacUse (term : string)
| NTacRefl
| NTacContradiction
| NTacCases
    (hypothesis first_name second_name : string).

Record tactic_plan : Type := TacticPlan {
  planned_tactic : tactic;
  tactic_generated_metadata : list goal_metadata;
  tactic_environment : list string
}.

Definition plan_named_tactic
  (metadata : goal_metadata)
  (view : named_goal)
  (command : named_tactic)
  : named_result tactic_plan :=
  let constants := metadata_constants metadata in
  let environment := metadata_environment metadata in
  let target := named_conclusion view in
  match command with
  | NTacRule _ => NError NWrongNamedShape
  | NTacIntro name =>
      match target with
      | NImpl premise conclusion =>
          named_bind (ensure_hypothesis_fresh metadata name) (fun _ =>
          NOk (TacticPlan TacIntro
            [metadata_with_hypothesis metadata name
              (named_binder_names premise)
              (named_binder_names conclusion)
              environment]
            environment))
      | NNeg premise =>
          named_bind (ensure_hypothesis_fresh metadata name) (fun _ =>
          NOk (TacticPlan TacIntro
            [metadata_with_hypothesis metadata name
              (named_binder_names premise) [] environment]
            environment))
      | NAll _ body =>
          named_bind (ensure_variable_fresh metadata name) (fun _ =>
          let next_environment := name :: environment in
          NOk (TacticPlan TacIntro
            [metadata_with_conclusion metadata
              (named_binder_names body) next_environment]
            next_environment))
      | _ => NError NWrongNamedShape
      end
  | NTacExact hypothesis =>
      named_bind (hypothesis_index metadata hypothesis) (fun index =>
      NOk (TacticPlan (TacExact index) [] environment))
  | NTacApply hypothesis =>
      named_bind (hypothesis_index metadata hypothesis) (fun index =>
      match find_named_hypothesis hypothesis (named_assumptions view) with
      | Some (NImpl premise _) =>
          NOk (TacticPlan (TacApply index)
            [metadata_with_conclusion metadata
              (named_binder_names premise) environment]
            environment)
      | Some (NNeg premise) =>
          NOk (TacticPlan (TacApply index)
            [metadata_with_conclusion metadata
              (named_binder_names premise) environment]
            environment)
      | Some _ => NError NWrongNamedShape
      | None => NError (NHypothesisNotFound hypothesis)
      end)
  | NTacSpecialize hypothesis term new_hypothesis =>
      named_bind
        (ensure_hypothesis_fresh metadata new_hypothesis)
        (fun _ =>
      named_bind (hypothesis_index metadata hypothesis) (fun index =>
      match find_named_hypothesis hypothesis (named_assumptions view) with
      | Some (NAll _ body) =>
          let next_environment :=
            add_environment_name constants environment term in
          named_bind (term_index constants next_environment term)
            (fun core_term =>
          NOk (TacticPlan (TacSpecialize index core_term)
            [metadata_with_hypothesis metadata new_hypothesis
              (named_binder_names body)
              (metadata_conclusion_binders metadata)
              next_environment]
            next_environment))
      | Some _ => NError NWrongNamedShape
      | None => NError (NHypothesisNotFound hypothesis)
      end))
  | NTacSplit =>
      match target with
      | NConj first second =>
          NOk (TacticPlan TacSplit
            [metadata_with_conclusion metadata
               (named_binder_names first) environment;
             metadata_with_conclusion metadata
               (named_binder_names second) environment]
            environment)
      | NIff first second =>
          NOk (TacticPlan TacSplit
            [metadata_with_conclusion metadata
               (named_binder_names (NImpl first second)) environment;
             metadata_with_conclusion metadata
               (named_binder_names (NImpl second first)) environment]
            environment)
      | _ => NError NWrongNamedShape
      end
  | NTacLeft =>
      match target with
      | NDisj first _ =>
          NOk (TacticPlan TacLeft
            [metadata_with_conclusion metadata
              (named_binder_names first) environment]
            environment)
      | _ => NError NWrongNamedShape
      end
  | NTacRight =>
      match target with
      | NDisj _ second =>
          NOk (TacticPlan TacRight
            [metadata_with_conclusion metadata
              (named_binder_names second) environment]
            environment)
      | _ => NError NWrongNamedShape
      end
  | NTacUse term =>
      match target with
      | NEx _ body =>
          let next_environment :=
            add_environment_name constants environment term in
          named_bind (term_index constants next_environment term)
            (fun core_term =>
          NOk (TacticPlan (TacUse core_term)
            [metadata_with_conclusion metadata
              (named_binder_names body) next_environment]
            next_environment))
      | _ => NError NWrongNamedShape
      end
  | NTacRefl =>
      NOk (TacticPlan TacRefl [] environment)
  | NTacContradiction =>
      NOk (TacticPlan TacContradiction [] environment)
  | NTacCases hypothesis first_name second_name =>
      named_bind (hypothesis_index metadata hypothesis) (fun index =>
      match find_named_hypothesis hypothesis (named_assumptions view) with
      | Some (NConj first second) =>
          named_bind
            (ensure_hypothesis_fresh metadata first_name) (fun _ =>
          named_bind
            (ensure_hypothesis_fresh metadata second_name) (fun _ =>
          if String.eqb first_name second_name
          then NError (NHypothesisAlreadyUsed second_name)
          else
            NOk (TacticPlan (TacCases index)
              [GoalMetadata
                (second_name :: first_name ::
                   metadata_hypothesis_names metadata)
                (named_binder_names second ::
                   named_binder_names first ::
                   metadata_assumption_binders metadata)
                (metadata_conclusion_binders metadata)
                environment
                constants]
              environment)))
      | Some (NIff first second) =>
          named_bind
            (ensure_hypothesis_fresh metadata first_name) (fun _ =>
          named_bind
            (ensure_hypothesis_fresh metadata second_name) (fun _ =>
          if String.eqb first_name second_name
          then NError (NHypothesisAlreadyUsed second_name)
          else
            NOk (TacticPlan (TacCases index)
              [GoalMetadata
                (second_name :: first_name ::
                   metadata_hypothesis_names metadata)
                (named_binder_names (NImpl second first) ::
                   named_binder_names (NImpl first second) ::
                   metadata_assumption_binders metadata)
                (metadata_conclusion_binders metadata)
                environment
                constants]
              environment)))
      | Some (NEx _ body) =>
          named_bind
            (ensure_hypothesis_fresh metadata second_name) (fun _ =>
          named_bind (ensure_variable_fresh metadata first_name) (fun _ =>
          let next_environment := first_name :: environment in
          NOk (TacticPlan (TacCases index)
            [metadata_with_hypothesis metadata second_name
              (named_binder_names body)
              (metadata_conclusion_binders metadata)
              next_environment]
            next_environment)))
      | Some _ => NError NWrongNamedShape
      | None => NError (NHypothesisNotFound hypothesis)
      end)
  end.

Definition named_tactic_step
  (command : named_tactic)
  (state : named_state) : named_result named_state :=
  match
    named_kernel_state state,
    named_goal_metadata state
  with
  | [], [] => NError (NCoreError NoGoals)
  | goal :: _, metadata :: metadata_rest =>
      named_bind (reify_goal metadata goal) (fun view =>
      named_bind
        (plan_named_tactic metadata view command)
        (fun plan =>
      match
        ProofState.step
          (fun _ => false)
          (planned_tactic plan)
          (named_kernel_state state)
      with
      | Success next =>
          NOk (NamedState next
            (tactic_generated_metadata plan ++ metadata_rest))
      | Failure error => NError (NCoreError error)
      end))
  | _, _ => NError NMetadataMismatch
  end.

Definition named_step
  (axioms : list named_axiom)
  (command : named_tactic)
  (state : named_state) : named_result named_state :=
  match command with
  | NTacRule primitive => named_rule_step axioms primitive state
  | _ => named_tactic_step command state
  end.

Fixpoint named_run
  (axioms : list named_axiom)
  (commands : list named_tactic)
  (state : named_state) : named_result named_state :=
  match commands with
  | [] => NOk state
  | command :: rest =>
      named_bind (named_step axioms command state)
        (fun next => named_run axioms rest next)
  end.

(** The named machine does not introduce a second proof theory: successful
    transitions refine the underlying de Bruijn state by the already-proved
    core soundness theorems. *)

Definition named_state_provable
  (T : theory) (state : named_state) : Prop :=
  state_provable T (named_kernel_state state).

Definition named_axioms_sound
  (T : theory) (axioms : list named_axiom) : Prop :=
  forall constants environment core_axioms,
    compile_axioms constants environment axioms = NOk core_axioms ->
    forall candidate,
      formula_in candidate core_axioms = true ->
      T candidate.

Theorem named_rule_step_sound :
  forall T axioms primitive state next,
    named_axioms_sound T axioms ->
    named_rule_step axioms primitive state = NOk next ->
    named_state_provable T next ->
    named_state_provable T state.
Proof.
  intros T axioms primitive state next Haxioms Hstep Hnext.
  unfold named_rule_step in Hstep.
  destruct (named_kernel_state state) as [|g rest] eqn:Hkernel.
  - destruct (named_goal_metadata state)
      as [|metadata metadata_rest] eqn:Hmetadata;
      cbn in Hstep; discriminate.
  - destruct (named_goal_metadata state)
      as [|metadata metadata_rest] eqn:Hmetadata.
    + cbn in Hstep. discriminate.
    + destruct (reify_goal metadata g) as [view | view_error]
        eqn:Hview.
      * destruct (plan_named_rule metadata view primitive)
          as [plan | plan_error] eqn:Hplan.
        -- destruct (compile_axioms
             (metadata_constants metadata)
             (planned_environment plan) axioms)
             as [core_axioms | axiom_error] eqn:Hcompile.
           ++ destruct
                (TacticCompleteness.rule_step
                  (fun candidate => formula_in candidate core_axioms)
                  (planned_rule plan)
                  (named_kernel_state state))
                as [core_next | core_error] eqn:Hcore.
              ** pose proof Hcore as Hcore_step.
                 cbn in Hstep.
                 rewrite Hplan in Hstep. cbn in Hstep.
                 rewrite Hcompile in Hstep. cbn in Hstep.
                 rewrite Hkernel in Hcore. cbn in Hcore.
                 rewrite Hcore in Hstep. cbn in Hstep.
                 inversion Hstep; subst.
                 unfold named_state_provable in *; simpl in Hnext.
                 assert (Hchecker :
                   forall candidate,
                     (fun candidate =>
                       formula_in candidate core_axioms) candidate = true ->
                     T candidate).
                 {
                   intros candidate Hcandidate.
                   unfold named_axioms_sound in Haxioms.
                   eapply Haxioms.
                   - exact Hcompile.
                   - exact Hcandidate.
                 }
                 eapply TacticCompleteness.rule_step_sound.
                 --- exact Hchecker.
                 --- exact Hcore_step.
                 --- exact Hnext.
              ** cbn in Hstep.
                 rewrite Hplan in Hstep. cbn in Hstep.
                 rewrite Hcompile in Hstep. cbn in Hstep.
                 rewrite Hkernel in Hcore. cbn in Hcore.
                 rewrite Hcore in Hstep. discriminate.
           ++ cbn in Hstep.
              rewrite Hplan in Hstep. cbn in Hstep.
              rewrite Hcompile in Hstep. discriminate.
        -- cbn in Hstep.
           rewrite Hplan in Hstep. discriminate.
      * cbn in Hstep. discriminate.
Qed.

Theorem named_rule_run_sound :
  forall T axioms rules state final,
    named_axioms_sound T axioms ->
    named_rule_run axioms rules state = NOk final ->
    named_state_provable T final ->
    named_state_provable T state.
Proof.
  intros T axioms rules.
  induction rules as [|primitive rest IH];
    intros state final Haxioms Hrun Hfinal; simpl in Hrun.
  - inversion Hrun. exact Hfinal.
  - destruct (named_rule_step axioms primitive state)
      as [next | error] eqn:Hstep; try discriminate.
    eapply named_rule_step_sound.
    + exact Haxioms.
    + exact Hstep.
    + eapply IH; eauto.
Qed.

Lemma false_checker_sound :
  forall T candidate,
    (fun _ : formula => false) candidate = true ->
    T candidate.
Proof.
  intros T candidate Hfalse. discriminate.
Qed.

Theorem named_tactic_step_sound :
  forall T command state next,
    named_tactic_step command state = NOk next ->
    named_state_provable T next ->
    named_state_provable T state.
Proof.
  intros T command state next Hstep Hnext.
  unfold named_tactic_step in Hstep.
  destruct (named_kernel_state state) as [|g rest] eqn:Hkernel.
  - destruct (named_goal_metadata state)
      as [|metadata metadata_rest] eqn:Hmetadata;
      cbn in Hstep; discriminate.
  - destruct (named_goal_metadata state)
      as [|metadata metadata_rest] eqn:Hmetadata.
    + cbn in Hstep. discriminate.
    + destruct (reify_goal metadata g) as [view | view_error]
        eqn:Hview.
      * destruct (plan_named_tactic metadata view command)
          as [plan | plan_error] eqn:Hplan.
        -- destruct
             (ProofState.step
               (fun _ => false)
               (planned_tactic plan)
               (named_kernel_state state))
             as [core_next | core_error] eqn:Hcore.
           ++ pose proof Hcore as Hcore_step.
              cbn in Hstep.
              rewrite Hplan in Hstep. cbn in Hstep.
              rewrite Hkernel in Hcore. cbn in Hcore.
              rewrite Hcore in Hstep. cbn in Hstep.
              inversion Hstep; subst.
              unfold named_state_provable in *; simpl in Hnext.
              eapply ProofState.step_sound.
              ** apply false_checker_sound.
              ** exact Hcore_step.
              ** exact Hnext.
           ++ cbn in Hstep.
              rewrite Hplan in Hstep. cbn in Hstep.
              rewrite Hkernel in Hcore. cbn in Hcore.
              rewrite Hcore in Hstep. discriminate.
        -- cbn in Hstep.
           rewrite Hplan in Hstep. discriminate.
      * cbn in Hstep. discriminate.
Qed.

Theorem named_step_sound :
  forall T axioms command state next,
    named_axioms_sound T axioms ->
    named_step axioms command state = NOk next ->
    named_state_provable T next ->
    named_state_provable T state.
Proof.
  intros T axioms command state next Haxioms Hstep Hnext.
  destruct command; simpl in Hstep.
  - eapply named_rule_step_sound; eauto.
  - eapply named_tactic_step_sound; eauto.
  - eapply named_tactic_step_sound; eauto.
  - eapply named_tactic_step_sound; eauto.
  - eapply named_tactic_step_sound; eauto.
  - eapply named_tactic_step_sound; eauto.
  - eapply named_tactic_step_sound; eauto.
  - eapply named_tactic_step_sound; eauto.
  - eapply named_tactic_step_sound; eauto.
  - eapply named_tactic_step_sound; eauto.
  - eapply named_tactic_step_sound; eauto.
  - eapply named_tactic_step_sound; eauto.
Qed.

Theorem named_run_sound :
  forall T axioms commands state final,
    named_axioms_sound T axioms ->
    named_run axioms commands state = NOk final ->
    named_state_provable T final ->
    named_state_provable T state.
Proof.
  intros T axioms commands.
  induction commands as [|command rest IH];
    intros state final Haxioms Hrun Hfinal; simpl in Hrun.
  - inversion Hrun. exact Hfinal.
  - destruct (named_step axioms command state)
      as [next | error] eqn:Hstep; try discriminate.
    eapply named_step_sound.
    + exact Haxioms.
    + exact Hstep.
    + eapply IH; eauto.
Qed.

Lemma formula_in_correct :
  forall candidate axioms,
    formula_in candidate axioms = true ->
    In candidate axioms.
Proof.
  intros candidate axioms.
  induction axioms as [|axiom rest IH]; simpl.
  - discriminate.
  - rewrite Bool.orb_true_iff.
    intros [Hequal | Hin].
    + apply formula_eqb_true_iff in Hequal.
      left. congruence.
    + right. apply IH. exact Hin.
Qed.

Lemma compile_axiom_is_zfc :
  forall constants environment axiom core_axiom,
    compile_axiom constants environment axiom = NOk core_axiom ->
    zfc_theory core_axiom.
Proof.
  intros constants environment axiom core_axiom Hcompile.
  destruct axiom as
    [kind
    |source element predicate
    |input output predicate].
  - destruct kind; cbn in Hcompile; inversion Hcompile; subst;
      apply ZFC_set_axiom; constructor.
  - cbn in Hcompile.
    destruct
      (elaborate_schema_predicate
        constants [element; source] environment predicate)
      as [core_predicate | error] eqn:Hpredicate;
      try discriminate.
    inversion Hcompile; subst.
    apply ZFC_set_axiom. apply ZFC_separation.
  - cbn in Hcompile.
    destruct
      (elaborate_schema_predicate
        constants [output; input] environment predicate)
      as [core_predicate | error] eqn:Hpredicate;
      try discriminate.
    inversion Hcompile; subst.
    apply ZFC_set_axiom. apply ZFC_replacement.
Qed.

Lemma compile_axioms_are_zfc :
  forall constants environment axioms core_axioms,
    compile_axioms constants environment axioms = NOk core_axioms ->
    forall candidate,
      In candidate core_axioms ->
      zfc_theory candidate.
Proof.
  intros constants environment axioms.
  induction axioms as [|axiom rest IH];
    intros core_axioms Hcompile candidate Hin.
  - cbn in Hcompile. inversion Hcompile; subst. inversion Hin.
  - cbn in Hcompile.
    destruct (compile_axiom constants environment axiom)
      as [core_axiom | axiom_error] eqn:Haxiom;
      try discriminate.
    destruct (compile_axioms constants environment rest)
      as [core_rest | rest_error] eqn:Hrest;
      try discriminate.
    inversion Hcompile; subst.
    destruct Hin as [<- | Hin].
    + eapply compile_axiom_is_zfc. exact Haxiom.
    + eapply IH; eauto.
Qed.

Theorem named_axioms_are_zfc_sound :
  forall axioms,
    named_axioms_sound zfc_theory axioms.
Proof.
  intros axioms constants environment core_axioms
    Hcompile candidate Hcandidate.
  eapply compile_axioms_are_zfc.
  - exact Hcompile.
  - apply formula_in_correct. exact Hcandidate.
Qed.

Corollary named_zfc_rule_run_sound :
  forall axioms rules state final,
    named_rule_run axioms rules state = NOk final ->
    named_state_provable zfc_theory final ->
    named_state_provable zfc_theory state.
Proof.
  intros axioms rules state final Hrun Hfinal.
  eapply named_rule_run_sound.
  - apply named_axioms_are_zfc_sound.
  - exact Hrun.
  - exact Hfinal.
Qed.

Corollary named_zfc_run_sound :
  forall axioms commands state final,
    named_run axioms commands state = NOk final ->
    named_state_provable zfc_theory final ->
    named_state_provable zfc_theory state.
Proof.
  intros axioms commands state final Hrun Hfinal.
  eapply named_run_sound.
  - apply named_axioms_are_zfc_sound.
  - exact Hrun.
  - exact Hfinal.
Qed.
