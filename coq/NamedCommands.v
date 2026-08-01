(** Extractable named commands whose elaboration depends on ZFC axioms.

    The OCaml layer supplies only parsed names and formulas.  Construction of
    schema instances, fresh internal names, and the primitive rule sequences
    that justify the surface commands all live here.
 *)

From Coq Require Import List String.
From ZFCert Require Import ProofState NamedProofState ZFC.
Import ListNotations.
Open Scope string_scope.

Fixpoint named_all_variables (source : named_formula) : list string :=
  match source with
  | NFalsum => []
  | NEqual first second
  | NMember first second =>
      merge_names (named_term_names first) (named_term_names second)
  | NConj first second
  | NDisj first second
  | NImpl first second
  | NIff first second =>
      merge_names
        (named_all_variables first)
        (named_all_variables second)
  | NNeg body => named_all_variables body
  | NAll binder body
  | NEx binder body =>
      add_name (named_all_variables body) binder
  end.

Fixpoint named_substitute_variable
  (variable replacement : string)
  (source : named_formula) : named_formula :=
  match source with
  | NFalsum => NFalsum
  | NEqual first second =>
      NEqual (named_term_subst variable replacement first)
        (named_term_subst variable replacement second)
  | NMember first second =>
      NMember (named_term_subst variable replacement first)
        (named_term_subst variable replacement second)
  | NConj first second =>
      NConj
        (named_substitute_variable variable replacement first)
        (named_substitute_variable variable replacement second)
  | NDisj first second =>
      NDisj
        (named_substitute_variable variable replacement first)
        (named_substitute_variable variable replacement second)
  | NImpl first second =>
      NImpl
        (named_substitute_variable variable replacement first)
        (named_substitute_variable variable replacement second)
  | NNeg body =>
      NNeg (named_substitute_variable variable replacement body)
  | NIff first second =>
      NIff
        (named_substitute_variable variable replacement first)
        (named_substitute_variable variable replacement second)
  | NAll binder body =>
      if String.eqb binder variable
      then NAll binder body
      else NAll binder
        (named_substitute_variable variable replacement body)
  | NEx binder body =>
      if String.eqb binder variable
      then NEx binder body
      else NEx binder
        (named_substitute_variable variable replacement body)
  end.

Definition named_separation_instance
  (source element : string) (predicate : named_formula)
  : named_formula :=
  let used :=
    add_name
      (add_name (named_all_variables predicate) source)
      element
  in
  let subset := fresh_string "b" used in
  NEx subset
    (NAll element
      (NIff
        (NMember element subset)
        (NConj (NMember element source) predicate))).

Record named_replacement_parts : Type := NamedReplacementParts {
  named_replacement_functional : named_formula;
  named_replacement_image : named_formula;
  named_replacement_instance : named_formula
}.

Definition make_named_replacement_parts
  (source input output : string) (predicate : named_formula)
  : named_replacement_parts :=
  let used :=
    add_name
      (add_name
        (add_name (named_all_variables predicate) source)
        input)
      output
  in
  let alternate := fresh_string "z" used in
  let image_set := fresh_string "b" (add_name used alternate) in
  let alternate_predicate :=
    named_substitute_variable output alternate predicate
  in
  let functional :=
    NAll input
      (NEx output
        (NConj predicate
          (NAll alternate
            (NImpl alternate_predicate
              (NEqual alternate output)))))
  in
  let image :=
    NEx image_set
      (NAll output
        (NIff
          (NMember output image_set)
          (NEx input
            (NConj (NMember input source) predicate))))
  in
  NamedReplacementParts functional image (NImpl functional image).

Definition named_fixed_axioms : list named_axiom :=
  [ NFixedAxiom NEmptySet;
    NFixedAxiom NExtensionality;
    NFixedAxiom NPairing;
    NFixedAxiom NUnion;
    NFixedAxiom NPowerSet;
    NFixedAxiom NFoundation;
    NFixedAxiom NInfinity;
    NFixedAxiom NChoice
  ].

Definition named_default_all_intro_rule_step
  (state : named_state) : named_result named_state :=
  match named_goals state with
  | NOk (goal :: _) =>
      match named_conclusion goal with
      | NAll binder _ =>
          named_rule_step [] (NRAllIntro binder) state
      | _ => NError NWrongNamedShape
      end
  | NOk [] => NError (NCoreError NoGoals)
  | NError error => NError error
  end.

Definition named_fixed_axiom_rule_step
  (state : named_state) : named_result named_state :=
  named_rule_run named_fixed_axioms [NRAxiom] state.

Definition named_separation_axiom_rule_step
  (source element : string) (predicate : named_formula)
  (state : named_state) : named_result named_state :=
  let instance := named_separation_instance source element predicate in
  named_rule_run
    [NSeparationAxiom source element predicate]
    [NRAllElim source (NAll source instance); NRAxiom]
    state.

Definition current_hypothesis_names (state : named_state) : list string :=
  match named_goal_metadata state with
  | [] => []
  | metadata :: _ => metadata_hypothesis_names metadata
  end.

Definition replacement_internal_hypothesis
  (state : named_state) : string :=
  fresh_string "__replacement_functional"
    (current_hypothesis_names state).

Definition named_replacement_axiom_rule_step
  (source input output : string) (predicate : named_formula)
  (state : named_state) : named_result named_state :=
  let parts :=
    make_named_replacement_parts source input output predicate
  in
  let functional := named_replacement_functional parts in
  let image := named_replacement_image parts in
  let internal := replacement_internal_hypothesis state in
  named_rule_run
    [NReplacementAxiom input output predicate]
    [ NRImplIntro internal;
      NRAllElim source (NAll source image);
      NRImplElim functional;
      NRAxiom;
      NRHypothesis internal
    ]
    state.

Definition named_separation_tactic_step
  (fact source element : string) (predicate : named_formula)
  (state : named_state) : named_result named_state :=
  let instance := named_separation_instance source element predicate in
  named_rule_run
    [NSeparationAxiom source element predicate]
    [ NRCut fact instance;
      NRAllElim source (NAll source instance);
      NRAxiom
    ]
    state.

Definition named_replacement_tactic_step
  (fact source input output : string) (predicate : named_formula)
  (state : named_state) : named_result named_state :=
  let parts :=
    make_named_replacement_parts source input output predicate
  in
  let functional := named_replacement_functional parts in
  let image := named_replacement_image parts in
  let instance := named_replacement_instance parts in
  let internal := replacement_internal_hypothesis state in
  named_rule_run
    [NReplacementAxiom input output predicate]
    [ NRCut fact instance;
      NRImplIntro internal;
      NRAllElim source (NAll source image);
      NRImplElim functional;
      NRAxiom;
      NRHypothesis internal
    ]
    state.

Inductive named_rule_request : Type :=
| NPrimitiveRule (primitive : named_rule)
| NDefaultAllIntroRule
| NFixedAxiomRule
| NSeparationAxiomRule
    (source element : string) (predicate : named_formula)
| NReplacementAxiomRule
    (source input output : string) (predicate : named_formula).

Definition named_execute_rule
  (request : named_rule_request)
  (state : named_state) : named_result named_state :=
  match request with
  | NPrimitiveRule primitive =>
      named_rule_step [] primitive state
  | NDefaultAllIntroRule =>
      named_default_all_intro_rule_step state
  | NFixedAxiomRule =>
      named_fixed_axiom_rule_step state
  | NSeparationAxiomRule source element predicate =>
      named_separation_axiom_rule_step
        source element predicate state
  | NReplacementAxiomRule source input output predicate =>
      named_replacement_axiom_rule_step
        source input output predicate state
  end.

Corollary named_default_all_intro_rule_step_sound :
  forall state final,
    named_default_all_intro_rule_step state = NOk final ->
    named_state_provable zfc_theory final ->
    named_state_provable zfc_theory state.
Proof.
  intros state final Hstep Hfinal.
  unfold named_default_all_intro_rule_step in Hstep.
  destruct (named_goals state) as [views | error] eqn:Hgoals;
    try discriminate.
  destruct views as [|view rest]; try discriminate.
  destruct (named_conclusion view); try discriminate.
  eapply named_rule_step_sound.
  - apply named_axioms_are_zfc_sound.
  - exact Hstep.
  - exact Hfinal.
Qed.

Corollary named_fixed_axiom_rule_step_sound :
  forall state final,
    named_fixed_axiom_rule_step state = NOk final ->
    named_state_provable zfc_theory final ->
    named_state_provable zfc_theory state.
Proof.
  intros state final Hstep Hfinal.
  unfold named_fixed_axiom_rule_step in Hstep.
  eapply named_zfc_rule_run_sound; eauto.
Qed.

Corollary named_separation_axiom_rule_step_sound :
  forall source element predicate state final,
    named_separation_axiom_rule_step
      source element predicate state = NOk final ->
    named_state_provable zfc_theory final ->
    named_state_provable zfc_theory state.
Proof.
  intros source element predicate state final Hstep Hfinal.
  unfold named_separation_axiom_rule_step in Hstep.
  eapply named_zfc_rule_run_sound; eauto.
Qed.

Corollary named_replacement_axiom_rule_step_sound :
  forall source input output predicate state final,
    named_replacement_axiom_rule_step
      source input output predicate state = NOk final ->
    named_state_provable zfc_theory final ->
    named_state_provable zfc_theory state.
Proof.
  intros source input output predicate state final Hstep Hfinal.
  unfold named_replacement_axiom_rule_step in Hstep.
  eapply named_zfc_rule_run_sound; eauto.
Qed.

Theorem named_execute_rule_sound :
  forall request state final,
    named_execute_rule request state = NOk final ->
    named_state_provable zfc_theory final ->
    named_state_provable zfc_theory state.
Proof.
  intros request state final Hstep Hfinal.
  destruct request as
    [primitive
    |
    |
    |source element predicate
    |source input output predicate].
  - eapply named_rule_step_sound.
    + apply named_axioms_are_zfc_sound.
    + exact Hstep.
    + exact Hfinal.
  - eapply named_default_all_intro_rule_step_sound.
    + exact Hstep.
    + exact Hfinal.
  - eapply named_fixed_axiom_rule_step_sound.
    + exact Hstep.
    + exact Hfinal.
  - eapply named_separation_axiom_rule_step_sound.
    + exact Hstep.
    + exact Hfinal.
  - eapply named_replacement_axiom_rule_step_sound.
    + exact Hstep.
    + exact Hfinal.
Qed.

Corollary named_separation_tactic_step_sound :
  forall fact source element predicate state final,
    named_separation_tactic_step
      fact source element predicate state = NOk final ->
    named_state_provable zfc_theory final ->
    named_state_provable zfc_theory state.
Proof.
  intros fact source element predicate state final Hstep Hfinal.
  unfold named_separation_tactic_step in Hstep.
  eapply named_zfc_rule_run_sound; eauto.
Qed.

Corollary named_replacement_tactic_step_sound :
  forall fact source input output predicate state final,
    named_replacement_tactic_step
      fact source input output predicate state = NOk final ->
    named_state_provable zfc_theory final ->
    named_state_provable zfc_theory state.
Proof.
  intros fact source input output predicate state final Hstep Hfinal.
  unfold named_replacement_tactic_step in Hstep.
  eapply named_zfc_rule_run_sound; eauto.
Qed.
