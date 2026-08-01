(** Replayable proof certificates and an extraction-ready certified session.

    The OCaml layer may plan any sequence of named primitive rules. It cannot
    mutate a proof state directly: this module checks every primitive rule,
    records exactly the accepted sequence, and replays that sequence from the
    original theorem before accepting [qed].
 *)

From Coq Require Import List String Bool.
From ZFCert Require Import
  FOL ProofState NamedProofState NamedCommands ZFC.
Import ListNotations.
Open Scope string_scope.

Record certificate_step : Type := CertificateStep {
  certificate_axioms : list named_axiom;
  certificate_rule : named_rule
}.

Definition certificate : Type := list certificate_step.

Definition run_certificate_step
  (step : certificate_step)
  (state : named_state) : named_result named_state :=
  named_rule_step
    (certificate_axioms step)
    (certificate_rule step)
    state.

Fixpoint replay_steps
  (steps : certificate)
  (state : named_state) : named_result named_state :=
  match steps with
  | [] => NOk state
  | step :: rest =>
      named_bind (run_certificate_step step state)
        (fun next => replay_steps rest next)
  end.

Record certified_state : Type := CertifiedState {
  certified_initial_formula : named_formula;
  certified_constants : list string;
  certified_current_state : named_state;
  certified_reverse_certificate : certificate
}.

Definition certified_start_with_constants
  (constants : list string) (source : named_formula)
  : named_result certified_state :=
  named_bind (named_start_with_constants constants source) (fun state =>
  NOk (CertifiedState source constants state [])).

Definition certified_start
  (source : named_formula) : named_result certified_state :=
  certified_start_with_constants [] source.

Definition certified_goals
  (state : certified_state) : named_result (list named_goal) :=
  named_goals (certified_current_state state).

Definition certified_solved (state : certified_state) : bool :=
  named_solved (certified_current_state state).

Definition certified_certificate (state : certified_state) : certificate :=
  rev (certified_reverse_certificate state).

Definition certified_step
  (step : certificate_step)
  (state : certified_state) : named_result certified_state :=
  named_bind
    (run_certificate_step step (certified_current_state state))
    (fun next =>
  NOk (CertifiedState
    (certified_initial_formula state)
    (certified_constants state)
    next
    (step :: certified_reverse_certificate state))).

Fixpoint certified_run
  (steps : certificate)
  (state : certified_state) : named_result certified_state :=
  match steps with
  | [] => NOk state
  | step :: rest =>
      named_bind (certified_step step state)
        (fun next => certified_run rest next)
  end.

Definition replay_certificate_with_constants
  (constants : list string) (source : named_formula)
  (steps : certificate) : named_result named_state :=
  named_bind (named_start_with_constants constants source) (fun state =>
  replay_steps steps state).

Definition replay_certificate
  (source : named_formula)
  (steps : certificate) : named_result named_state :=
  replay_certificate_with_constants [] source steps.

(** [certified_finalize] deliberately ignores the cached current proof state.
    It starts again from the theorem statement and accepts only when replaying
    the recorded primitive rules closes every goal. *)
Definition certified_finalize
  (state : certified_state) : named_result certificate :=
  let steps := certified_certificate state in
  named_bind
    (replay_certificate_with_constants
      (certified_constants state)
      (certified_initial_formula state) steps)
    (fun replayed =>
  if named_solved replayed
  then NOk steps
  else NError NWrongNamedShape).

Definition one_step
  (axioms : list named_axiom) (primitive : named_rule)
  : certificate_step :=
  CertificateStep axioms primitive.

Definition named_rule_request_program
  (request : named_rule_request)
  (state : named_state) : named_result certificate :=
  match request with
  | NPrimitiveRule primitive =>
      NOk [one_step [] primitive]
  | NDefaultAllIntroRule =>
      match named_goals state with
      | NOk (goal :: _) =>
          match named_conclusion goal with
          | NAll binder _ =>
              NOk [one_step [] (NRAllIntro binder)]
          | _ => NError NWrongNamedShape
          end
      | NOk [] => NError (NCoreError NoGoals)
      | NError error => NError error
      end
  | NFixedAxiomRule =>
      NOk [one_step named_fixed_axioms NRAxiom]
  | NSeparationAxiomRule source element predicate =>
      let instance :=
        named_separation_instance source element predicate
      in
      let capability :=
        NSeparationAxiom source element predicate
      in
      NOk
        [ one_step [] (NRAllElim source (NAll source instance));
          one_step [capability] NRAxiom
        ]
  | NReplacementAxiomRule source input output predicate =>
      let parts :=
        make_named_replacement_parts source input output predicate
      in
      let functional := named_replacement_functional parts in
      let image := named_replacement_image parts in
      let internal := replacement_internal_hypothesis state in
      let capability :=
        NReplacementAxiom input output predicate
      in
      NOk
        [ one_step [] (NRImplIntro internal);
          one_step [] (NRAllElim source (NAll source image));
          one_step [] (NRImplElim functional);
          one_step [capability] NRAxiom;
          one_step [] (NRHypothesis internal)
        ]
  end.

Definition certified_execute_rule
  (request : named_rule_request)
  (state : certified_state) : named_result certified_state :=
  named_bind
    (named_rule_request_program
      request (certified_current_state state))
    (fun steps => certified_run steps state).

Definition separation_tactic_program
  (fact source element : string) (predicate : named_formula)
  : certificate :=
  let instance := named_separation_instance source element predicate in
  let capability := NSeparationAxiom source element predicate in
  [ one_step [] (NRCut fact instance);
    one_step [] (NRAllElim source (NAll source instance));
    one_step [capability] NRAxiom
  ].

Definition certified_separation_tactic
  (fact source element : string) (predicate : named_formula)
  (state : certified_state) : named_result certified_state :=
  certified_run
    (separation_tactic_program fact source element predicate)
    state.

Definition replacement_tactic_program
  (fact source input output : string) (predicate : named_formula)
  (state : named_state) : certificate :=
  let parts :=
    make_named_replacement_parts source input output predicate
  in
  let functional := named_replacement_functional parts in
  let image := named_replacement_image parts in
  let instance := named_replacement_instance parts in
  let internal := replacement_internal_hypothesis state in
  let capability := NReplacementAxiom input output predicate in
  [ one_step [] (NRCut fact instance);
    one_step [] (NRImplIntro internal);
    one_step [] (NRAllElim source (NAll source image));
    one_step [] (NRImplElim functional);
    one_step [capability] NRAxiom;
    one_step [] (NRHypothesis internal)
  ].

Definition certified_replacement_tactic
  (fact source input output : string) (predicate : named_formula)
  (state : certified_state) : named_result certified_state :=
  certified_run
    (replacement_tactic_program
      fact source input output predicate
      (certified_current_state state))
    state.

(** Soundness of the computational certificate checker. *)

Theorem replay_steps_sound :
  forall steps state final,
    replay_steps steps state = NOk final ->
    named_state_provable zfc_theory final ->
    named_state_provable zfc_theory state.
Proof.
  induction steps as [|step rest IH];
    intros state final Hrun Hfinal; cbn in Hrun.
  - inversion Hrun. exact Hfinal.
  - destruct (run_certificate_step step state)
      as [next | error] eqn:Hstep; try discriminate.
    eapply named_rule_step_sound.
    + apply named_axioms_are_zfc_sound.
    + exact Hstep.
    + eapply IH; eauto.
Qed.

Theorem certified_step_sound :
  forall step state next,
    certified_step step state = NOk next ->
    named_state_provable zfc_theory
      (certified_current_state next) ->
    named_state_provable zfc_theory
      (certified_current_state state).
Proof.
  intros step state next Hstep Hnext.
  unfold certified_step in Hstep.
  destruct
    (run_certificate_step step (certified_current_state state))
    as [current | error] eqn:Hcurrent; try discriminate.
  inversion Hstep; subst.
  eapply named_rule_step_sound.
  - apply named_axioms_are_zfc_sound.
  - exact Hcurrent.
  - exact Hnext.
Qed.

Theorem certified_run_sound :
  forall steps state final,
    certified_run steps state = NOk final ->
    named_state_provable zfc_theory
      (certified_current_state final) ->
    named_state_provable zfc_theory
      (certified_current_state state).
Proof.
  induction steps as [|step rest IH];
    intros state final Hrun Hfinal; cbn in Hrun.
  - inversion Hrun. exact Hfinal.
  - destruct (certified_step step state)
      as [next | error] eqn:Hstep; try discriminate.
    eapply certified_step_sound.
    + exact Hstep.
    + eapply IH; eauto.
Qed.

Lemma named_solved_provable :
  forall state,
    named_solved state = true ->
    named_state_provable zfc_theory state.
Proof.
  intros [kernel metadata] Hsolved.
  destruct kernel as [|goal rest].
  - constructor.
  - discriminate.
Qed.

Definition named_formula_provable_with_constants
  (constants : list string) (source : named_formula) : Prop :=
  exists core,
    elaborate_closed constants source = NOk core /\
    derives zfc_theory [] core.

Definition named_formula_provable (source : named_formula) : Prop :=
  named_formula_provable_with_constants [] source.

Lemma named_start_with_constants_provable :
  forall constants source state,
    named_start_with_constants constants source = NOk state ->
    named_state_provable zfc_theory state ->
    named_formula_provable_with_constants constants source.
Proof.
  intros constants source state Hstart Hstate.
  unfold named_start_with_constants in Hstart.
  destruct (elaborate_closed constants source)
    as [core | error] eqn:Helaborate; try discriminate.
  inversion Hstart; subst.
  exists core. split.
  - exact Helaborate.
  - unfold named_state_provable, state_provable in Hstate.
    inversion Hstate; subst. exact H1.
Qed.

Lemma named_start_provable :
  forall source state,
    named_start source = NOk state ->
    named_state_provable zfc_theory state ->
    named_formula_provable source.
Proof.
  intros source state Hstart Hstate.
  unfold named_start, named_formula_provable in *.
  eapply named_start_with_constants_provable; eauto.
Qed.

Theorem replay_certificate_with_constants_sound :
  forall constants source steps final,
    replay_certificate_with_constants constants source steps = NOk final ->
    named_solved final = true ->
    named_formula_provable_with_constants constants source.
Proof.
  intros constants source steps final Hreplay Hsolved.
  unfold replay_certificate_with_constants in Hreplay.
  destruct (named_start_with_constants constants source)
    as [initial | error] eqn:Hstart; try discriminate.
  eapply named_start_with_constants_provable.
  - exact Hstart.
  - eapply replay_steps_sound.
    + exact Hreplay.
    + apply named_solved_provable. exact Hsolved.
Qed.

Theorem replay_certificate_sound :
  forall source steps final,
    replay_certificate source steps = NOk final ->
    named_solved final = true ->
    named_formula_provable source.
Proof.
  intros source steps final Hreplay Hsolved.
  unfold replay_certificate, named_formula_provable in *.
  eapply replay_certificate_with_constants_sound; eauto.
Qed.

Theorem certified_finalize_sound :
  forall state steps,
    certified_finalize state = NOk steps ->
    named_formula_provable_with_constants
      (certified_constants state)
      (certified_initial_formula state).
Proof.
  intros state steps Hfinalize.
  unfold certified_finalize in Hfinalize.
  destruct
    (replay_certificate_with_constants
      (certified_constants state)
      (certified_initial_formula state)
      (certified_certificate state))
    as [replayed | error] eqn:Hreplay.
  - destruct replayed as [kernel metadata].
    destruct kernel as [|goal rest].
    + cbn in Hfinalize. inversion Hfinalize; subst.
      eapply replay_certificate_with_constants_sound
        with (constants := certified_constants state)
             (steps := certified_certificate state)
             (final := NamedState [] metadata).
      * exact Hreplay.
      * reflexivity.
    + cbn in Hfinalize. discriminate.
  - cbn in Hfinalize. discriminate.
Qed.
