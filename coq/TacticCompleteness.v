(** Primitive rules, their executable machine, and completeness.

    [rule] contains exactly the primitive natural-deduction rules.
    [tactic] is the user-facing language from [ProofState]; [TacRule r]
    makes every primitive rule directly available as a tactic.
 *)

From Coq Require Import List Bool PeanoNat.
From ZFCert Require Import FOL ProofState.
Import ListNotations.

Set Implicit Arguments.

Definition rule_step
  (is_axiom : formula -> bool)
  (primitive : rule)
  (state : proof_state) : outcome proof_state :=
  match state with
  | [] => Failure NoGoals
  | g :: rest =>
      match rule_step_focus is_axiom primitive g with
      | Success generated => Success (generated ++ rest)
      | Failure error => Failure error
      end
  end.

Fixpoint rule_run
  (is_axiom : formula -> bool)
  (rules : list rule)
  (state : proof_state) : outcome proof_state :=
  match rules with
  | [] => Success state
  | primitive :: rest =>
      match rule_step is_axiom primitive state with
      | Success next => rule_run is_axiom rest next
      | Failure error => Failure error
      end
  end.

Section Soundness.
  Variable T : theory.
  Variable is_axiom : formula -> bool.

  Hypothesis axiom_sound :
    forall A, is_axiom A = true -> T A.

  Theorem rule_step_sound :
    forall primitive state next,
      rule_step is_axiom primitive state = Success next ->
      state_provable T next ->
      state_provable T state.
  Proof.
    intros primitive [|g rest] next Hstep Hnext; simpl in Hstep.
    - discriminate.
    - destruct (rule_step_focus is_axiom primitive g)
        as [generated | error] eqn:Hfocus; try discriminate Hstep.
      inversion Hstep; subst next.
      apply Forall_app in Hnext.
      destruct Hnext as [Hgenerated Hrest].
      constructor.
      + eapply rule_step_focus_sound; eauto.
      + exact Hrest.
  Qed.

  Theorem rule_run_sound :
    forall rules state final,
      rule_run is_axiom rules state = Success final ->
      state_provable T final ->
      state_provable T state.
  Proof.
    induction rules as [|primitive rest IH];
      intros state final Hrun Hfinal; simpl in Hrun.
    - inversion Hrun. assumption.
    - destruct (rule_step is_axiom primitive state)
        as [next | error] eqn:Hstep; try discriminate Hrun.
      eapply rule_step_sound.
      + exact Hstep.
      + eapply IH; eauto.
  Qed.

  Corollary successful_rule_run_derives :
    forall rules Gamma C,
      rule_run is_axiom rules [Goal Gamma C] = Success [] ->
      derives T Gamma C.
  Proof.
    intros rules Gamma C Hrun.
    assert (Hinitial : state_provable T [Goal Gamma C]).
    { eapply rule_run_sound.
      - exact Hrun.
      - constructor. }
    inversion Hinitial. assumption.
  Qed.
End Soundness.

Section ListExecution.
  Variable is_axiom : formula -> bool.

  Lemma rule_step_suffix :
    forall primitive state next suffix,
      state <> [] ->
      rule_step is_axiom primitive state = Success next ->
      rule_step is_axiom primitive (state ++ suffix) =
        Success (next ++ suffix).
  Proof.
    intros primitive [|g rest] next suffix Hnonempty Hstep.
    - contradiction.
    - simpl in Hstep |- *.
      destruct (rule_step_focus is_axiom primitive g)
        as [generated | error] eqn:Hfocus; try discriminate Hstep.
      inversion Hstep; subst next.
      rewrite app_assoc.
      reflexivity.
  Qed.

  Lemma rule_run_suffix :
    forall rules state suffix,
      state <> [] ->
      rule_run is_axiom rules state = Success [] ->
      rule_run is_axiom rules (state ++ suffix) = Success suffix.
  Proof.
    induction rules as [|primitive rest IH];
      intros state suffix Hnonempty Hrun; simpl in Hrun.
    - inversion Hrun. contradiction.
    - destruct (rule_step is_axiom primitive state)
        as [next | error] eqn:Hstep; try discriminate Hrun.
      simpl.
      rewrite (@rule_step_suffix
        primitive state next suffix Hnonempty Hstep).
      destruct next as [|g goals].
      + destruct rest as [|next_rule rest'].
        * simpl. reflexivity.
        * simpl in Hrun. discriminate.
      + apply IH.
        * discriminate.
        * exact Hrun.
  Qed.

  Lemma rule_run_app :
    forall first second state,
      rule_run is_axiom (first ++ second) state =
      match rule_run is_axiom first state with
      | Success middle => rule_run is_axiom second middle
      | Failure error => Failure error
      end.
  Proof.
    induction first as [|primitive rest IH]; intros second state; simpl.
    - reflexivity.
    - destruct (rule_step is_axiom primitive state); simpl; auto.
  Qed.

  Lemma solve_two :
    forall first second g1 g2,
      rule_run is_axiom first [g1] = Success [] ->
      rule_run is_axiom second [g2] = Success [] ->
      rule_run is_axiom (first ++ second) [g1; g2] = Success [].
  Proof.
    intros first second g1 g2 Hfirst Hsecond.
    assert (Hfirst_suffix :
      rule_run is_axiom first [g1; g2] = Success [g2]).
    { change
        (rule_run is_axiom first ([g1] ++ [g2]) = Success [g2]).
      apply rule_run_suffix.
      - discriminate.
      - exact Hfirst. }
    rewrite rule_run_app.
    rewrite Hfirst_suffix.
    exact Hsecond.
  Qed.

  Lemma solve_three :
    forall first second third g1 g2 g3,
      rule_run is_axiom first [g1] = Success [] ->
      rule_run is_axiom second [g2] = Success [] ->
      rule_run is_axiom third [g3] = Success [] ->
      rule_run is_axiom (first ++ second ++ third) [g1; g2; g3] =
        Success [].
  Proof.
    intros first second third g1 g2 g3 Hfirst Hsecond Hthird.
    assert (Hfirst_suffix :
      rule_run is_axiom first [g1; g2; g3] = Success [g2; g3]).
    { change
        (rule_run is_axiom first ([g1] ++ [g2; g3]) =
          Success [g2; g3]).
      apply rule_run_suffix.
      - discriminate.
      - exact Hfirst. }
    rewrite rule_run_app.
    rewrite Hfirst_suffix.
    apply solve_two; assumption.
  Qed.
End ListExecution.

Lemma In_nth_error_exists :
  forall (A : formula) Gamma,
    In A Gamma -> exists n, nth_error Gamma n = Some A.
Proof.
  intros A Gamma Hin.
  induction Gamma as [|B rest IH].
  - contradiction.
  - destruct Hin as [<- | Hin].
    + exists 0. reflexivity.
    + destruct (IH Hin) as [n Hn].
      exists (S n). exact Hn.
Qed.

Section Completeness.
  Variable T : theory.
  Variable is_axiom : formula -> bool.

  Hypothesis axiom_complete :
    forall A, T A -> is_axiom A = true.

  Theorem derives_has_rule_list :
    forall Gamma C,
      derives T Gamma C ->
      exists rules,
        rule_run is_axiom rules [Goal Gamma C] = Success [].
  Proof.
    intros Gamma C Hderiv.
    induction Hderiv.
    - exists [RAxiom]. simpl.
      rewrite (axiom_complete H). reflexivity.
    - destruct (In_nth_error_exists A Gamma H) as [n Hnth].
      exists [RHypothesis n]. simpl.
      rewrite Hnth.
      unfold formula_eqb.
      destruct (formula_eq_dec A A); [reflexivity | contradiction].
    - destruct IHHderiv as [rules Hrules].
      exists (RFalsumElim :: rules). simpl. exact Hrules.
    - destruct IHHderiv as [rules Hrules].
      exists (RImplIntro :: rules). simpl. exact Hrules.
    - destruct IHHderiv1 as [first Hfirst].
      destruct IHHderiv2 as [second Hsecond].
      exists (RImplElim A :: first ++ second). simpl.
      apply solve_two; assumption.
    - destruct IHHderiv1 as [first Hfirst].
      destruct IHHderiv2 as [second Hsecond].
      exists (RConjIntro :: first ++ second). simpl.
      apply solve_two; assumption.
    - destruct IHHderiv as [rules Hrules].
      exists (RConjElimL B :: rules). simpl. exact Hrules.
    - destruct IHHderiv as [rules Hrules].
      exists (RConjElimR A :: rules). simpl. exact Hrules.
    - destruct IHHderiv as [rules Hrules].
      exists (RDisjIntroL :: rules). simpl. exact Hrules.
    - destruct IHHderiv as [rules Hrules].
      exists (RDisjIntroR :: rules). simpl. exact Hrules.
    - destruct IHHderiv1 as [first Hfirst].
      destruct IHHderiv2 as [second Hsecond].
      destruct IHHderiv3 as [third Hthird].
      exists (RDisjElim A B :: first ++ second ++ third). simpl.
      apply solve_three; assumption.
    - destruct IHHderiv as [rules Hrules].
      exists (RAllIntro :: rules). simpl. exact Hrules.
    - destruct IHHderiv as [rules Hrules].
      exists (RAllElim A t :: rules). simpl.
      rewrite (proj2 (formula_eqb_true_iff _ _) eq_refl).
      exact Hrules.
    - destruct IHHderiv as [rules Hrules].
      exists (RExIntro t :: rules). simpl. exact Hrules.
    - destruct IHHderiv1 as [first Hfirst].
      destruct IHHderiv2 as [second Hsecond].
      exists (RExElim A :: first ++ second). simpl.
      apply solve_two; assumption.
    - exists [REqualRefl]. simpl.
      rewrite Nat.eqb_refl. reflexivity.
    - destruct IHHderiv1 as [first Hfirst].
      destruct IHHderiv2 as [second Hsecond].
      exists (REqualElim P s t :: first ++ second). simpl.
      rewrite (proj2 (formula_eqb_true_iff _ _) eq_refl).
      apply solve_two; assumption.
    - destruct IHHderiv1 as [first Hfirst].
      destruct IHHderiv2 as [second Hsecond].
      exists (RCut A :: first ++ second). simpl.
      apply solve_two; assumption.
  Qed.
End Completeness.

Theorem derives_iff_rule_success :
  forall T is_axiom,
    (forall A, is_axiom A = true -> T A) ->
    (forall A, T A -> is_axiom A = true) ->
    forall Gamma C,
      derives T Gamma C <->
      exists rules,
        rule_run is_axiom rules [Goal Gamma C] = Success [].
Proof.
  intros T is_axiom Hsound Hcomplete Gamma C.
  split.
  - apply derives_has_rule_list. exact Hcomplete.
  - intros [rules Hrun].
    eapply successful_rule_run_derives; eauto.
Qed.

Lemma run_rule_list :
  forall is_axiom rules state,
    run is_axiom (map TacRule rules) state =
    rule_run is_axiom rules state.
Proof.
  intros is_axiom rules.
  induction rules as [|primitive rest IH]; intro state; simpl.
  - reflexivity.
  - destruct state as [|g goals]; simpl.
    + reflexivity.
    + destruct (rule_step_focus is_axiom primitive g); simpl.
      * apply IH.
      * reflexivity.
Qed.

Theorem derives_has_tactic_list :
  forall T is_axiom,
    (forall A, T A -> is_axiom A = true) ->
    forall Gamma C,
      derives T Gamma C ->
      exists commands,
        run is_axiom commands [Goal Gamma C] = Success [].
Proof.
  intros T is_axiom Hcomplete Gamma C Hderiv.
  destruct (@derives_has_rule_list T is_axiom Hcomplete Gamma C Hderiv)
    as [rules Hrules].
  exists (map TacRule rules).
  rewrite run_rule_list.
  exact Hrules.
Qed.

Theorem derives_iff_success :
  forall T is_axiom,
    (forall A, is_axiom A = true -> T A) ->
    (forall A, T A -> is_axiom A = true) ->
    forall Gamma C,
      derives T Gamma C <->
      exists commands,
        run is_axiom commands [Goal Gamma C] = Success [].
Proof.
  intros T is_axiom Hsound Hcomplete Gamma C.
  split.
  - apply derives_has_tactic_list. exact Hcomplete.
  - intros [commands Hrun].
    eapply successful_run_derives; eauto.
Qed.
