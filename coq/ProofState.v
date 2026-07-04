(** Extraction-ready proof states and tactic execution.

    The computational function [step] is independent of [Prop].  Its
    correctness theorem connects every successful transition back to the
    natural-deduction relation [derives] from [FOL].
 *)

From Coq Require Import List Bool PeanoNat.
From ZFCert Require Import FOL.
Import ListNotations.

Set Implicit Arguments.

Record goal : Type := Goal {
  assumptions : list formula;
  conclusion : formula
}.

Definition proof_state : Type := list goal.

Definition start (C : formula) : proof_state :=
  [Goal [] C].

Definition state_goals (state : proof_state) : list goal :=
  state.

Inductive rule : Type :=
| RAxiom
| RHypothesis (hypothesis : nat)
| RFalsumElim
| RImplIntro
| RImplElim (premise : formula)
| RConjIntro
| RConjElimL (right : formula)
| RConjElimR (left : formula)
| RDisjIntroL
| RDisjIntroR
| RDisjElim (left right : formula)
| RAllIntro
| RAllElim (body : formula) (term : nat)
| RExIntro (term : nat)
| RExElim (body : formula)
| REqualRefl
| REqualElim (predicate : formula) (left right : nat)
| RCut (lemma : formula).

Inductive tactic : Type :=
| TacRule (primitive : rule)
| TacIntro
| TacExact (hypothesis : nat)
| TacApply (hypothesis : nat)
| TacSpecialize (hypothesis term : nat)
| TacSplit
| TacLeft
| TacRight
| TacUse (term : nat)
| TacRefl
| TacContradiction
| TacCases (hypothesis : nat).

Inductive step_error : Type :=
| NoGoals
| HypothesisNotFound
| FormulaMismatch
| WrongGoalShape.

Inductive outcome (A : Type) : Type :=
| Success : A -> outcome A
| Failure : step_error -> outcome A.

Arguments Success {A} _.
Arguments Failure {A} _.

Definition rule_step_focus
  (is_axiom : formula -> bool)
  (primitive : rule)
  (g : goal) : outcome (list goal) :=
  let Gamma := assumptions g in
  let C := conclusion g in
  match primitive with
  | RAxiom =>
      if is_axiom C then Success [] else Failure FormulaMismatch
  | RHypothesis n =>
      match nth_error Gamma n with
      | Some A =>
          if formula_eqb A C then Success []
          else Failure FormulaMismatch
      | None => Failure HypothesisNotFound
      end
  | RFalsumElim =>
      Success [Goal Gamma Falsum]
  | RImplIntro =>
      match C with
      | Impl A B => Success [Goal (A :: Gamma) B]
      | _ => Failure WrongGoalShape
      end
  | RImplElim A =>
      Success [Goal Gamma (Impl A C); Goal Gamma A]
  | RConjIntro =>
      match C with
      | Conj A B => Success [Goal Gamma A; Goal Gamma B]
      | _ => Failure WrongGoalShape
      end
  | RConjElimL B =>
      Success [Goal Gamma (Conj C B)]
  | RConjElimR A =>
      Success [Goal Gamma (Conj A C)]
  | RDisjIntroL =>
      match C with
      | Disj A _ => Success [Goal Gamma A]
      | _ => Failure WrongGoalShape
      end
  | RDisjIntroR =>
      match C with
      | Disj _ B => Success [Goal Gamma B]
      | _ => Failure WrongGoalShape
      end
  | RDisjElim A B =>
      Success
        [ Goal Gamma (Disj A B);
          Goal (A :: Gamma) C;
          Goal (B :: Gamma) C ]
  | RAllIntro =>
      match C with
      | All A => Success [Goal (map lift Gamma) A]
      | _ => Failure WrongGoalShape
      end
  | RAllElim A t =>
      if formula_eqb (instantiate t A) C
      then Success [Goal Gamma (All A)]
      else Failure FormulaMismatch
  | RExIntro t =>
      match C with
      | Ex A => Success [Goal Gamma (instantiate t A)]
      | _ => Failure WrongGoalShape
      end
  | RExElim A =>
      Success
        [ Goal Gamma (Ex A);
          Goal (A :: map lift Gamma) (lift C) ]
  | REqualRefl =>
      match C with
      | Equal s t =>
          if Nat.eqb s t then Success []
          else Failure FormulaMismatch
      | _ => Failure WrongGoalShape
      end
  | REqualElim P s t =>
      if formula_eqb (instantiate t P) C
      then Success
        [ Goal Gamma (Equal s t);
          Goal Gamma (instantiate s P) ]
      else Failure FormulaMismatch
  | RCut A =>
      Success
        [ Goal Gamma A;
          Goal (A :: Gamma) C ]
  end.

Fixpoint contains_formula (A : formula) (Gamma : list formula) : bool :=
  match Gamma with
  | [] => false
  | B :: rest => formula_eqb A B || contains_formula A rest
  end.

Fixpoint contradictory (Gamma : list formula) : bool :=
  match Gamma with
  | [] => false
  | A :: rest =>
      contains_formula (Neg A) Gamma ||
      match A with
      | Impl P Falsum =>
          contains_formula P Gamma || contradictory rest
      | _ => contradictory rest
      end
  end.

Definition step_focus
  (is_axiom : formula -> bool)
  (command : tactic) (g : goal)
  : outcome (list goal) :=
  let Gamma := assumptions g in
  let C := conclusion g in
  match command with
  | TacRule primitive => rule_step_focus is_axiom primitive g
  | TacIntro =>
      match C with
      | Impl A B => Success [Goal (A :: Gamma) B]
      | All A => Success [Goal (map lift Gamma) A]
      | _ => Failure WrongGoalShape
      end
  | TacExact n =>
      match nth_error Gamma n with
      | Some A =>
          if formula_eqb A C then Success []
          else Failure FormulaMismatch
      | None => Failure HypothesisNotFound
      end
  | TacApply n =>
      match nth_error Gamma n with
      | Some (Impl A B) =>
          if formula_eqb B C then Success [Goal Gamma A]
          else Failure FormulaMismatch
      | Some _ => Failure WrongGoalShape
      | None => Failure HypothesisNotFound
      end
  | TacSpecialize n t =>
      match nth_error Gamma n with
      | Some (All A) =>
          Success [Goal (instantiate t A :: Gamma) C]
      | Some _ => Failure WrongGoalShape
      | None => Failure HypothesisNotFound
      end
  | TacSplit =>
      match C with
      | Conj A B => Success [Goal Gamma A; Goal Gamma B]
      | _ => Failure WrongGoalShape
      end
  | TacLeft =>
      match C with
      | Disj A _ => Success [Goal Gamma A]
      | _ => Failure WrongGoalShape
      end
  | TacRight =>
      match C with
      | Disj _ B => Success [Goal Gamma B]
      | _ => Failure WrongGoalShape
      end
  | TacUse t =>
      match C with
      | Ex A => Success [Goal Gamma (instantiate t A)]
      | _ => Failure WrongGoalShape
      end
  | TacRefl =>
      match C with
      | Equal s t =>
          if Nat.eqb s t then Success []
          else Failure FormulaMismatch
      | _ => Failure WrongGoalShape
      end
  | TacContradiction =>
      if contradictory Gamma then Success []
      else Failure FormulaMismatch
  | TacCases n =>
      match nth_error Gamma n with
      | Some (Conj A B) =>
          Success [Goal (B :: A :: Gamma) C]
      | Some (Ex A) =>
          Success [Goal (A :: map lift Gamma) (lift C)]
      | Some _ => Failure WrongGoalShape
      | None => Failure HypothesisNotFound
      end
  end.

(** [step] focuses the first goal and leaves all other goals untouched. *)
Definition step
  (is_axiom : formula -> bool)
  (command : tactic) (state : proof_state)
  : outcome proof_state :=
  match state with
  | [] => Failure NoGoals
  | g :: rest =>
      match step_focus is_axiom command g with
      | Success generated => Success (generated ++ rest)
      | Failure error => Failure error
      end
  end.

Fixpoint run
  (is_axiom : formula -> bool)
  (commands : list tactic) (state : proof_state)
  : outcome proof_state :=
  match commands with
  | [] => Success state
  | command :: rest =>
      match step is_axiom command state with
      | Success next => run is_axiom rest next
      | Failure error => Failure error
      end
  end.

Section Correctness.
  Variable T : theory.
  Variable is_axiom : formula -> bool.

  Hypothesis axiom_sound :
    forall A, is_axiom A = true -> T A.

  Definition goal_provable (g : goal) : Prop :=
    derives T (assumptions g) (conclusion g).

  Definition state_provable (state : proof_state) : Prop :=
    Forall goal_provable state.

  Definition refines (next previous : proof_state) : Prop :=
    state_provable next -> state_provable previous.

  Lemma contains_formula_correct :
    forall A Gamma,
      contains_formula A Gamma = true <-> In A Gamma.
  Proof.
    intros A Gamma.
    induction Gamma as [|B rest IH]; simpl.
    - split; intro H; [discriminate | contradiction].
    - rewrite Bool.orb_true_iff, formula_eqb_true_iff, IH.
      split.
      + intros [HAB | Hin].
        * left. symmetry. exact HAB.
        * right. exact Hin.
      + intros [HBA | Hin].
        * left. symmetry. exact HBA.
        * right. exact Hin.
  Qed.

  Lemma contradictory_correct :
    forall Gamma,
      contradictory Gamma = true ->
      exists A, In A Gamma /\ In (Neg A) Gamma.
  Proof.
    induction Gamma as [|A rest IH]; simpl.
    - discriminate.
    - rewrite Bool.orb_true_iff.
      intros [Hneg | Hremaining].
      + exists A. split.
        * left. reflexivity.
        * apply (proj1 (contains_formula_correct (Neg A) (A :: rest))).
          exact Hneg.
      + destruct A as [|x y|x y|A1 A2|A1 A2|A1 A2|A1|A1]; try (
          destruct (IH Hremaining) as [B [HB HnotB]];
          exists B; split; right; assumption).
        destruct A2; try (
          destruct (IH Hremaining) as [B [HB HnotB]];
          exists B; split; right; assumption).
        rewrite Bool.orb_true_iff in Hremaining.
        destruct Hremaining as [HP | Hrest].
        * exists A1. split.
          -- apply (proj1
               (contains_formula_correct A1 (Impl A1 Falsum :: rest))).
             exact HP.
          -- left. reflexivity.
        * destruct (IH Hrest) as [B [HB HnotB]].
          exists B. split; right; assumption.
  Qed.

  Lemma nth_error_derivable :
    forall Gamma n A,
      nth_error Gamma n = Some A ->
      derives T Gamma A.
  Proof.
    intros Gamma n A Hnth.
    apply D_hyp.
    eapply nth_error_In.
    exact Hnth.
  Qed.

  Theorem rule_step_focus_sound :
    forall primitive g generated,
      rule_step_focus is_axiom primitive g = Success generated ->
      Forall goal_provable generated ->
      goal_provable g.
  Proof.
    intros primitive [Gamma C] generated Hstep Hgenerated.
    destruct primitive; simpl in Hstep.
    - destruct (is_axiom C) eqn:HA; try discriminate Hstep.
      inversion Hstep; subst. apply D_axiom. apply axiom_sound. exact HA.
    - destruct (nth_error Gamma hypothesis) as [A |] eqn:Hnth;
        try discriminate Hstep.
      destruct (formula_eqb A C) eqn:Heq; try discriminate Hstep.
      inversion Hstep; subst.
      apply formula_eqb_true_iff in Heq. subst A.
      eapply nth_error_derivable. exact Hnth.
    - inversion Hstep; subst. inversion Hgenerated; subst.
      apply D_falsum_elim. assumption.
    - destruct C; try discriminate Hstep.
      inversion Hstep; subst. inversion Hgenerated; subst.
      apply D_impl_intro. assumption.
    - inversion Hstep; subst.
      inversion Hgenerated as [|g1 tail Hg1 Htail]; subst.
      inversion Htail as [|g2 tail' Hg2 Hempty]; subst.
      inversion Hempty.
      eapply D_impl_elim; eauto.
    - destruct C; try discriminate Hstep.
      inversion Hstep; subst.
      inversion Hgenerated as [|g1 tail Hg1 Htail]; subst.
      inversion Htail as [|g2 tail' Hg2 Hempty]; subst.
      inversion Hempty.
      apply D_conj_intro; assumption.
    - inversion Hstep; subst. inversion Hgenerated; subst.
      eapply D_conj_elim_l. eauto.
    - inversion Hstep; subst. inversion Hgenerated; subst.
      eapply D_conj_elim_r. eauto.
    - destruct C; try discriminate Hstep.
      inversion Hstep; subst. inversion Hgenerated; subst.
      apply D_disj_intro_l. assumption.
    - destruct C; try discriminate Hstep.
      inversion Hstep; subst. inversion Hgenerated; subst.
      apply D_disj_intro_r. assumption.
    - inversion Hstep; subst.
      inversion Hgenerated as [|g1 tail Hg1 Htail]; subst.
      inversion Htail as [|g2 tail2 Hg2 Htail2]; subst.
      inversion Htail2 as [|g3 tail3 Hg3 Hempty]; subst.
      inversion Hempty.
      eapply D_disj_elim; eauto.
    - destruct C; try discriminate Hstep.
      inversion Hstep; subst. inversion Hgenerated; subst.
      apply D_all_intro. assumption.
    - destruct (formula_eqb (instantiate term body) C) eqn:Heq;
        try discriminate Hstep.
      inversion Hstep; subst. inversion Hgenerated; subst.
      apply formula_eqb_true_iff in Heq. subst C.
      apply D_all_elim. assumption.
    - destruct C; try discriminate Hstep.
      inversion Hstep; subst. inversion Hgenerated; subst.
      apply D_ex_intro with (t := term). assumption.
    - inversion Hstep; subst.
      inversion Hgenerated as [|g1 tail Hg1 Htail]; subst.
      inversion Htail as [|g2 tail' Hg2 Hempty]; subst.
      inversion Hempty.
      eapply D_ex_elim; eauto.
    - destruct C; try discriminate Hstep.
      destruct (Nat.eqb n n0) eqn:Heq; try discriminate Hstep.
      inversion Hstep; subst.
      apply Nat.eqb_eq in Heq. subst n0.
      apply D_equal_refl.
    - destruct (formula_eqb (instantiate right predicate) C) eqn:Heq;
        try discriminate Hstep.
      inversion Hstep; subst.
      apply formula_eqb_true_iff in Heq. subst C.
      inversion Hgenerated as [|g1 tail Hg1 Htail]; subst.
      inversion Htail as [|g2 tail' Hg2 Hempty]; subst.
      inversion Hempty.
      eapply D_equal_elim; eauto.
    - inversion Hstep; subst.
      inversion Hgenerated as [|g1 tail Hg1 Htail]; subst.
      inversion Htail as [|g2 tail' Hg2 Hempty]; subst.
      inversion Hempty.
      eapply D_cut; eauto.
  Qed.

  Theorem step_focus_sound :
    forall command g generated,
      step_focus is_axiom command g = Success generated ->
      Forall goal_provable generated ->
      goal_provable g.
  Proof.
    intros command [Gamma C] generated Hstep Hgenerated.
    destruct command; simpl in Hstep.
    - eapply rule_step_focus_sound; eauto.
    - destruct C; try discriminate Hstep.
      + inversion Hstep; subst. inversion Hgenerated; subst.
        apply D_impl_intro. assumption.
      + inversion Hstep; subst. inversion Hgenerated; subst.
        apply D_all_intro. assumption.
    - destruct (nth_error Gamma hypothesis) as [A |] eqn:Hnth;
        try discriminate Hstep.
      destruct (formula_eqb A C) eqn:Heq; try discriminate Hstep.
      inversion Hstep; subst.
      apply formula_eqb_true_iff in Heq. subst A.
      eapply nth_error_derivable. exact Hnth.
    - destruct (nth_error Gamma hypothesis) as [H |] eqn:Hnth;
        try discriminate Hstep.
      destruct H as [|x y|x y|P Q|P Q|P Q|P|P];
        try discriminate Hstep.
      destruct (formula_eqb Q C) eqn:Heq; try discriminate Hstep.
      inversion Hstep; subst. inversion Hgenerated; subst.
      apply formula_eqb_true_iff in Heq. subst Q.
      eapply D_impl_elim.
      + eapply nth_error_derivable. exact Hnth.
      + assumption.
    - destruct (nth_error Gamma hypothesis) as [H |] eqn:Hnth;
        try discriminate Hstep.
      destruct H as [|x y|x y|P Q|P Q|P Q|P|P];
        try discriminate Hstep.
      inversion Hstep; subst. inversion Hgenerated; subst.
      eapply D_cut.
      + apply D_all_elim with (t := term).
        eapply nth_error_derivable. exact Hnth.
      + assumption.
    - destruct C; try discriminate Hstep.
      inversion Hstep; subst.
      inversion Hgenerated as [|g1 tail Hg1 Htail]; subst.
      inversion Htail as [|g2 tail' Hg2 Hempty]; subst.
      inversion Hempty.
      apply D_conj_intro; assumption.
    - destruct C; try discriminate Hstep.
      inversion Hstep; subst. inversion Hgenerated; subst.
      apply D_disj_intro_l. assumption.
    - destruct C; try discriminate Hstep.
      inversion Hstep; subst. inversion Hgenerated; subst.
      apply D_disj_intro_r. assumption.
    - destruct C; try discriminate Hstep.
      inversion Hstep; subst. inversion Hgenerated; subst.
      apply D_ex_intro with (t := term). assumption.
    - destruct C; try discriminate Hstep.
      destruct (Nat.eqb n n0) eqn:Heq; try discriminate Hstep.
      inversion Hstep; subst.
      apply Nat.eqb_eq in Heq. subst n0.
      apply D_equal_refl.
    - destruct (contradictory Gamma) eqn:Hcontra; try discriminate Hstep.
      inversion Hstep; subst.
      destruct (contradictory_correct Gamma Hcontra)
        as [A [HA HnotA]].
      apply D_falsum_elim.
      eapply D_impl_elim.
      + apply D_hyp. exact HnotA.
      + apply D_hyp. exact HA.
    - destruct (nth_error Gamma hypothesis) as [H |] eqn:Hnth;
        try discriminate Hstep.
      destruct H as [|x y|x y|P Q|P Q|P Q|P|P];
        try discriminate Hstep.
      + inversion Hstep; subst. inversion Hgenerated; subst.
        eapply D_cut with (A := P).
        * eapply D_conj_elim_l.
          eapply nth_error_derivable. exact Hnth.
        * eapply D_cut with (A := Q).
          -- eapply D_conj_elim_r.
             eapply derives_weakening.
             ++ eapply nth_error_derivable. exact Hnth.
             ++ intros X HX. right. exact HX.
          -- assumption.
      + inversion Hstep; subst. inversion Hgenerated; subst.
        eapply D_ex_elim.
        * eapply nth_error_derivable. exact Hnth.
        * assumption.
  Qed.

  Theorem step_sound :
    forall command state next,
      step is_axiom command state = Success next ->
      state_provable next ->
      state_provable state.
  Proof.
    intros command [|g rest] next Hstep Hnext; simpl in Hstep.
    - discriminate.
    - destruct (step_focus is_axiom command g)
        as [generated | error] eqn:Hfocus;
        try discriminate Hstep.
      inversion Hstep; subst next.
      apply Forall_app in Hnext.
      destruct Hnext as [Hgenerated Hrest].
      constructor.
      + eapply step_focus_sound; eauto.
      + exact Hrest.
  Qed.

  Corollary step_refines :
    forall command state next,
      step is_axiom command state = Success next ->
      refines next state.
  Proof.
    intros command state next Hstep.
    unfold refines.
    eapply step_sound.
    exact Hstep.
  Qed.

  Theorem run_sound :
    forall commands state final,
      run is_axiom commands state = Success final ->
      state_provable final ->
      state_provable state.
  Proof.
    induction commands as [|command rest IH];
      intros state final Hrun Hfinal; simpl in Hrun.
    - inversion Hrun. assumption.
    - destruct (step is_axiom command state) as [next | error] eqn:Hstep;
        try discriminate Hrun.
      eapply step_sound.
      + exact Hstep.
      + eapply IH; eauto.
  Qed.

  Corollary successful_run_derives :
    forall commands Gamma C,
      run is_axiom commands [Goal Gamma C] = Success [] ->
      derives T Gamma C.
  Proof.
    intros commands Gamma C Hrun.
    assert (Hinitial :
      state_provable [Goal Gamma C]).
    { eapply run_sound.
      - exact Hrun.
      - constructor. }
    inversion Hinitial.
    assumption.
  Qed.

  Theorem intro_imp_reversible :
    forall Gamma A B,
      goal_provable (Goal Gamma (Impl A B)) <->
      goal_provable (Goal (A :: Gamma) B).
  Proof.
    intros Gamma A B. split.
    - intros H.
      eapply D_impl_elim.
      + eapply derives_weakening.
        * exact H.
        * intros X HX. right. exact HX.
      + apply D_hyp. left. reflexivity.
    - apply D_impl_intro.
  Qed.

  Theorem split_reversible :
    forall Gamma A B,
      goal_provable (Goal Gamma (Conj A B)) <->
      goal_provable (Goal Gamma A) /\ goal_provable (Goal Gamma B).
  Proof.
    intros Gamma A B. split.
    - intro H. split.
      + eapply D_conj_elim_l. exact H.
      + eapply D_conj_elim_r. exact H.
    - intros [HA HB]. apply D_conj_intro; assumption.
  Qed.
End Correctness.

(** Small executable examples; all are proved by computation. *)
Example step_intro_example :
  step (fun _ => false) TacIntro
    [Goal [] (Impl (Equal 0 0) (Equal 0 0))]
  =
  Success [Goal [Equal 0 0] (Equal 0 0)].
Proof. reflexivity. Qed.

Example run_identity_example :
  run (fun _ => false) [TacIntro; TacExact 0]
    [Goal [] (Impl (Equal 0 0) (Equal 0 0))]
  =
  Success [].
Proof. reflexivity. Qed.
