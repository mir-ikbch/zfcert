(** First-order logic for the language of set theory.

    Terms are variables represented by de Bruijn indices.  ZFC has no
    function symbols, so this is the complete term language that we need.
    Equality is interpreted as Coq equality; [member] is supplied by a model.
 *)

From Coq Require Import List PeanoNat.
Import ListNotations.

Set Implicit Arguments.

Inductive formula : Type :=
| Falsum : formula
| Equal : nat -> nat -> formula
| Member : nat -> nat -> formula
| Conj : formula -> formula -> formula
| Disj : formula -> formula -> formula
| Impl : formula -> formula -> formula
| All : formula -> formula
| Ex : formula -> formula.

Definition formula_eq_dec :
  forall A B : formula, {A = B} + {A <> B}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Definition formula_eqb (A B : formula) : bool :=
  if formula_eq_dec A B then true else false.

Lemma formula_eqb_true_iff :
  forall A B, formula_eqb A B = true <-> A = B.
Proof.
  intros A B.
  unfold formula_eqb.
  destruct (formula_eq_dec A B); split; intro H; try reflexivity;
    try discriminate; congruence.
Qed.

Definition Neg (A : formula) : formula := Impl A Falsum.
Definition Iff (A B : formula) : formula :=
  Conj (Impl A B) (Impl B A).

(** Renaming and capture-free instantiation. *)

Definition up (xi : nat -> nat) (n : nat) : nat :=
  match n with
  | O => O
  | S k => S (xi k)
  end.

Fixpoint rename (xi : nat -> nat) (A : formula) : formula :=
  match A with
  | Falsum => Falsum
  | Equal x y => Equal (xi x) (xi y)
  | Member x y => Member (xi x) (xi y)
  | Conj B C => Conj (rename xi B) (rename xi C)
  | Disj B C => Disj (rename xi B) (rename xi C)
  | Impl B C => Impl (rename xi B) (rename xi C)
  | All B => All (rename (up xi) B)
  | Ex B => Ex (rename (up xi) B)
  end.

Definition lift (A : formula) : formula := rename S A.

Definition subst_zero (t n : nat) : nat :=
  match n with
  | O => t
  | S k => k
  end.

(** [instantiate t A] replaces the variable bound by an outer quantifier
    with variable [t], shifting correctly below nested quantifiers. *)
Definition instantiate (t : nat) (A : formula) : formula :=
  rename (subst_zero t) A.

(** Tarskian semantics. *)

Section Semantics.
  Context {D : Type}.
  Variable member : D -> D -> Prop.

  Definition valuation := nat -> D.

  Definition extend (d : D) (rho : valuation) : valuation :=
    fun n =>
      match n with
      | O => d
      | S k => rho k
      end.

  Fixpoint satisfies (rho : valuation) (A : formula) : Prop :=
    match A with
    | Falsum => False
    | Equal x y => rho x = rho y
    | Member x y => member (rho x) (rho y)
    | Conj B C => satisfies rho B /\ satisfies rho C
    | Disj B C => satisfies rho B \/ satisfies rho C
    | Impl B C => satisfies rho B -> satisfies rho C
    | All B => forall d : D, satisfies (extend d rho) B
    | Ex B => exists d : D, satisfies (extend d rho) B
    end.

  Theorem satisfies_ext :
    forall (A : formula) (rho sigma : valuation),
      (forall n, rho n = sigma n) ->
      (satisfies rho A <-> satisfies sigma A).
  Proof.
    induction A; intros rho sigma Heq; simpl.
    - tauto.
    - rewrite (Heq n), (Heq n0). tauto.
    - rewrite (Heq n), (Heq n0). tauto.
    - rewrite (IHA1 rho sigma Heq), (IHA2 rho sigma Heq). tauto.
    - rewrite (IHA1 rho sigma Heq), (IHA2 rho sigma Heq). tauto.
    - rewrite (IHA1 rho sigma Heq), (IHA2 rho sigma Heq). tauto.
    - split; intros H d.
      + assert (Hext : forall n,
          extend d rho n = extend d sigma n).
        { intros [|n]; simpl. reflexivity. apply Heq. }
        apply (proj1 (IHA (extend d rho) (extend d sigma) Hext)).
        apply H.
      + assert (Hext : forall n,
          extend d rho n = extend d sigma n).
        { intros [|n]; simpl. reflexivity. apply Heq. }
        apply (proj2 (IHA (extend d rho) (extend d sigma) Hext)).
        apply H.
    - split; intros [d H]; exists d.
      + assert (Hext : forall n,
          extend d rho n = extend d sigma n).
        { intros [|n]; simpl. reflexivity. apply Heq. }
        apply (proj1 (IHA (extend d rho) (extend d sigma) Hext)).
        exact H.
      + assert (Hext : forall n,
          extend d rho n = extend d sigma n).
        { intros [|n]; simpl. reflexivity. apply Heq. }
        apply (proj2 (IHA (extend d rho) (extend d sigma) Hext)).
        exact H.
  Qed.

  Theorem satisfies_rename :
    forall (A : formula) (rho : valuation) (xi : nat -> nat),
      satisfies rho (rename xi A) <->
      satisfies (fun n => rho (xi n)) A.
  Proof.
    induction A; intros rho xi; simpl.
    - tauto.
    - reflexivity.
    - reflexivity.
    - rewrite IHA1, IHA2. tauto.
    - rewrite IHA1, IHA2. tauto.
    - rewrite IHA1, IHA2. tauto.
    - split.
      + intros H d.
        specialize (H d).
        apply (proj1 (IHA (extend d rho) (up xi))) in H.
        assert (Hext : forall n,
          extend d rho (up xi n) =
          extend d (fun n => rho (xi n)) n).
        { intros [|n]; reflexivity. }
        apply (proj1
          (satisfies_ext A
            (fun n => extend d rho (up xi n))
            (extend d (fun n => rho (xi n))) Hext)).
        exact H.
      + intros H d.
        apply (proj2 (IHA (extend d rho) (up xi))).
        assert (Hext : forall n,
          extend d rho (up xi n) =
          extend d (fun n => rho (xi n)) n).
        { intros [|n]; reflexivity. }
        apply (proj2
          (satisfies_ext A
            (fun n => extend d rho (up xi n))
            (extend d (fun n => rho (xi n))) Hext)).
        apply H.
    - split.
      + intros [d H].
        exists d.
        apply (proj1 (IHA (extend d rho) (up xi))) in H.
        assert (Hext : forall n,
          extend d rho (up xi n) =
          extend d (fun n => rho (xi n)) n).
        { intros [|n]; reflexivity. }
        apply (proj1
          (satisfies_ext A
            (fun n => extend d rho (up xi n))
            (extend d (fun n => rho (xi n))) Hext)).
        exact H.
      + intros [d H].
        exists d.
        apply (proj2 (IHA (extend d rho) (up xi))).
        assert (Hext : forall n,
          extend d rho (up xi n) =
          extend d (fun n => rho (xi n)) n).
        { intros [|n]; reflexivity. }
        apply (proj2
          (satisfies_ext A
            (fun n => extend d rho (up xi n))
            (extend d (fun n => rho (xi n))) Hext)).
        exact H.
  Qed.

  Lemma subst_zero_semantics :
    forall (rho : valuation) (t n : nat),
      rho (subst_zero t n) = extend (rho t) rho n.
  Proof.
    intros rho t [|n]; reflexivity.
  Qed.

  Theorem satisfies_instantiate :
    forall (A : formula) (rho : valuation) (t : nat),
      satisfies rho (instantiate t A) <->
      satisfies (extend (rho t) rho) A.
  Proof.
    intros A rho t.
    unfold instantiate.
    rewrite satisfies_rename.
    apply satisfies_ext.
    intro n.
    apply subst_zero_semantics.
  Qed.

  Definition satisfies_context (rho : valuation) (Gamma : list formula) :=
    forall A, In A Gamma -> satisfies rho A.

  Lemma satisfies_lifted_context :
    forall (rho : valuation) (Gamma : list formula),
      satisfies_context rho Gamma ->
      forall d : D, satisfies_context (extend d rho) (map lift Gamma).
  Proof.
    intros rho Gamma Hctx d A Hin.
    apply in_map_iff in Hin.
    destruct Hin as [B [<- Hin]].
    unfold lift.
    apply (proj2 (satisfies_rename B (extend d rho) S)).
    assert (Hext : forall n, rho n = extend d rho (S n)).
    { intro n. reflexivity. }
    apply (proj2
      (satisfies_ext B rho (fun n => extend d rho (S n)) Hext)).
    apply Hctx. exact Hin.
  Qed.

  Lemma satisfies_unlift :
    forall (rho : valuation) (d : D) (A : formula),
      satisfies (extend d rho) (lift A) <-> satisfies rho A.
  Proof.
    intros rho d A.
    unfold lift.
    rewrite satisfies_rename.
    apply satisfies_ext.
    intro n. reflexivity.
  Qed.
End Semantics.

(** A theory is an explicitly trusted collection of axioms. *)

Definition theory := formula -> Prop.

(** Intuitionistic natural deduction.  Classical principles may be supplied
    explicitly as axioms in the theory when desired. *)

Inductive derives (T : theory) : list formula -> formula -> Prop :=
| D_axiom : forall Gamma A,
    T A ->
    derives T Gamma A
| D_hyp : forall Gamma A,
    In A Gamma ->
    derives T Gamma A
| D_falsum_elim : forall Gamma A,
    derives T Gamma Falsum ->
    derives T Gamma A
| D_impl_intro : forall Gamma A B,
    derives T (A :: Gamma) B ->
    derives T Gamma (Impl A B)
| D_impl_elim : forall Gamma A B,
    derives T Gamma (Impl A B) ->
    derives T Gamma A ->
    derives T Gamma B
| D_conj_intro : forall Gamma A B,
    derives T Gamma A ->
    derives T Gamma B ->
    derives T Gamma (Conj A B)
| D_conj_elim_l : forall Gamma A B,
    derives T Gamma (Conj A B) ->
    derives T Gamma A
| D_conj_elim_r : forall Gamma A B,
    derives T Gamma (Conj A B) ->
    derives T Gamma B
| D_disj_intro_l : forall Gamma A B,
    derives T Gamma A ->
    derives T Gamma (Disj A B)
| D_disj_intro_r : forall Gamma A B,
    derives T Gamma B ->
    derives T Gamma (Disj A B)
| D_disj_elim : forall Gamma A B C,
    derives T Gamma (Disj A B) ->
    derives T (A :: Gamma) C ->
    derives T (B :: Gamma) C ->
    derives T Gamma C
| D_all_intro : forall Gamma A,
    derives T (map lift Gamma) A ->
    derives T Gamma (All A)
| D_all_elim : forall Gamma A t,
    derives T Gamma (All A) ->
    derives T Gamma (instantiate t A)
| D_ex_intro : forall Gamma A t,
    derives T Gamma (instantiate t A) ->
    derives T Gamma (Ex A)
| D_ex_elim : forall Gamma A B,
    derives T Gamma (Ex A) ->
    derives T (A :: map lift Gamma) (lift B) ->
    derives T Gamma B
| D_equal_refl : forall Gamma t,
    derives T Gamma (Equal t t)
| D_equal_elim : forall Gamma P s t,
    derives T Gamma (Equal s t) ->
    derives T Gamma (instantiate s P) ->
    derives T Gamma (instantiate t P)
| D_cut : forall Gamma A B,
    derives T Gamma A ->
    derives T (A :: Gamma) B ->
    derives T Gamma B.

Lemma lift_context_incl :
  forall Gamma Delta,
    incl Gamma Delta ->
    incl (map lift Gamma) (map lift Delta).
Proof.
  intros Gamma Delta Hinc A Hin.
  apply in_map_iff in Hin.
  destruct Hin as [B [<- Hin]].
  apply in_map.
  apply Hinc.
  exact Hin.
Qed.

Theorem derives_weakening :
  forall T Gamma A,
    derives T Gamma A ->
    forall Delta, incl Gamma Delta -> derives T Delta A.
Proof.
  intros T Gamma A Hderiv.
  induction Hderiv; intros Delta Hinc.
  - apply D_axiom. assumption.
  - apply D_hyp. apply Hinc. assumption.
  - apply D_falsum_elim. apply IHHderiv. exact Hinc.
  - apply D_impl_intro.
    apply IHHderiv.
    intros X [HX | HX].
    + left. exact HX.
    + right. apply Hinc. exact HX.
  - eapply D_impl_elim.
    + apply IHHderiv1. exact Hinc.
    + apply IHHderiv2. exact Hinc.
  - apply D_conj_intro.
    + apply IHHderiv1. exact Hinc.
    + apply IHHderiv2. exact Hinc.
  - eapply D_conj_elim_l. apply IHHderiv. exact Hinc.
  - eapply D_conj_elim_r. apply IHHderiv. exact Hinc.
  - apply D_disj_intro_l. apply IHHderiv. exact Hinc.
  - apply D_disj_intro_r. apply IHHderiv. exact Hinc.
  - eapply D_disj_elim.
    + apply IHHderiv1. exact Hinc.
    + apply IHHderiv2.
      intros X [HX | HX].
      * left. exact HX.
      * right. apply Hinc. exact HX.
    + apply IHHderiv3.
      intros X [HX | HX].
      * left. exact HX.
      * right. apply Hinc. exact HX.
  - apply D_all_intro.
    apply IHHderiv.
    apply lift_context_incl.
    exact Hinc.
  - apply D_all_elim.
    apply IHHderiv. exact Hinc.
  - apply D_ex_intro with (t := t).
    apply IHHderiv. exact Hinc.
  - eapply D_ex_elim.
    + apply IHHderiv1. exact Hinc.
    + apply IHHderiv2.
      intros X [HX | HX].
      * left. exact HX.
      * right.
        apply lift_context_incl with (Gamma := Gamma).
        -- exact Hinc.
        -- exact HX.
  - apply D_equal_refl.
  - eapply D_equal_elim.
    + apply IHHderiv1. exact Hinc.
    + apply IHHderiv2. exact Hinc.
  - eapply D_cut.
    + apply IHHderiv1. exact Hinc.
    + apply IHHderiv2.
      intros X [HX | HX].
      * left. exact HX.
      * right. apply Hinc. exact HX.
Qed.

(** This is the kernel-level counterpart of
    [specialize H t; contradiction]. *)
Lemma derives_all_neg_contradiction :
  forall (T : theory) Gamma P t C,
    derives T Gamma (All (Neg P)) ->
    derives T Gamma (instantiate t P) ->
    derives T Gamma C.
Proof.
  intros T Gamma P t C Hall HP.
  apply D_falsum_elim.
  eapply D_impl_elim with (A := instantiate t P).
  - change (derives T Gamma (instantiate t (Neg P))).
    apply D_all_elim.
    exact Hall.
  - exact HP.
Qed.

Section Soundness.
  Context {D : Type}.
  Variable member : D -> D -> Prop.
  Variable T : theory.

  Definition theory_valid : Prop :=
    forall (A : formula) (rho : nat -> D),
      T A -> satisfies member rho A.

  Theorem natural_deduction_sound :
    theory_valid ->
    forall (Gamma : list formula) (A : formula),
      derives T Gamma A ->
      forall rho : nat -> D,
        satisfies_context member rho Gamma ->
        satisfies member rho A.
  Proof.
    intros Htheory Gamma A Hderiv.
    induction Hderiv; intros rho Hctx; simpl in *.
    - apply Htheory. assumption.
    - apply Hctx. assumption.
    - exfalso. exact (IHHderiv rho Hctx).
    - intros HA.
      apply IHHderiv.
      intros C [HC | HC].
      + subst C. exact HA.
      + apply Hctx. exact HC.
    - apply (IHHderiv1 rho Hctx).
      apply IHHderiv2. exact Hctx.
    - split.
      + apply IHHderiv1. exact Hctx.
      + apply IHHderiv2. exact Hctx.
    - apply (IHHderiv rho Hctx).
    - apply (IHHderiv rho Hctx).
    - left. apply IHHderiv. exact Hctx.
    - right. apply IHHderiv. exact Hctx.
    - destruct (IHHderiv1 rho Hctx) as [HA | HB].
      + apply IHHderiv2.
        intros X [HX | HX].
        * subst X. exact HA.
        * apply Hctx. exact HX.
      + apply IHHderiv3.
        intros X [HX | HX].
        * subst X. exact HB.
        * apply Hctx. exact HX.
    - intros d.
      apply IHHderiv.
      apply satisfies_lifted_context.
      exact Hctx.
    - apply (proj2 (satisfies_instantiate member A rho t)).
      apply (IHHderiv rho Hctx).
    - exists (rho t).
      apply (proj1 (satisfies_instantiate member A rho t)).
      apply IHHderiv. exact Hctx.
    - destruct (IHHderiv1 rho Hctx) as [d HA].
      assert (Hlifted :
        satisfies_context member (extend d rho) (map lift Gamma)).
      { apply satisfies_lifted_context. exact Hctx. }
      assert (Hbranch :
        satisfies member (extend d rho) (lift B)).
      { apply IHHderiv2.
        intros X [HX | HX].
        - subst X. exact HA.
        - apply Hlifted. exact HX. }
      apply (proj1 (satisfies_unlift member rho d B)).
      exact Hbranch.
    - reflexivity.
    - apply (proj2 (satisfies_instantiate member P rho t)).
      rewrite <- (IHHderiv1 rho Hctx).
      apply (proj1 (satisfies_instantiate member P rho s)).
      apply IHHderiv2.
      exact Hctx.
    - apply IHHderiv2.
      intros X [HX | HX].
      + subst X. apply IHHderiv1. exact Hctx.
      + apply Hctx. exact HX.
  Qed.

  Corollary closed_theorem_sound :
    theory_valid ->
    forall A, derives T [] A ->
    forall rho, satisfies member rho A.
  Proof.
    intros HT A H rho.
    eapply natural_deduction_sound; eauto.
    intros B HIn. inversion HIn.
  Qed.

  Corollary relative_consistency :
    theory_valid ->
    D ->
    ~ derives T [] Falsum.
  Proof.
    intros HT d Hfalse.
    pose proof (closed_theorem_sound HT Hfalse (fun _ => d)).
    exact H.
  Qed.
End Soundness.
