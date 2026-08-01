(** First-order logic for the language of set theory.

    Bound and local variables use de Bruijn indices.  Global constants are
    stable string-named symbols: they are never shifted or captured by a
    quantifier.  ZFC has no positive-arity function symbols.
    Equality is interpreted as Coq equality; [member] is supplied by a model.
 *)

From Coq Require Import List PeanoNat String.
Import ListNotations.

Set Implicit Arguments.

Inductive term : Type :=
| Var : nat -> term
| Const : string -> term.

Coercion Var : nat >-> term.

Definition term_eq_dec :
  forall s t : term, {s = t} + {s <> t}.
Proof.
  decide equality.
  - apply Nat.eq_dec.
  - apply String.string_dec.
Defined.

Definition term_eqb (s t : term) : bool :=
  if term_eq_dec s t then true else false.

Lemma term_eqb_true_iff :
  forall s t, term_eqb s t = true <-> s = t.
Proof.
  intros s t.
  unfold term_eqb.
  destruct (term_eq_dec s t); split; intro H; try reflexivity;
    try discriminate; congruence.
Qed.

Inductive formula : Type :=
| Falsum : formula
| Equal : term -> term -> formula
| Member : term -> term -> formula
| Conj : formula -> formula -> formula
| Disj : formula -> formula -> formula
| Impl : formula -> formula -> formula
| All : formula -> formula
| Ex : formula -> formula.

Definition formula_eq_dec :
  forall A B : formula, {A = B} + {A <> B}.
Proof.
  decide equality; apply term_eq_dec.
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

Definition rename_term (xi : nat -> nat) (t : term) : term :=
  match t with
  | Var n => Var (xi n)
  | Const name => Const name
  end.

Fixpoint rename (xi : nat -> nat) (A : formula) : formula :=
  match A with
  | Falsum => Falsum
  | Equal x y => Equal (rename_term xi x) (rename_term xi y)
  | Member x y => Member (rename_term xi x) (rename_term xi y)
  | Conj B C => Conj (rename xi B) (rename xi C)
  | Disj B C => Disj (rename xi B) (rename xi C)
  | Impl B C => Impl (rename xi B) (rename xi C)
  | All B => All (rename (up xi) B)
  | Ex B => Ex (rename (up xi) B)
  end.

Definition lift (A : formula) : formula := rename S A.

Definition lift_term (t : term) : term := rename_term S t.

Definition up_substitution (sigma : nat -> term) (n : nat) : term :=
  match n with
  | O => Var O
  | S k => lift_term (sigma k)
  end.

Definition substitute_term (sigma : nat -> term) (t : term) : term :=
  match t with
  | Var n => sigma n
  | Const name => Const name
  end.

Fixpoint substitute (sigma : nat -> term) (A : formula) : formula :=
  match A with
  | Falsum => Falsum
  | Equal x y =>
      Equal (substitute_term sigma x) (substitute_term sigma y)
  | Member x y =>
      Member (substitute_term sigma x) (substitute_term sigma y)
  | Conj B C => Conj (substitute sigma B) (substitute sigma C)
  | Disj B C => Disj (substitute sigma B) (substitute sigma C)
  | Impl B C => Impl (substitute sigma B) (substitute sigma C)
  | All B => All (substitute (up_substitution sigma) B)
  | Ex B => Ex (substitute (up_substitution sigma) B)
  end.

Definition subst_zero (t : term) (n : nat) : term :=
  match n with
  | O => t
  | S k => Var k
  end.

(** [instantiate t A] replaces the variable bound by an outer quantifier
    with term [t], shifting variables correctly below nested quantifiers while
    leaving constants unchanged. *)
Definition instantiate (t : term) (A : formula) : formula :=
  substitute (subst_zero t) A.

Example lift_preserves_constant_example :
  lift (Member (Const "empty"%string) (Var 0)) =
  Member (Const "empty"%string) (Var 1).
Proof. reflexivity. Qed.

Example instantiate_with_constant_example :
  instantiate (Const "empty"%string) (Member (Var 0) (Var 1)) =
  Member (Const "empty"%string) (Var 0).
Proof. reflexivity. Qed.

(** Tarskian semantics. *)

Section Semantics.
  Context {D : Type}.
  Variable member : D -> D -> Prop.

  Definition valuation := nat -> D.
  Definition constant_valuation := string -> D.

  Definition extend (d : D) (rho : valuation) : valuation :=
    fun n =>
      match n with
      | O => d
      | S k => rho k
      end.

  Definition eval_term
    (constants : constant_valuation) (rho : valuation) (t : term) : D :=
    match t with
    | Var n => rho n
    | Const name => constants name
    end.

  Fixpoint satisfies
    (constants : constant_valuation) (rho : valuation) (A : formula) : Prop :=
    match A with
    | Falsum => False
    | Equal x y => eval_term constants rho x = eval_term constants rho y
    | Member x y => member (eval_term constants rho x) (eval_term constants rho y)
    | Conj B C => satisfies constants rho B /\ satisfies constants rho C
    | Disj B C => satisfies constants rho B \/ satisfies constants rho C
    | Impl B C => satisfies constants rho B -> satisfies constants rho C
    | All B => forall d : D, satisfies constants (extend d rho) B
    | Ex B => exists d : D, satisfies constants (extend d rho) B
    end.

  Lemma eval_term_ext :
    forall constants (rho sigma : valuation) t,
      (forall n, rho n = sigma n) ->
      eval_term constants rho t = eval_term constants sigma t.
  Proof.
    intros constants rho sigma [n | name] Heq; simpl.
    - apply Heq.
    - reflexivity.
  Qed.

  Theorem satisfies_ext :
    forall constants (A : formula) (rho sigma : valuation),
      (forall n, rho n = sigma n) ->
      (satisfies constants rho A <-> satisfies constants sigma A).
  Proof.
    intros constants A.
    induction A as
      [|s t|s t|B IHB C IHC|B IHB C IHC|B IHB C IHC|B IHB|B IHB];
      intros rho sigma Heq; simpl.
    - tauto.
    - rewrite (eval_term_ext constants rho sigma s Heq).
      rewrite (eval_term_ext constants rho sigma t Heq). tauto.
    - rewrite (eval_term_ext constants rho sigma s Heq).
      rewrite (eval_term_ext constants rho sigma t Heq). tauto.
    - rewrite (IHB rho sigma Heq), (IHC rho sigma Heq). tauto.
    - rewrite (IHB rho sigma Heq), (IHC rho sigma Heq). tauto.
    - rewrite (IHB rho sigma Heq), (IHC rho sigma Heq). tauto.
    - split; intros H d.
      + assert (Hext : forall n,
          extend d rho n = extend d sigma n).
        { intros [|n]; simpl. reflexivity. apply Heq. }
        apply (proj1 (IHB (extend d rho) (extend d sigma) Hext)).
        apply H.
      + assert (Hext : forall n,
          extend d rho n = extend d sigma n).
        { intros [|n]; simpl. reflexivity. apply Heq. }
        apply (proj2 (IHB (extend d rho) (extend d sigma) Hext)).
        apply H.
    - split; intros [d H]; exists d.
      + assert (Hext : forall n,
          extend d rho n = extend d sigma n).
        { intros [|n]; simpl. reflexivity. apply Heq. }
        apply (proj1 (IHB (extend d rho) (extend d sigma) Hext)).
        exact H.
      + assert (Hext : forall n,
          extend d rho n = extend d sigma n).
        { intros [|n]; simpl. reflexivity. apply Heq. }
        apply (proj2 (IHB (extend d rho) (extend d sigma) Hext)).
        exact H.
  Qed.

  Lemma eval_rename_term :
    forall constants (rho : valuation) xi t,
      eval_term constants rho (rename_term xi t) =
      eval_term constants (fun n => rho (xi n)) t.
  Proof.
    intros constants rho xi [n | name]; reflexivity.
  Qed.

  Theorem satisfies_rename :
    forall constants (A : formula) (rho : valuation) (xi : nat -> nat),
      satisfies constants rho (rename xi A) <->
      satisfies constants (fun n => rho (xi n)) A.
  Proof.
    intros constants A.
    induction A as
      [|s t|s t|B IHB C IHC|B IHB C IHC|B IHB C IHC|B IHB|B IHB];
      intros rho xi; simpl.
    - tauto.
    - rewrite !eval_rename_term. reflexivity.
    - rewrite !eval_rename_term. reflexivity.
    - rewrite IHB, IHC. tauto.
    - rewrite IHB, IHC. tauto.
    - rewrite IHB, IHC. tauto.
    - split.
      + intros H d.
        specialize (H d).
        apply (proj1 (IHB (extend d rho) (up xi))) in H.
        assert (Hext : forall n,
          extend d rho (up xi n) =
          extend d (fun n => rho (xi n)) n).
        { intros [|n]; reflexivity. }
        apply (proj1
          (satisfies_ext constants B
            (fun n => extend d rho (up xi n))
            (extend d (fun n => rho (xi n))) Hext)).
        exact H.
      + intros H d.
        apply (proj2 (IHB (extend d rho) (up xi))).
        assert (Hext : forall n,
          extend d rho (up xi n) =
          extend d (fun n => rho (xi n)) n).
        { intros [|n]; reflexivity. }
        apply (proj2
          (satisfies_ext constants B
            (fun n => extend d rho (up xi n))
            (extend d (fun n => rho (xi n))) Hext)).
        apply H.
    - split.
      + intros [d H].
        exists d.
        apply (proj1 (IHB (extend d rho) (up xi))) in H.
        assert (Hext : forall n,
          extend d rho (up xi n) =
          extend d (fun n => rho (xi n)) n).
        { intros [|n]; reflexivity. }
        apply (proj1
          (satisfies_ext constants B
            (fun n => extend d rho (up xi n))
            (extend d (fun n => rho (xi n))) Hext)).
        exact H.
      + intros [d H].
        exists d.
        apply (proj2 (IHB (extend d rho) (up xi))).
        assert (Hext : forall n,
          extend d rho (up xi n) =
          extend d (fun n => rho (xi n)) n).
        { intros [|n]; reflexivity. }
        apply (proj2
          (satisfies_ext constants B
            (fun n => extend d rho (up xi n))
            (extend d (fun n => rho (xi n))) Hext)).
        exact H.
  Qed.

  Lemma eval_lift_term :
    forall constants (rho : valuation) d t,
      eval_term constants (extend d rho) (lift_term t) =
      eval_term constants rho t.
  Proof.
    intros constants rho d [n | name]; reflexivity.
  Qed.

  Lemma eval_up_substitution :
    forall constants (rho : valuation) d sigma n,
      eval_term constants (extend d rho) (up_substitution sigma n) =
      extend d (fun k => eval_term constants rho (sigma k)) n.
  Proof.
    intros constants rho d sigma [|n]; simpl.
    - reflexivity.
    - apply eval_lift_term.
  Qed.

  Lemma eval_substitute_term :
    forall constants (rho : valuation) sigma t,
      eval_term constants rho (substitute_term sigma t) =
      eval_term constants
        (fun n => eval_term constants rho (sigma n)) t.
  Proof.
    intros constants rho sigma [n | name]; reflexivity.
  Qed.

  Theorem satisfies_substitute :
    forall constants (A : formula) (rho : valuation) (sigma : nat -> term),
      satisfies constants rho (substitute sigma A) <->
      satisfies constants
        (fun n => eval_term constants rho (sigma n)) A.
  Proof.
    intros constants A.
    induction A as
      [|s t|s t|B IHB C IHC|B IHB C IHC|B IHB C IHC|B IHB|B IHB];
      intros rho sigma; simpl.
    - tauto.
    - rewrite !eval_substitute_term. reflexivity.
    - rewrite !eval_substitute_term. reflexivity.
    - rewrite IHB, IHC. tauto.
    - rewrite IHB, IHC. tauto.
    - rewrite IHB, IHC. tauto.
    - split.
      + intros H d.
        specialize (H d).
        apply (proj1 (IHB (extend d rho) (up_substitution sigma))) in H.
        assert (Hext : forall n,
          eval_term constants (extend d rho) (up_substitution sigma n) =
          extend d (fun k => eval_term constants rho (sigma k)) n).
        { intro n. apply eval_up_substitution. }
        apply (proj1
          (satisfies_ext constants B
            (fun n =>
              eval_term constants (extend d rho) (up_substitution sigma n))
            (extend d (fun k => eval_term constants rho (sigma k)))
            Hext)).
        exact H.
      + intros H d.
        apply (proj2 (IHB (extend d rho) (up_substitution sigma))).
        assert (Hext : forall n,
          eval_term constants (extend d rho) (up_substitution sigma n) =
          extend d (fun k => eval_term constants rho (sigma k)) n).
        { intro n. apply eval_up_substitution. }
        apply (proj2
          (satisfies_ext constants B
            (fun n =>
              eval_term constants (extend d rho) (up_substitution sigma n))
            (extend d (fun k => eval_term constants rho (sigma k)))
            Hext)).
        apply H.
    - split.
      + intros [d H].
        exists d.
        apply (proj1 (IHB (extend d rho) (up_substitution sigma))) in H.
        assert (Hext : forall n,
          eval_term constants (extend d rho) (up_substitution sigma n) =
          extend d (fun k => eval_term constants rho (sigma k)) n).
        { intro n. apply eval_up_substitution. }
        apply (proj1
          (satisfies_ext constants B
            (fun n =>
              eval_term constants (extend d rho) (up_substitution sigma n))
            (extend d (fun k => eval_term constants rho (sigma k)))
            Hext)).
        exact H.
      + intros [d H].
        exists d.
        apply (proj2 (IHB (extend d rho) (up_substitution sigma))).
        assert (Hext : forall n,
          eval_term constants (extend d rho) (up_substitution sigma n) =
          extend d (fun k => eval_term constants rho (sigma k)) n).
        { intro n. apply eval_up_substitution. }
        apply (proj2
          (satisfies_ext constants B
            (fun n =>
              eval_term constants (extend d rho) (up_substitution sigma n))
            (extend d (fun k => eval_term constants rho (sigma k)))
            Hext)).
        exact H.
  Qed.

  Lemma subst_zero_semantics :
    forall constants (rho : valuation) (t : term) n,
      eval_term constants rho (subst_zero t n) =
      extend (eval_term constants rho t) rho n.
  Proof.
    intros constants rho t [|n]; reflexivity.
  Qed.

  Theorem satisfies_instantiate :
    forall constants (A : formula) (rho : valuation) (t : term),
      satisfies constants rho (instantiate t A) <->
      satisfies constants (extend (eval_term constants rho t) rho) A.
  Proof.
    intros constants A rho t.
    unfold instantiate.
    rewrite satisfies_substitute.
    apply satisfies_ext.
    intro n.
    apply subst_zero_semantics.
  Qed.

  Definition satisfies_context
    (constants : constant_valuation)
    (rho : valuation) (Gamma : list formula) :=
    forall A, In A Gamma -> satisfies constants rho A.

  Lemma satisfies_lifted_context :
    forall constants (rho : valuation) (Gamma : list formula),
      satisfies_context constants rho Gamma ->
      forall d : D,
        satisfies_context constants (extend d rho) (map lift Gamma).
  Proof.
    intros constants rho Gamma Hctx d A Hin.
    apply in_map_iff in Hin.
    destruct Hin as [B [<- Hin]].
    unfold lift.
    apply (proj2 (satisfies_rename constants B (extend d rho) S)).
    assert (Hext : forall n, rho n = extend d rho (S n)).
    { intro n. reflexivity. }
    apply (proj2
      (satisfies_ext constants B
        rho (fun n => extend d rho (S n)) Hext)).
    apply Hctx. exact Hin.
  Qed.

  Lemma satisfies_unlift :
    forall constants (rho : valuation) (d : D) (A : formula),
      satisfies constants (extend d rho) (lift A) <->
      satisfies constants rho A.
  Proof.
    intros constants rho d A.
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
  Variable constants : string -> D.
  Variable T : theory.

  Definition theory_valid : Prop :=
    forall (A : formula) (rho : nat -> D),
      T A -> satisfies member constants rho A.

  Theorem natural_deduction_sound :
    theory_valid ->
    forall (Gamma : list formula) (A : formula),
      derives T Gamma A ->
      forall rho : nat -> D,
        satisfies_context member constants rho Gamma ->
        satisfies member constants rho A.
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
    - apply (proj2 (satisfies_instantiate member constants A rho t)).
      apply (IHHderiv rho Hctx).
    - exists (eval_term constants rho t).
      apply (proj1 (satisfies_instantiate member constants A rho t)).
      apply IHHderiv. exact Hctx.
    - destruct (IHHderiv1 rho Hctx) as [d HA].
      assert (Hlifted :
        satisfies_context member constants
          (extend d rho) (map lift Gamma)).
      { apply satisfies_lifted_context. exact Hctx. }
      assert (Hbranch :
        satisfies member constants (extend d rho) (lift B)).
      { apply IHHderiv2.
        intros X [HX | HX].
        - subst X. exact HA.
        - apply Hlifted. exact HX. }
      apply (proj1 (satisfies_unlift member constants rho d B)).
      exact Hbranch.
    - reflexivity.
    - apply (proj2 (satisfies_instantiate member constants P rho t)).
      rewrite <- (IHHderiv1 rho Hctx).
      apply (proj1 (satisfies_instantiate member constants P rho s)).
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
    forall rho, satisfies member constants rho A.
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
