(** ZFC axiom declarations in the first-order language from [FOL].

    The axiom schemata are represented by an open [zfc_axiom] predicate.
    Soundness of natural deduction is therefore conditional on a model
    satisfying each declared instance; Coq does not assume ZFC consistent.
 *)

From ZFCert Require Import FOL.

(** Empty set: exists e, forall x, x is not a member of e. *)
Definition empty_set_axiom : formula :=
  Ex (All (Neg (Member 0 1))).

(** Extensionality:
    forall x y, (forall z, z∈x <-> z∈y) -> x=y. *)
Definition extensionality_axiom : formula :=
  All (All
    (Impl
      (All (Iff (Member 0 2) (Member 0 1)))
      (Equal 1 0))).

(** Pairing:
    forall a b, exists p, forall x,
      x∈p <-> (x=a or x=b). *)
Definition pairing_axiom : formula :=
  All (All (Ex (All
    (Iff
      (Member 0 1)
      (Disj (Equal 0 3) (Equal 0 2)))))).

(** Union:
    forall a, exists u, forall x,
      x∈u <-> exists y, (x∈y and y∈a). *)
Definition union_axiom : formula :=
  All (Ex (All
    (Iff
      (Member 0 1)
      (Ex (Conj (Member 1 0) (Member 0 3)))))).

(** Power set:
    forall a, exists p, forall x,
      x∈p <-> forall z, z∈x -> z∈a. *)
Definition power_set_axiom : formula :=
  All (Ex (All
    (Iff
      (Member 0 1)
      (All (Impl (Member 0 1) (Member 0 3)))))).

(** Foundation:
    forall x, (exists a, a∈x) ->
      exists y, y∈x and forall z, z∈y -> not(z∈x). *)
Definition foundation_axiom : formula :=
  All
    (Impl
      (Ex (Member 0 1))
      (Ex
        (Conj
          (Member 0 1)
          (All
            (Impl
              (Member 0 1)
              (Neg (Member 0 2))))))).

(** Infinity, using the empty set and von Neumann successor:
    exists i, empty∈i and forall x∈i, (x union {x})∈i. *)
Definition infinity_axiom : formula :=
  Ex
    (Conj
      (Ex
        (Conj
          (All (Neg (Member 0 1)))
          (Member 0 1)))
      (All
        (Impl
          (Member 0 1)
          (Ex
            (Conj
              (Member 0 2)
              (All
                (Iff
                  (Member 0 1)
                  (Disj (Member 0 2) (Equal 0 2))))))))).

(** A separation body is written in the local variable convention
    [x = 0, a = 1, parameters = 2,3,...].  The renaming inserts the newly
    quantified subset at index 1. *)
Definition insert_subset (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => S (S k)
  end.

Definition separation_instance (P : formula) : formula :=
  All (Ex (All
    (Iff
      (Member 0 1)
      (Conj (Member 0 2) (rename insert_subset P))))).

(** A replacement body uses the convention
    [y = 0, x = 1, parameters = 2,3,...].

    [replacement_alternate] puts a second possible output [z] at index 0.
    [replacement_image] embeds the body below [a,b,y,x]. *)
Definition replacement_alternate (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 2
  | S (S k) => S (S (S k))
  end.

Definition replacement_image (n : nat) : nat :=
  match n with
  | 0 => 1
  | 1 => 0
  | S (S k) => S (S (S (S k)))
  end.

Definition replacement_instance (P : formula) : formula :=
  Impl
    (All
      (Ex
        (Conj
          P
          (All
            (Impl
              (rename replacement_alternate P)
              (Equal 0 1))))))
    (All
      (Ex
        (All
          (Iff
            (Member 0 1)
            (Ex
              (Conj
                (Member 0 3)
                (rename replacement_image P))))))).

(** Choice:
    every family of nonempty sets has a set selecting exactly one element
    from each member of the family. *)
Definition choice_axiom : formula :=
  All
    (Impl
      (All
        (Impl
          (Member 0 1)
          (Ex (Member 0 1))))
      (Ex
        (All
          (Impl
            (Member 0 2)
            (Ex
              (Conj
                (Conj (Member 0 1) (Member 0 2))
                (All
                  (Impl
                    (Conj (Member 0 2) (Member 0 3))
                    (Equal 0 1))))))))).

(** The inductive predicate is the only trusted ZFC theory supplied to
    [derives].  In particular, no constructor accepts an arbitrary formula
    as an axiom. *)
Inductive zfc_axiom : formula -> Prop :=
| ZFC_empty : zfc_axiom empty_set_axiom
| ZFC_extensionality : zfc_axiom extensionality_axiom
| ZFC_pairing : zfc_axiom pairing_axiom
| ZFC_union : zfc_axiom union_axiom
| ZFC_power_set : zfc_axiom power_set_axiom
| ZFC_foundation : zfc_axiom foundation_axiom
| ZFC_infinity : zfc_axiom infinity_axiom
| ZFC_separation : forall P, zfc_axiom (separation_instance P)
| ZFC_replacement : forall P, zfc_axiom (replacement_instance P)
| ZFC_choice : zfc_axiom choice_axiom.

(** ZFC uses classical first-order logic.  The set-theoretic axioms and
    excluded middle remain visibly separate in the trusted theory. *)
Inductive zfc_theory : formula -> Prop :=
| ZFC_set_axiom : forall A, zfc_axiom A -> zfc_theory A
| ZFC_excluded_middle : forall A, zfc_theory (Disj A (Neg A)).

(** Example: the empty-set axiom is directly derivable from the theory. *)
Example derives_empty_set :
  derives zfc_theory nil empty_set_axiom.
Proof.
  apply D_axiom.
  apply ZFC_set_axiom.
  apply ZFC_empty.
Qed.
