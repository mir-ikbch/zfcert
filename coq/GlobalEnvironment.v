(** Certified global constants and facts.

    A global environment can only be extended by replaying a certificate for
    an existential statement under the facts already present.  The selected
    witness becomes a fresh [Const] and the instantiated body becomes a named
    global fact.  This module is computational and intended for extraction.
 *)

From Coq Require Import List String Bool.
From ZFCert Require Import
  FOL ProofState NamedProofState CertifiedSession ZFC.
Import ListNotations.
Open Scope string_scope.

Record global_environment : Type := GlobalEnvironment {
  global_constants : list string;
  global_named_facts : list named_hypothesis;
  global_core_facts : list formula
}.

Definition empty_global_environment : global_environment :=
  GlobalEnvironment [] [] [].

Definition global_fact_names
  (environment : global_environment) : list string :=
  map named_hypothesis_name (global_named_facts environment).

Definition global_start
  (environment : global_environment) (source : named_formula)
  : named_result certified_state :=
  certified_start_with_environment
    (global_constants environment)
    []
    (global_named_facts environment)
    (global_core_facts environment)
    source.

Definition global_replay
  (environment : global_environment)
  (source : named_formula)
  (proof : certificate) : named_result named_state :=
  replay_certificate_with_environment
    (global_constants environment)
    []
    (global_named_facts environment)
    (global_core_facts environment)
    source proof.

Definition global_declare_choice
  (constant_name fact_name : string)
  (source : named_formula)
  (proof : certificate)
  (environment : global_environment)
  : named_result global_environment :=
  if string_mem constant_name (global_constants environment)
  then NError (NVariableAlreadyUsed constant_name)
  else if string_mem fact_name (global_fact_names environment)
  then NError (NHypothesisAlreadyUsed fact_name)
  else
    match source with
    | NEx _ body =>
        named_bind (global_replay environment source proof)
          (fun replayed =>
        if named_solved replayed
        then
          named_bind
            (elaborate (global_constants environment) [] [] source)
            (fun core_source =>
          match core_source with
          | Ex core_body =>
              let constants :=
                constant_name :: global_constants environment
              in
              let core_fact :=
                instantiate (Const constant_name) core_body
              in
              named_bind
                (reify constants []
                  (named_binder_names body) core_fact)
                (fun named_fact =>
              NOk (GlobalEnvironment
                constants
                (NamedHypothesis fact_name named_fact ::
                  global_named_facts environment)
                (core_fact :: global_core_facts environment)))
          | _ => NError NWrongNamedShape
          end)
        else NError NWrongNamedShape)
    | _ => NError NWrongNamedShape
    end.

(** Any accepted declaration has a kernel-checked derivation of its source
    existential from exactly the preceding global facts. *)
Theorem global_declare_choice_source_sound :
  forall constant_name fact_name source proof environment next,
    global_declare_choice constant_name fact_name source proof environment =
      NOk next ->
    named_formula_provable_with_environment
      (global_constants environment) []
      (global_core_facts environment) source.
Proof.
  intros constant_name fact_name source proof environment next Hdeclare.
  unfold global_declare_choice in Hdeclare.
  destruct (string_mem constant_name (global_constants environment));
    try discriminate.
  destruct (string_mem fact_name (global_fact_names environment));
    try discriminate.
  destruct source as
    [|eq_l eq_r|mem_l mem_r|conj_l conj_r|disj_l disj_r
     |impl_l impl_r|neg_body|iff_l iff_r|all_binder all_body
     |binder body]; cbn in Hdeclare; try discriminate.
  destruct (global_replay environment (NEx binder body) proof)
    as [replayed | replay_error] eqn:Hreplay;
    cbn in Hdeclare; try discriminate.
  destruct (named_solved replayed) eqn:Hsolved;
    cbn in Hdeclare; try discriminate.
  unfold global_replay in Hreplay.
  eapply replay_certificate_with_environment_sound.
  - exact Hreplay.
  - exact Hsolved.
Qed.

(** Successful declarations have exactly the advertised computational shape:
    one constant and one aligned named/core fact are prepended. *)
Theorem global_declare_choice_extends_environment :
  forall constant_name fact_name source proof environment next,
    global_declare_choice constant_name fact_name source proof environment =
      NOk next ->
    global_constants next =
      constant_name :: global_constants environment /\
    exists named_fact core_fact,
      global_named_facts next =
        NamedHypothesis fact_name named_fact ::
          global_named_facts environment /\
      global_core_facts next =
        core_fact :: global_core_facts environment.
Proof.
  intros constant_name fact_name source proof environment next Hdeclare.
  unfold global_declare_choice in Hdeclare.
  destruct (string_mem constant_name (global_constants environment));
    try discriminate.
  destruct (string_mem fact_name (global_fact_names environment));
    try discriminate.
  destruct source as
    [|eq_l eq_r|mem_l mem_r|conj_l conj_r|disj_l disj_r
     |impl_l impl_r|neg_body|iff_l iff_r|all_binder all_body
     |binder body]; cbn in Hdeclare; try discriminate.
  destruct (global_replay environment (NEx binder body) proof)
    as [replayed | replay_error] eqn:Hreplay;
    cbn in Hdeclare; try discriminate.
  destruct (named_solved replayed) eqn:Hsolved;
    cbn in Hdeclare; try discriminate.
  destruct (string_mem binder (global_constants environment))
    eqn:Hbinder; cbn in Hdeclare; try discriminate.
  destruct (elaborate (global_constants environment) [binder] [] body)
    as [core_body | elaboration_error] eqn:Helaborate;
    cbn in Hdeclare; try discriminate.
  destruct (reify
    (constant_name :: global_constants environment) []
    (named_binder_names body)
    (instantiate (Const constant_name) core_body))
    as [named_fact | reification_error] eqn:Hreify;
    cbn in Hdeclare; try discriminate.
  inversion Hdeclare; subst next. cbn.
  split; [reflexivity|].
  exists named_fact, (instantiate (Const constant_name) core_body).
  split; reflexivity.
Qed.

Example empty_environment_has_no_constants :
  global_constants empty_global_environment = [].
Proof. reflexivity. Qed.
