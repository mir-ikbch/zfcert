(** Certified global constants and facts.

    A global environment can only be extended by replaying a certificate for
    an existential statement under the facts already present.  The selected
    witness becomes a fresh 0-ary application and the instantiated body becomes
    a named global fact.  Skolem declarations add a named function application
    and the universally closed Skolemized instance.  This module is
    computational and intended for extraction.
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

Fixpoint named_arguments_of_names (names : list string) : named_arguments :=
  match names with
  | [] => NNNil
  | name :: rest => NNCons (NName name) (named_arguments_of_names rest)
  end.

Fixpoint named_term_replace
  (variable : string) (replacement : named_term) (source : named_term)
  : named_term :=
  match source with
  | NName name =>
      if String.eqb name variable then replacement else NName name
  | NApp name arguments =>
      NApp name (named_arguments_replace variable replacement arguments)
  end

with named_arguments_replace
  (variable : string) (replacement : named_term) (source : named_arguments)
  : named_arguments :=
  match source with
  | NNNil => NNNil
  | NNCons argument rest =>
      NNCons (named_term_replace variable replacement argument)
        (named_arguments_replace variable replacement rest)
  end.

Fixpoint named_formula_replace
  (variable : string) (replacement : named_term) (source : named_formula)
  : named_formula :=
  match source with
  | NFalsum => NFalsum
  | NEqual left_term right_term =>
      NEqual (named_term_replace variable replacement left_term)
        (named_term_replace variable replacement right_term)
  | NMember left_term right_term =>
      NMember (named_term_replace variable replacement left_term)
        (named_term_replace variable replacement right_term)
  | NConj left_formula right_formula =>
      NConj (named_formula_replace variable replacement left_formula)
        (named_formula_replace variable replacement right_formula)
  | NDisj left_formula right_formula =>
      NDisj (named_formula_replace variable replacement left_formula)
        (named_formula_replace variable replacement right_formula)
  | NImpl left_formula right_formula =>
      NImpl (named_formula_replace variable replacement left_formula)
        (named_formula_replace variable replacement right_formula)
  | NNeg body => NNeg (named_formula_replace variable replacement body)
  | NIff left_formula right_formula =>
      NIff (named_formula_replace variable replacement left_formula)
        (named_formula_replace variable replacement right_formula)
  | NAll binder body =>
      if String.eqb binder variable
      then NAll binder body
      else NAll binder (named_formula_replace variable replacement body)
  | NEx binder body =>
      if String.eqb binder variable
      then NEx binder body
      else NEx binder (named_formula_replace variable replacement body)
  end.

Fixpoint named_skolemize
  (function_name : string) (binders : list string) (source : named_formula)
  : option named_formula :=
  match source with
  | NAll binder body =>
      if string_mem binder binders then None else
        match named_skolemize function_name (binders ++ [binder]) body with
        | Some result => Some (NAll binder result)
        | None => None
        end
  | NEx witness body =>
      if string_mem witness binders then None else
        Some (named_formula_replace witness
          (NApp function_name (named_arguments_of_names binders)) body)
  | _ => None
  end.

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
                instantiate (App constant_name TNil) core_body
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

Definition global_declare_skolem
  (function_name fact_name : string)
  (source : named_formula)
  (proof : certificate)
  (environment : global_environment)
  : named_result global_environment :=
  if string_mem function_name (global_constants environment)
  then NError (NVariableAlreadyUsed function_name)
  else if string_mem fact_name (global_fact_names environment)
  then NError (NHypothesisAlreadyUsed fact_name)
  else
    match named_skolemize function_name [] source with
    | None => NError NWrongNamedShape
    | Some skolemized =>
        named_bind (global_replay environment source proof)
          (fun replayed =>
        if named_solved replayed
        then
          let constants := function_name :: global_constants environment in
          named_bind (elaborate constants [] [] skolemized)
            (fun core_fact =>
          NOk (GlobalEnvironment
            constants
            (NamedHypothesis fact_name skolemized ::
              global_named_facts environment)
            (core_fact :: global_core_facts environment)))
        else NError NWrongNamedShape)
    end.

Theorem global_declare_skolem_source_sound :
  forall function_name fact_name source proof environment next,
    global_declare_skolem function_name fact_name source proof environment =
      NOk next ->
    named_formula_provable_with_environment
      (global_constants environment) []
      (global_core_facts environment) source.
Proof.
  intros function_name fact_name source proof environment next Hdeclare.
  unfold global_declare_skolem in Hdeclare.
  destruct (string_mem function_name (global_constants environment));
    try discriminate.
  destruct (string_mem fact_name (global_fact_names environment));
    try discriminate.
  destruct (named_skolemize function_name [] source) as [skolemized |]
    eqn:Hshape; try discriminate.
  destruct (global_replay environment source proof)
    as [replayed | replay_error] eqn:Hreplay;
    cbn in Hdeclare; try discriminate.
  destruct (named_solved replayed) eqn:Hsolved;
    cbn in Hdeclare; try discriminate.
  unfold global_replay in Hreplay.
  eapply replay_certificate_with_environment_sound.
  - exact Hreplay.
  - exact Hsolved.
Qed.

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
    (instantiate (App constant_name TNil) core_body))
    as [named_fact | reification_error] eqn:Hreify;
    cbn in Hdeclare; try discriminate.
  inversion Hdeclare; subst next. cbn.
  split; [reflexivity|].
  exists named_fact, (instantiate (App constant_name TNil) core_body).
  split; reflexivity.
Qed.

Example empty_environment_has_no_constants :
  global_constants empty_global_environment = [].
Proof. reflexivity. Qed.
