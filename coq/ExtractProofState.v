(** Optional extraction entry point.

    This file is deliberately not part of the default [make coq] target.
    Run [make extract] only when an OCaml artifact is wanted.
 *)

From Coq Require Import
  Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString.
From ZFCert Require Import
  ProofState TacticCompleteness ZFC NamedProofState NamedCommands
  CertifiedSession.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "proof_state.ml"
  start state_goals
  step run rule_step rule_run
  named_start named_goals named_solved
  named_step named_run named_rule_step named_rule_run
  named_default_all_intro_rule_step
  named_fixed_axiom_rule_step
  named_separation_axiom_rule_step
  named_replacement_axiom_rule_step
  named_separation_tactic_step
  named_replacement_tactic_step
  named_execute_rule
  certified_start certified_goals certified_solved
  one_step certified_step certified_run
  certified_certificate replay_certificate certified_finalize
  certified_execute_rule
  certified_separation_tactic
  certified_replacement_tactic
  empty_set_axiom extensionality_axiom pairing_axiom union_axiom
  power_set_axiom foundation_axiom infinity_axiom choice_axiom
  separation_instance replacement_instance.
