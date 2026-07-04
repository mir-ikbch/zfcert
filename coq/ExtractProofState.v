(** Optional extraction entry point.

    This file is deliberately not part of the default [make coq] target.
    Run [make extract] only when an OCaml artifact is wanted.
 *)

From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From ZFCert Require Import ProofState TacticCompleteness ZFC.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "proof_state.ml"
  start state_goals
  step run rule_step rule_run
  empty_set_axiom extensionality_axiom pairing_axiom union_axiom
  power_set_axiom foundation_axiom infinity_axiom choice_axiom
  separation_instance replacement_instance.
