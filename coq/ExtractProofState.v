(** Optional extraction entry point.

    This file is deliberately not part of the default [make coq] target.
    Run [make extract] only when an OCaml artifact is wanted.
 *)

From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From ZFCert Require Import ProofState TacticCompleteness.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "proof_state.ml"
  step run rule_step rule_run.
