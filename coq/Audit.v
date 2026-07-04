(** Mechanical audit of the trusted assumptions used by the core results. *)

From ZFCert Require Import FOL ZFC ProofState TacticCompleteness.

Print Assumptions natural_deduction_sound.
Print Assumptions closed_theorem_sound.
Print Assumptions relative_consistency.
Print Assumptions derives_empty_set.
Print Assumptions step_sound.
Print Assumptions run_sound.
Print Assumptions successful_run_derives.
Print Assumptions intro_imp_reversible.
Print Assumptions split_reversible.
Print Assumptions rule_step_sound.
Print Assumptions rule_run_sound.
Print Assumptions successful_rule_run_derives.
Print Assumptions derives_has_rule_list.
Print Assumptions derives_iff_rule_success.
Print Assumptions derives_has_tactic_list.
Print Assumptions derives_iff_success.
