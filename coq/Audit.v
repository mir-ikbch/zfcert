(** Mechanical audit of the trusted assumptions used by the core results. *)

From ZFCert Require Import
  FOL ZFC ProofState TacticCompleteness NamedProofState NamedCommands
  CertifiedSession GlobalEnvironment.

Print Assumptions natural_deduction_sound.
Print Assumptions satisfies_substitute.
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
Print Assumptions named_rule_step_sound.
Print Assumptions named_rule_run_sound.
Print Assumptions named_step_sound.
Print Assumptions named_run_sound.
Print Assumptions named_axioms_are_zfc_sound.
Print Assumptions named_zfc_rule_run_sound.
Print Assumptions named_zfc_run_sound.
Print Assumptions named_default_all_intro_rule_step_sound.
Print Assumptions named_fixed_axiom_rule_step_sound.
Print Assumptions named_separation_axiom_rule_step_sound.
Print Assumptions named_replacement_axiom_rule_step_sound.
Print Assumptions named_execute_rule_sound.
Print Assumptions named_separation_tactic_step_sound.
Print Assumptions named_replacement_tactic_step_sound.
Print Assumptions replay_steps_sound.
Print Assumptions certified_step_sound.
Print Assumptions certified_run_sound.
Print Assumptions replay_certificate_sound.
Print Assumptions replay_certificate_with_constants_sound.
Print Assumptions certified_finalize_sound.
Print Assumptions global_declare_choice_source_sound.
Print Assumptions global_declare_choice_extends_environment.
Print Assumptions global_declare_skolem_source_sound.
