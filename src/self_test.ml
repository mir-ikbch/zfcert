let terminate_lines script =
  script
  |> String.split_on_char '\n'
  |> List.map (fun line ->
       if String.trim line = "" then line else line ^ ".")
  |> String.concat "\n"

let contains text fragment =
  let text_length = String.length text in
  let fragment_length = String.length fragment in
  let rec search index =
    if index + fragment_length > text_length then false
    else if String.sub text index fragment_length = fragment then true
    else search (index + 1)
  in
  search 0

let valid_scripts =
  [
    "theorem refl : forall x, x = x\nintro x\nrefl\nqed";
    "theorem intros_named : forall x, forall y, (x = y -> x = y)\nintros x y H\nexact H\nqed";
    "theorem intros_auto : forall x, forall y, (x = y -> x = y)\nintros\nexact H\nqed";
    "theorem resolution_basic : forall p, forall q, ((p = p or q = q) -> (not (p = p) -> q = q))\nintros p q Hclause Hnot\nresolution\nqed";
    "theorem resolution_ignores_opaque : forall p, forall q, ((forall x, x = x) -> ((p = p or q = q) -> (not (p = p) -> q = q)))\nintros p q Hopaque Hclause Hnot\nresolution\nqed";
    "theorem resolution_implication_contradiction : forall p, forall q, (((p = p -> q = q)) -> (not (p = p -> q = q) -> q = q))\nintros p q Himp HnotImp\nresolution\nqed";
    "theorem resolution_implication : forall p, forall q, ((p = p -> q = q) -> (p = p -> q = q))\nintros p q Himp Hp\nresolution\nqed";
    "theorem resolution_equivalence : forall p, forall q, ((p = p <-> q = q) -> (p = p -> q = q))\nintros p q Hiff Hp\nresolution\nqed";
    "theorem resolution_equivalence_backward : forall p, forall q, ((p = p <-> q = q) -> (q = q -> p = p))\nintros p q Hiff Hq\nresolution\nqed";
    "theorem resolution_compound_implication : forall p, forall q, forall r, (((p = p and q = q) -> r = r) -> ((p = p and q = q) -> r = r))\nintros p q r Himp Hpq\nresolution\nqed";
    "theorem resolution_negated_implication : forall p, forall q, (not (p = p -> q = q) -> p = p)\nintros p q Hnot\nresolution\nqed";
    "theorem resolution_negated_equivalence : forall p, forall q, ((not (p = p <-> q = q)) -> ((p = p) -> ((q = q) -> false)))\nintros p q Hnot Hleft Hright\nresolution\nqed";
    "theorem resolution_forall : forall a, ((forall x, x = x) -> (not (a = a) -> a = a))\nintros a Hall Hnot\nresolution\nqed";
    "theorem resolution_forall_two : forall a, ((forall x, x = a) -> ((forall y, not (y = a)) -> false))\nintros a Hleft Hright\nresolution\nqed";
    "theorem resolution_forall_implication : forall a, forall x, ((forall y, (y = a -> y = y)) -> (x = a -> x = x))\nintros a x Hall Hx\nresolution\nqed";
    "choose pair Hpair from pairing\ntheorem resolution_forall_function : forall a, ((forall x, x = pair(a, a)) -> (not (pair(a, a) = pair(a, a)) -> pair(a, a) = pair(a, a)))\nintros a Hall Hnot\nresolution\nqed";
    "theorem resolution_goal_conjunction : forall p, forall q, ((p = p) -> ((q = q) -> (p = p and q = q)))\nintros p q Hp Hq\nresolution\nqed";
    "theorem resolution_goal_disjunction : forall p, forall q, ((p = p) -> (p = p or q = q))\nintros p q Hp\nresolution\nqed";
    "theorem resolution_goal_implication : forall p, forall q, (not (p = p) -> (p = p -> q = q))\nintros p q Hnot\nresolution\nqed";
    "theorem resolution_goal_equivalence : forall p, forall q, ((p = p) -> ((q = q) -> (p = p <-> q = q)))\nintros p q Hp Hq\nresolution\nqed";
    "theorem resolution_goal_forall : ((forall x, x = x) -> forall y, y = y)\nintro Hall\nresolution\nqed";
    "theorem resolution_exists_goal : forall a, (a = a -> exists x, x = a)\nintros a Ha\nresolution\nqed";
    "theorem resolution_nested_exists_goal : forall a, (a = a -> exists x, exists y, x = a)\nintros a Ha\nresolution\nqed";
    "theorem resolution_exists_hypothesis : forall a, ((exists x, x = a) -> ((forall x, not (x = a)) -> false))\nintros a H Hnot\nresolution\nqed";
    "theorem resolution_not_exists_hypothesis : forall a, (not (exists x, x = a) -> forall y, not (y = a))\nintros a H\nresolution\nqed";
    "theorem resolution_nested_not_exists_hypothesis : (not (exists x, exists y, x = y) -> forall x, forall y, not (x = y))\nintro H\nresolution\nqed";
    "theorem resolution_nested_exists_hypothesis : ((exists x, exists y, x = y) -> ((forall x, forall y, not (x = y)) -> false))\nintros H Hnot\nresolution\nqed";
    "theorem resolution_chain : forall p, forall q, forall r, ((p = p or q = q) -> ((not (p = p) or r = r) -> (not (q = q) -> r = r)))\nintros p q r H1 H2 H3\nresolution\nqed";
    "theorem resolution_conjunction : forall p, forall q, ((p = p and q = q) -> (not (p = p) -> q = q))\nintros p q H1 H2\nresolution\nqed";
    "theorem resolution_falsum : forall p, ((p = p and not (p = p)) -> false)\nintros p H\nresolution\nqed";
    "theorem resolution_distributed : forall p, forall q, forall r, (((p = p and q = q) or r = r) -> (not (p = p) -> r = r))\nintros p q r H1 H2\nresolution\nqed";
    "theorem intros_shadow : forall x, (x = x -> forall x, x = x)\nintros\nrefl\nqed";
    "theorem compact_quantifiers : forall x y z, (x = z -> x = z)\nintros x y z H\nexact H\nqed";
    "theorem empty : exists e, forall x, not (x in e)\nexact empty_set\nqed";
    "theorem ext : forall a, forall b, ((forall z, (z in a <-> z in b)) -> a = b)\nintro a\nintro b\nintro H\napply extensionality\nexact H\nqed";
    "theorem ext_specialized : forall a, forall b, ((forall z, (z in a <-> z in b)) -> a = b)\nintro a\nintro b\nintro H\nspecialize extensionality a b as E\napply E\nexact H\nqed";
    "theorem sep : forall a, exists b, forall x, (x in b <-> (x in a and not (x in x)))\nintro a\nseparation S a x : not (x in x)\nexact S\nqed";
    "choose pair Hpair from pairing\ntheorem sep_term : forall a, forall b, exists c, forall x, (x in c <-> (x in pair(a, b) and not (x in x)))\nintro a\nintro b\nseparation S pair(a, b) x : not (x in x)\nexact S\nqed";
    "theorem rep : forall a, ((forall x, exists y, (y = x and forall z, (z = x -> z = y))) -> exists b, forall y, (y in b <-> exists x, (x in a and y = x)))\nintro a\nreplacement R a x y : y = x\nexact R\nqed";
    "theorem universal_contradiction : forall a, forall b, ((forall x, not (x in b)) -> (a in b -> b in a))\nintro a\nintro b\nintro H\nintro Ha\nspecialize H a as Hna\ncontradiction\nqed";
    "choose f Hf from union\ntheorem specialize_function : forall x, ((forall y, y = x) -> f(x) = x)\nintros x H\nspecialize H f(x) as Hinst\nexact Hinst\nqed";
    "choose f Hf from union\nchoose pair Hpair from pairing\ntheorem specialize_multiple_functions : forall x, ((forall a b, a = b) -> pair(x, f(x)) = f(pair(x, x)))\nintros x H\nspecialize H pair ( x, f (x) )\tf ( pair(x, x) ) as Hinst\nexact Hinst\nqed";
    "choose f Hf from union\nchoose pair Hpair from pairing\ntheorem specialize_function_source : forall y, y = y\nintro y\nrefl\nqed\ntheorem specialize_hidden_function : forall x, pair(x, f(x)) = pair(x, f(x))\nintro x\nspecialize specialize_function_source pair(x, f(x)) as Hinst\nexact Hinst\nqed";
    "choose f Hf from union\nchoose pair Hpair from pairing\ntheorem specialize_chosen_fact_functions : forall x z, (z in pair(pair(x, f(x)), f(x)) <-> (z = pair(x, f(x)) or z = f(x)))\nintros x z\nspecialize Hpair pair(x, f(x)) f(x) z as Hinst\nexact Hinst\nqed";
    "choose f Hf from union\ntheorem specialize_function_avoids_capture : forall y, ((forall z, forall y, z in y) -> forall u, f(y) in u)\nintros y H\nspecialize H f(y) as Hinst\nexact Hinst\nqed";
    "theorem surface_split : forall a, (a = a and a = a)\nintro a\nsplit\nrefl\nrefl\nqed";
    "theorem surface_left : forall a, (a = a or false)\nintro a\nleft\nrefl\nqed";
    "theorem surface_right : forall a, (false or a = a)\nintro a\nright\nrefl\nqed";
    "theorem surface_use : forall a, exists x, x = a\nintro a\nuse a\nrefl\nqed";
    "theorem surface_cases_conj : forall a, ((a = a and a = a) -> a = a)\nintro a\nintro H\ncases H H1 H2\nassumption\nqed";
    "theorem surface_cases_iff : forall a, ((a = a <-> a = a) -> a = a)\nintro a\nintro H\ncases H Hforward Hbackward\napply Hforward\nrefl\nqed";
    "theorem surface_cases_disj : forall a, ((a = a or a = a) -> a = a)\nintro a\nintro H\ncases H Hleft Hright\nassumption\nassumption\nqed";
    "theorem surface_apply_in : forall a, ((a = a -> a = a) -> (a = a -> a = a))\nintro a\nintro H0\nintro H\napply H0 in H as H1\nexact H1\nqed";
    "theorem surface_apply_in_forall : forall a, ((forall x, (x = a -> x = a)) -> (a = a -> a = a))\nintro a\nintro H0\nintro H\napply H0 in H as H1\nexact H1\nqed";
    "theorem surface_rewrite : forall a, forall b, forall c, (a = b -> (a = c -> a = c))\nintro a\nintro b\nintro c\nintro H\nintro Ha\nrewrite H\nrule equal_elim a b x : x = c\nexact H\nexact Ha\nqed";
    "theorem surface_rewrite_back : forall a, forall b, (a = b -> b = b)\nintro a\nintro b\nintro H\nrewrite <- H\nrefl\nqed";
    "choose f Hf from union\ntheorem rewrite_function : forall x c s, (f(x) = c -> (c in s -> f(x) in s))\nintros x c s H Hmem\nrewrite H\nexact Hmem\nqed";
    "choose f Hf from union\ntheorem rewrite_function_back : forall x c s, (f(x) = c -> (f(x) in s -> c in s))\nintros x c s H Hmem\nrewrite <- H\nexact Hmem\nqed";
    "choose f Hf from union\nchoose pair Hpair from pairing\ntheorem rewrite_nested_functions : forall x c d, (f(x) = pair(c, c) -> (pair(pair(c, c), f(pair(c, c))) in pair(pair(c, c), d) -> pair(f(x), f(f(x))) in pair(f(x), d)))\nintros x c d H Hmem\nrewrite H\nexact Hmem\nqed";
    "choose empty Hempty from empty_set\ntheorem rewrite_chosen_constant : forall c s, (empty = c -> (c in s -> empty in s))\nintros c s H Hmem\nrewrite H\nexact Hmem\nqed";
    "choose f Hf from union\ntheorem rewrite_function_avoids_capture : forall x y, (f(x) = y -> ((forall z, y in z) -> forall y, f(x) in y))\nintros x y H Hall\nrewrite H\nexact Hall\nqed";
    "choose f Hf from union\ntheorem rewrite_function_back_avoids_capture : forall x c, (f(x) = c -> ((forall z, f(x) in z) -> forall x, c in x))\nintros x c H Hall\nrewrite <- H\nexact Hall\nqed";
    "choose f Hf from union\ntheorem rewrite_function_preserves_bound_occurrence : forall x c, (f(x) = c -> ((forall x, f(x) in c) -> forall x, f(x) in c))\nintros x c H Hall\nrewrite H\nexact Hall\nqed";
    "choose f Hf from union\ntheorem rewrite_function_preserves_bound_subterm : forall x c s, (f(x) = c -> ((c in s and forall z, f(z) in s) -> (f(x) in s and forall x, f(x) in s)))\nintros x c s H Hmem\nrewrite H\nexact Hmem\nqed";
    "choose f Hf from union\nchoose rewrite_var0 Hempty from empty_set\ntheorem rewrite_function_fresh_constant : forall x c, (f(x) = c -> (c in rewrite_var0 -> f(x) in rewrite_var0))\nintros x c H Hmem\nrewrite H\nexact Hmem\nqed";
    "theorem surface_cases_ex : ((exists x, x = x) -> exists y, y = y)\nintro H\ncases H x Hx\nuse x\nexact Hx\nqed";
    "alias is_empty x := forall y, not (y in x)\nalias empty_alias x := is_empty x\ntheorem alias_identity : forall a, (empty_alias a -> is_empty a)\nintro a\nintro H\nexact H\nqed";
    "alias has_equal x := exists y, y = x\ntheorem alias_avoids_capture : forall y, (has_equal y -> exists z, z = y)\nintro y\nintro H\nexact H\nqed";
    "alias relates x y := x = y\ntheorem simultaneous_arguments : forall x, forall y, (relates y x -> y = x)\nintro x\nintro y\nintro H\nexact H\nqed";
    "choose empty Hempty from empty_set\nalias empty_has_no_members := forall x, not (x in empty)\ntheorem alias_chosen_constant : empty_has_no_members\nput Hempty\nexact Hempty\nqed";
    "choose empty Hempty from empty_set\nalias is_chosen_empty x := x = empty\nalias chosen_empty_reflexive := is_chosen_empty empty\ntheorem alias_nested_chosen_constant : chosen_empty_reflexive\nrefl\nqed";
    "choose empty Hempty from empty_set\nalias has_empty_equal x := exists y, (y = x and y = empty)\ntheorem alias_constant_avoids_capture : forall y, (has_empty_equal y -> exists z, (z = y and z = empty))\nintros y H\nexact H\nqed";
    "choose empty Hempty from empty_set\nchoose pair Hpair from pairing\nalias contains_empty_pair x := x in pair(empty, empty)\ntheorem alias_constant_in_function : forall x, (contains_empty_pair x <-> (x = empty or x = empty))\nspecialize Hpair empty empty as H\nexact H\nqed";
    "choose empty Hempty from empty_set\ntheorem before_constant_alias : empty = empty\nrefl\nqed\nalias empty_has_no_members := forall x, not (x in empty)\ntheorem alias_previous_chosen_constant : empty_has_no_members\nput Hempty\nexact Hempty\nqed";
    "theorem obtain_local : ((exists x, x = x) -> exists y, y = y)\nintro H\nobtain x Hx from H\nuse x\nexact Hx\nqed";
    "theorem obtain_specialized : forall a, forall b, exists p, forall x, (x in p <-> (x = a or x = b))\nintro a\nintro b\nobtain p Hp from pairing a b\nuse p\nexact Hp\nqed";
    "alias is_empty x := forall y, not (y in x)\nchoose empty Hempty from empty_set\ntheorem choose_empty : is_empty empty\nput Hempty\nexact Hempty\nqed";
    "alias is_empty x := forall y, not (y in x)\nchoose empty Hempty from empty_set\ntheorem choose_resolution : is_empty empty\nput Hempty\nresolution\nqed";
    "choose empty Hempty from empty_set\nchoose pair_empty Hpair from pairing empty empty\ntheorem choose_pair : forall x, (x in pair_empty <-> (x = empty or x = empty))\nput Hpair\nexact Hpair\nqed";
    "choose pair Hpair from pairing\ntheorem choose_function_pair : forall a, forall b, forall x, (x in pair(a, b) <-> (x = a or x = b))\nput Hpair\nexact Hpair\nqed";
    "choose pair Hpair from pairing\ntheorem choose_function_use : forall a, exists p, p = pair(a, a)\nintro a\nuse pair(a, a)\nrefl\nqed";
    "choose pair Hpair from pairing\ntheorem choose_function_specialize : forall a, forall b, forall x, (x in pair(a,b) <-> (x = a or x = b))\nintro a\nintro b\nput Hpair\nspecialize Hpair a b as Hab\nexact Hab\nqed";
    "(* A nested (* comment. *) is ignored. *) theorem commented : forall x, x = x\nintro (* binder name *) x\nrefl # legacy line comment\nqed";
    "theorem rule_identity : forall x, x = x\nrule all_intro x\nrule equal_refl\nqed";
    "theorem rule_default_all_intro : forall x, x = x\nrule all_intro\nrule equal_refl\nqed";
    "theorem rule_cut : forall x, x = x\nrule cut H : forall x, x = x\nrule all_intro x\nrule equal_refl\nrule hypothesis H\nqed";
    "theorem rule_equal_elim : forall s, forall t, (s = t -> (s in s -> s in t))\nrule all_intro s\nrule all_intro t\nrule impl_intro Heq\nrule impl_intro Hmem\nrule equal_elim s t x : s in x\nrule hypothesis Heq\nrule hypothesis Hmem\nqed";
    "choose f Hf from union\nchoose pair Hpair from pairing\ntheorem rule_equal_elim_functions : forall x c s, (f(x) = pair(c, c) -> (f(x) in s -> pair(c, c) in s))\nintros x c s Heq Hmem\nrule equal_elim f(x) pair(c, c) z : z in s\nexact Heq\nexact Hmem\nqed";
    "theorem rule_all_elim : forall a, ((forall x, x = x) -> a = a)\nrule all_intro a\nrule impl_intro H\nrule all_elim a x : x = x\nrule hypothesis H\nqed";
    "theorem rule_axiom : exists e, forall x, not (x in e)\nrule axiom\nqed";
    "theorem rule_impl_elim : forall a, forall b, ((a = a -> b = b) -> (a = a -> b = b))\nrule all_intro a\nrule all_intro b\nrule impl_intro Himp\nrule impl_intro Ha\nrule impl_elim : a = a\nrule hypothesis Himp\nrule hypothesis Ha\nqed";
    "theorem rule_conjunction : forall a, forall b, ((a = a and b = b) -> (b = b and a = a))\nrule all_intro a\nrule all_intro b\nrule impl_intro H\nrule conj_intro\nrule conj_elim_r : a = a\nrule hypothesis H\nrule conj_elim_l : b = b\nrule hypothesis H\nqed";
    "theorem rule_disjunction : forall a, forall b, ((a = a or b = b) -> (a = a or b = b))\nrule all_intro a\nrule all_intro b\nrule impl_intro H\nrule disj_elim HA HB : a = a ; b = b\nrule hypothesis H\nrule disj_intro_l\nrule hypothesis HA\nrule disj_intro_r\nrule hypothesis HB\nqed";
    "theorem rule_ex_elim : (exists x, x = x) -> exists y, y = y\nrule impl_intro H\nrule ex_elim x Hx : x = x\nrule hypothesis H\nrule ex_intro x\nrule equal_refl\nqed";
    "theorem rule_falsum : forall a, (false -> a = a)\nrule all_intro a\nrule impl_intro H\nrule falsum_elim\nrule hypothesis H\nqed";
    "theorem rule_separation_axiom : forall a, exists b, forall x, (x in b <-> (x in a and not (x in x)))\nrule all_intro a\nrule axiom separation a x : not (x in x)\nqed";
    "theorem rule_replacement_axiom : forall a, ((forall x, exists y, (y = x and forall z, (z = x -> z = y))) -> exists b, forall y, (y in b <-> exists x, (x in a and y = x)))\nrule all_intro a\nrule axiom replacement a x y : y = x\nqed";
    "theorem first_after_qed : forall x, x = x\nintro x\nrefl\nqed\ntheorem second_after_qed : forall y, y = y\nintro y\nrefl\nqed";
    "theorem proof_then_declaration : forall x, x = x\nintro x\nrefl\nqed\nchoose empty Hempty from empty_set\ntheorem declaration_after_qed : forall x, not (x in empty)\nput Hempty\nexact Hempty\nqed";
    "theorem proved_exists_pair : forall a, forall b, exists p, forall x, (x in p <-> (x = a or x = b))\nintro a\nintro b\nspecialize pairing a b as H\nobtain p Hp from H\nuse p\nexact Hp\nqed\nchoose pair_from_theorem Hpair from proved_exists_pair\ntheorem choose_function_from_theorem : forall a, forall b, forall x, (x in pair_from_theorem(a,b) <-> (x = a or x = b))\nput Hpair\nexact Hpair\nqed";
    "theorem put_source : forall x, x = x\nintro x\nrefl\nqed\ntheorem put_use : forall a, a = a\nintro a\nput put_source\nresolution\nqed";
    "theorem hidden_specialize_source : forall x, x = x\nintro x\nrefl\nqed\ntheorem hidden_specialize_target : forall a, a = a\nintro a\nspecialize hidden_specialize_source a as H\nexact H\nqed";
    "theorem hidden_apply_source : forall x, (x = x -> x = x)\nintro x\nintro H\nexact H\nqed\ntheorem hidden_apply_target : forall a, a = a\nintro a\napply hidden_apply_source\nrefl\nqed";
    "theorem hidden_apply_in_source : forall x, (x = x -> x = x)\nintro x\nintro H\nexact H\nqed\ntheorem hidden_apply_in_target : forall a, (a = a -> a = a)\nintro a\nintro H\napply hidden_apply_in_source in H as H1\nexact H1\nqed";
    "choose empty empty_is_empty from empty_set\nchoose pair Hpair from pairing\ntheorem exists_ordpair : forall x, forall y, exists p, forall z, (z in p) <-> (z = x or z = pair(x, y))\nintros x y\nspecialize pairing x pair(x,y) as H\napply H\nqed\nchoose ordpair Hordpair from exists_ordpair\ntheorem exists_singleton : forall x, exists p, forall y, (y in p) <-> (y = x)\nintro x\nspecialize pairing x x as H\nput Hordpair\nresolution\nqed";
  ]

let rejected script =
  try
    ignore (Proof_session.check_script (terminate_lines script));
    false
  with Proof_session.Proof_error _ -> true

let run_directional_apply_tests () =
  let assert_formula actual expected message =
    if not (Syntax.alpha_equal actual (Parser.parse_formula expected)) then
      failwith message
  in
  let assert_replayed script =
    let state = Proof_session.check_script (terminate_lines script) in
    match Proof_session.certificate_rules state with
    | Some (_ :: _) -> ()
    | _ -> failwith "Directional apply did not produce a replayed certificate"
  in
  let assert_transition prefix tactic expected_target expected_context finish =
    let script = prefix ^ "\n" ^ tactic in
    let state, has_qed =
      Proof_session.analyze_script (terminate_lines script)
    in
    if has_qed then failwith "Directional apply unexpectedly finalized a proof";
    begin match Proof_session.goals state with
    | [{ target; context; _ }] ->
        assert_formula target expected_target
          ("Directional apply produced an unexpected goal after " ^ tactic);
        if List.length context <> List.length expected_context then
          failwith ("Directional apply changed the context size after " ^ tactic);
        List.iter
          (fun (name, expected) ->
             match List.assoc_opt name context with
             | Some actual ->
                 assert_formula actual expected
                   ("Directional apply changed hypothesis " ^ name)
             | None ->
                 failwith ("Directional apply lost hypothesis " ^ name))
          expected_context
    | _ -> failwith "Directional apply did not leave one transformed goal"
    end;
    assert_replayed (script ^ "\n" ^ finish ^ "\nqed")
  in
  let equivalence = "a in b <-> b in a" in
  let forward_prefix =
    "theorem directional_apply_forward : forall a b, ((a in b <-> b in a) -> (a in b -> b in a))\nintros a b H Ha"
  in
  let backward_prefix =
    "theorem directional_apply_backward : forall a b, ((a in b <-> b in a) -> (b in a -> a in b))\nintros a b H Hb"
  in
  assert_transition forward_prefix "apply -> H" "a in b"
    ["H", equivalence; "Ha", "a in b"] "exact Ha";
  assert_transition backward_prefix "apply <- H" "b in a"
    ["H", equivalence; "Hb", "b in a"] "exact Hb";
  assert_transition forward_prefix "apply -> H in Ha as Hb" "b in a"
    ["H", equivalence; "Ha", "a in b"; "Hb", "b in a"] "exact Hb";
  assert_transition backward_prefix "apply <- H in Hb as Ha" "a in b"
    ["H", equivalence; "Hb", "b in a"; "Ha", "a in b"] "exact Ha";
  let implication_prefix =
    "theorem directional_apply_implication_side : forall a b, (((a in b -> b in a) <-> a = a) -> ((a in b -> b in a) -> a = a))\nintros a b H H'"
  in
  let implication_context =
    ["H", "(a in b -> b in a) <-> a = a";
     "H'", "a in b -> b in a"]
  in
  assert_transition implication_prefix "apply -> H" "a in b -> b in a"
    implication_context "exact H'";
  assert_transition implication_prefix "apply -> H in H' as H''" "a = a"
    (implication_context @ ["H''", "a = a"]) "exact H''";
  let implication_conclusion_prefix =
    "theorem directional_apply_implication_conclusion : forall a b, (((a in b -> b in a) <-> a = a) -> (a = a -> (a in b -> b in a)))\nintros a b H H'"
  in
  let implication_conclusion_context =
    ["H", "(a in b -> b in a) <-> a = a"; "H'", "a = a"]
  in
  assert_transition implication_conclusion_prefix "apply <- H" "a = a"
    implication_conclusion_context "exact H'";
  assert_transition implication_conclusion_prefix "apply <- H in H' as H''"
    "a in b -> b in a"
    (implication_conclusion_context @ ["H''", "a in b -> b in a"])
    "exact H''";
  let negation_prefix =
    "theorem directional_apply_negation_side : forall a b, ((a = a <-> not (a in b)) -> (not (a in b) -> a = a))\nintros a b H H'"
  in
  let negation_context =
    ["H", "a = a <-> not (a in b)"; "H'", "not (a in b)"]
  in
  assert_transition negation_prefix "apply <- H" "not (a in b)"
    negation_context "exact H'";
  assert_transition negation_prefix "apply <- H in H' as H''" "a = a"
    (negation_context @ ["H''", "a = a"]) "exact H''";
  let negation_conclusion_prefix =
    "theorem directional_apply_negation_conclusion : forall a b, ((a = a <-> not (a in b)) -> (a = a -> not (a in b)))\nintros a b H H'"
  in
  let negation_conclusion_context =
    ["H", "a = a <-> not (a in b)"; "H'", "a = a"]
  in
  assert_transition negation_conclusion_prefix "apply -> H" "a = a"
    negation_conclusion_context "exact H'";
  assert_transition negation_conclusion_prefix "apply -> H in H' as H''"
    "not (a in b)"
    (negation_conclusion_context @ ["H''", "not (a in b)"])
    "exact H''";
  let quantified_equivalence = "forall x, (x in a <-> x in b)" in
  let quantified_forward_prefix =
    "theorem directional_apply_forall_forward : forall a b c, ((forall x, (x in a <-> x in b)) -> (c in a -> c in b))\nintros a b c H Ha"
  in
  let quantified_backward_prefix =
    "theorem directional_apply_forall_backward : forall a b c, ((forall x, (x in a <-> x in b)) -> (c in b -> c in a))\nintros a b c H Hb"
  in
  assert_transition quantified_forward_prefix "apply -> H" "c in a"
    ["H", quantified_equivalence; "Ha", "c in a"] "exact Ha";
  assert_transition quantified_backward_prefix "apply <- H" "c in b"
    ["H", quantified_equivalence; "Hb", "c in b"] "exact Hb";
  assert_transition quantified_forward_prefix "apply -> H in Ha as Hb" "c in b"
    ["H", quantified_equivalence; "Ha", "c in a"; "Hb", "c in b"] "exact Hb";
  assert_transition quantified_backward_prefix "apply <- H in Hb as Ha" "c in a"
    ["H", quantified_equivalence; "Hb", "c in b"; "Ha", "c in a"] "exact Ha";
  let hidden_source =
    "theorem directional_apply_source : forall x, (x = x <-> x = x)\nintro x\nsplit\nintro H\nexact H\nintro H\nexact H\nqed\n"
  in
  assert_transition
    (hidden_source ^ "theorem directional_apply_hidden_goal : forall a, a = a\nintro a")
    "apply -> directional_apply_source" "a = a" [] "refl";
  assert_transition
    (hidden_source ^ "theorem directional_apply_hidden_hypothesis : forall a, (a = a -> a = a)\nintros a Ha")
    "apply <- directional_apply_source in Ha as Hb" "a = a"
    ["Ha", "a = a"; "Hb", "a = a"] "exact Hb";
  let chosen_prefix =
    "choose pair Hpair from pairing\ntheorem directional_apply_chosen : forall a b c, ((c = a or c = b) -> c in pair(a, b))\nintros a b c Hmem"
  in
  assert_transition chosen_prefix "apply <- Hpair" "c = a or c = b"
    ["Hmem", "c = a or c = b"] "exact Hmem";
  assert_transition chosen_prefix "apply <- Hpair in Hmem as Hpairmem"
    "c in pair(a, b)"
    ["Hmem", "c = a or c = b"; "Hpairmem", "c in pair(a, b)"]
    "exact Hpairmem";
  let assert_rejected script message =
    let rejected =
      try
        ignore (Proof_session.analyze_script (terminate_lines script));
        false
      with Proof_session.Proof_error _ -> true
    in
    if not rejected then failwith message
  in
  List.iter
    (fun (script, message) -> assert_rejected script message)
    [
      (backward_prefix ^ "\napply -> H",
       "Directional apply accepted the wrong direction for a goal");
      (forward_prefix ^ "\napply <- H",
       "Reverse directional apply accepted the wrong goal");
      (forward_prefix ^ "\napply <- H in Ha as Hb",
       "Directional apply accepted the wrong source hypothesis");
      (backward_prefix ^ "\napply -> H in Hb as Ha",
       "Forward directional apply accepted the wrong source hypothesis");
      (forward_prefix ^ "\napply -> H in Ha as Ha",
       "Directional apply accepted a duplicate output hypothesis");
      (forward_prefix ^ "\napply -> H in Hmissing as Hb",
       "Directional apply accepted a missing source hypothesis");
      (forward_prefix ^ "\napply -> Hmissing",
       "Directional apply accepted a missing equivalence");
      (forward_prefix ^ "\napply -> Ha",
       "Directional apply accepted a non-equivalence fact");
      (forward_prefix ^ "\napply <- Ha in Ha as Hb",
       "Directional apply in accepted a non-equivalence fact");
      ("theorem directional_apply_implication : forall a b, ((a in b -> b in a) -> (a in b -> b in a))\nintros a b H Ha\napply -> H",
       "Directional apply accepted an implication as an equivalence");
      ("theorem directional_apply_unresolved_goal : forall a, ((forall x, (x = x <-> a = a)) -> a = a)\nintros a H\napply -> H",
       "Directional apply guessed an unconstrained universal instantiation");
      ("theorem directional_apply_unresolved_source : forall a, ((forall x, (a = a <-> x = x)) -> (a = a -> a = a))\nintros a H Ha\napply -> H in Ha as Hb",
       "Directional apply in guessed an unconstrained universal instantiation");
      ("theorem directional_apply_unresolved_reverse : forall a, ((forall x, (x = x <-> a = a)) -> (a = a -> a = a))\nintros a H Ha\napply <- H in Ha as Hb",
       "Reverse directional apply in guessed an unconstrained instantiation");
    ];
  Printf.printf "Directional apply tests passed (20 replay cases, 13 rejection cases).\n%!"

let run () =
  Input_test.run ();
  Definition_test.run ();
  if Syntax.fresh_name "x" Syntax.StringSet.empty <> "x0"
     || Syntax.fresh_name "x"
          (Syntax.StringSet.of_list ["x0"; "x1"]) <> "x2"
  then
    failwith "Fresh names did not use numeric suffixes";
  List.iter
    (fun script ->
       let state =
         Proof_session.check_script (terminate_lines script)
       in
       let theorem = Proof_session.theorem state in
       let printed = Syntax.formula_to_string theorem in
       if not
            (Syntax.alpha_equal theorem (Parser.parse_formula printed))
       then
         failwith
           ("Pretty-printed theorem did not round-trip: " ^ printed);
       begin match Proof_session.certificate_rules state with
       | Some (_ :: _) -> ()
       | Some [] -> failwith "A completed proof produced an empty certificate"
       | None -> failwith "A completed proof was not finalized by replay"
       end)
    valid_scripts;
  run_directional_apply_tests ();
  let multiline_specialize_script =
    "choose f Hf from union.
     choose pair Hpair from pairing.
     theorem specialize_multiline : forall x, ((forall a b, a = b) -> pair(x, f(x)) = f(pair(x, x))).
     intros x H.
     specialize H
       pair( x,
             f(x) )
       f( pair(x, x) )
       as Hinst."
  in
  let multiline_specialized, _ =
    Proof_session.analyze_script multiline_specialize_script
  in
  begin match Proof_session.goals multiline_specialized with
  | [{ context; _ }] ->
      begin match List.assoc_opt "Hinst" context, List.assoc_opt "H" context with
      | Some specialized, Some original
        when Syntax.alpha_equal specialized
               (Parser.parse_formula "pair(x, f(x)) = f(pair(x, x))")
          && Syntax.alpha_equal original
               (Parser.parse_formula "forall a b, a = b") -> ()
      | _ ->
          failwith
            "Multiline function specialization changed the source or produced the wrong fact"
      end
  | _ -> failwith "Function specialization did not preserve the current goal"
  end;
  ignore
    (Proof_session.check_script
       (multiline_specialize_script ^ "\nexact Hinst.\nqed."));
  let assert_rewrite_goal script expected =
    let state, _ =
      Proof_session.analyze_script (terminate_lines script)
    in
    match Proof_session.goals state with
    | [{ target; _ }]
      when Syntax.alpha_equal target (Parser.parse_formula expected) -> ()
    | [{ target; _ }] ->
        failwith
          ("Unexpected rewritten goal: " ^ Syntax.formula_to_string target ^
           " (expected " ^ expected ^ ")")
    | _ -> failwith "rewrite did not preserve a single transformed goal"
  in
  List.iter
    (fun (script, expected) -> assert_rewrite_goal script expected)
    [
      ("choose f Hf from union\ntheorem rewrite_goal : forall x c s, (f(x) = c -> (c in s -> f(x) in s))\nintros x c s H Hmem\nrewrite H",
       "c in s");
      ("choose f Hf from union\ntheorem rewrite_back_goal : forall x c s, (f(x) = c -> (f(x) in s -> c in s))\nintros x c s H Hmem\nrewrite <- H",
       "f(x) in s");
      ("choose f Hf from union\nchoose pair Hpair from pairing\ntheorem rewrite_nested_goal : forall x c d, (f(x) = pair(c, c) -> (pair(pair(c, c), f(pair(c, c))) in pair(pair(c, c), d) -> pair(f(x), f(f(x))) in pair(f(x), d)))\nintros x c d H Hmem\nrewrite H",
       "pair(pair(c, c), f(pair(c, c))) in pair(pair(c, c), d)");
      ("choose empty Hempty from empty_set\ntheorem rewrite_constant_goal : forall c s, (empty = c -> (c in s -> empty in s))\nintros c s H Hmem\nrewrite H",
       "c in s");
      ("choose f Hf from union\ntheorem rewrite_capture_goal : forall x y, (f(x) = y -> ((forall z, y in z) -> forall y, f(x) in y))\nintros x y H Hall\nrewrite H",
       "forall z, y in z");
      ("choose f Hf from union\ntheorem rewrite_back_capture_goal : forall x c, (f(x) = c -> ((forall z, f(x) in z) -> forall x, c in x))\nintros x c H Hall\nrewrite <- H",
       "forall z, f(x) in z");
      ("choose f Hf from union\ntheorem rewrite_bound_goal : forall x c, (f(x) = c -> ((forall x, f(x) in c) -> forall x, f(x) in c))\nintros x c H Hall\nrewrite H",
       "forall z, f(z) in c");
      ("choose f Hf from union\ntheorem rewrite_bound_subterm_goal : forall x c s, (f(x) = c -> ((c in s and forall z, f(z) in s) -> (f(x) in s and forall x, f(x) in s)))\nintros x c s H Hmem\nrewrite H",
       "c in s and forall z, f(z) in s");
      ("choose f Hf from union\nchoose rewrite_var0 Hempty from empty_set\ntheorem rewrite_fresh_constant_goal : forall x c, (f(x) = c -> (c in rewrite_var0 -> f(x) in rewrite_var0))\nintros x c H Hmem\nrewrite H",
       "c in rewrite_var0");
    ];
  let fresh_rewrite_variable_state =
    Proof_session.check_script
      (terminate_lines
         "choose f Hf from union\ntheorem rewrite_fresh_variable : forall rewrite_var0 x c s, (f(x) = c -> (c in s -> f(x) in s))\nintros rewrite_var0 x c s H Hmem\nrewrite H\nexact Hmem\nqed")
  in
  begin match Proof_session.certificate_rules fresh_rewrite_variable_state with
  | Some rules
    when not (List.exists (fun rule -> contains rule "∀rewrite_var0,") rules) ->
      ()
  | _ ->
      failwith "rewrite reused an introduced variable for its predicate binder"
  end;
  let fresh_rewrite_constant_state =
    Proof_session.check_script
      (terminate_lines
         "choose f Hf from union\nchoose rewrite_var0 Hempty from empty_set\ntheorem rewrite_fresh_unused_constant : forall x c s, (f(x) = c -> (c in s -> f(x) in s))\nintros x c s H Hmem\nrewrite H\nexact Hmem\nqed")
  in
  begin match Proof_session.certificate_rules fresh_rewrite_constant_state with
  | Some rules
    when not (List.exists (fun rule -> contains rule "∀rewrite_var0,") rules) ->
      ()
  | _ ->
      failwith "rewrite reused a declared constant for its predicate binder"
  end;
  let hidden_source_state, _ =
    Proof_session.analyze_script
      (terminate_lines
         "theorem hidden_source : forall x, x = x
intro x
refl
qed
theorem hidden_target : forall a, a = a
intro a")
  in
  begin match Proof_session.goals hidden_source_state with
  | [{ variables = ["a"]; context = [];
       target = Syntax.Eq (Syntax.Name "a", Syntax.Name "a") }] -> ()
  | _ -> failwith "A previous theorem was exposed in the proof context"
  end;
  let choose_hidden_state, _ =
    Proof_session.analyze_script
      (terminate_lines
         "alias is_empty x := forall y, not (y in x)
choose empty Hempty from empty_set
theorem choose_hidden : is_empty empty")
  in
  begin match Proof_session.goals choose_hidden_state with
  | [{ context = []; _ }] -> ()
  | _ -> failwith "A choose fact was exposed in the proof context"
  end;
  if not
       (rejected
          (terminate_lines
             "alias is_empty x := forall y, not (y in x)
choose empty Hempty from empty_set
theorem choose_without_put : is_empty empty
exact Hempty
qed"))
  then
    failwith "A choose fact was used without put";
  if not
       (rejected
          (terminate_lines
             "alias is_empty x := forall y, not (y in x)
choose empty Hempty from empty_set
theorem choose_resolution_without_put : is_empty empty
resolution
qed"))
  then
    failwith "Resolution used a choose fact without put";
  let put_state, _ =
    Proof_session.analyze_script
      (terminate_lines
         "theorem put_source : forall x, x = x
intro x
refl
qed
theorem put_target : forall a, a = a
intro a
put put_source")
  in
  begin match Proof_session.goals put_state with
  | [{ context = [("put_source", Syntax.Forall (_, _))]; _ }] -> ()
  | _ -> failwith "put did not expose the selected theorem in the context"
  end;
  if not
       (rejected
          (terminate_lines
             "theorem hidden_source : forall x, x = x
intro x
refl
qed
theorem hidden_target : forall a, a = a
intro a
resolution
qed"))
  then
    failwith "Resolution used a previous theorem without put";
  if not
       (rejected
          (terminate_lines
             "theorem hidden_source : forall x, x = x
intro x
refl
qed
theorem hidden_rule_target : forall x, x = x
rule hypothesis hidden_source
qed"))
  then
    failwith "A hidden theorem was accepted by rule hypothesis";
  if not
       (rejected
          (terminate_lines
             "theorem put_missing : forall x, x = x
put unknown_theorem
qed"))
  then
    failwith "put accepted an unknown theorem";
  if not
       (rejected
          (terminate_lines
             "theorem put_source : forall x, x = x
intro x
refl
qed
theorem put_duplicate : forall x, x = x
put put_source
put put_source
qed"))
  then
    failwith "put accepted a duplicate theorem";
  let forall_certificate =
    Proof_session.check_script
      (terminate_lines
         "theorem forall_certificate : forall a, ((forall x, x = x) -> (not (a = a) -> a = a))
intros a Hall Hnot
resolution
qed")
  in
  begin match Proof_session.certificate_rules forall_certificate with
  | Some rules when List.exists (fun rule -> contains rule "all_elim") rules -> ()
  | _ -> failwith "Universal resolution did not emit an all_elim step"
  end;
  let constant_state =
    match
      Zfcert_kernel.start_with_constants ["empty"]
        (Zfcert_kernel.NEqual
           (Zfcert_kernel.NName "empty", Zfcert_kernel.NName "empty"))
    with
    | Ok state -> state
    | Error _ -> failwith "The extracted kernel rejected a declared constant"
  in
  let constant_state =
    match
      Zfcert_kernel.rule_step ~axioms:[] Zfcert_kernel.NREqualRefl
        constant_state
    with
    | Ok state -> state
    | Error _ -> failwith "A constant was not stable under equality reflexivity"
  in
  if not (Zfcert_kernel.solved constant_state) then
    failwith "The constant equality proof left an unresolved goal";
  begin match Zfcert_kernel.finalize constant_state with
  | Ok _ -> ()
  | Error _ ->
      failwith "The constant environment was not retained during replay"
  end;
  let commented_formula =
    Parser.parse_formula
      "forall x, (* comments are whitespace *) x = x"
  in
  if not
       (Syntax.alpha_equal commented_formula
          (Syntax.Forall ("x", Syntax.Eq (Syntax.Name "x", Syntax.Name "x"))))
  then
    failwith "A block comment changed the parsed formula";
  if not
       (Syntax.alpha_equal
          (Parser.parse_formula "forall x y z, x = z")
          (Parser.parse_formula "forall x, forall y, forall z, x = z"))
  then
    failwith "Multiple universally quantified variables were parsed incorrectly";
  if not
       (Syntax.alpha_equal
          (Parser.parse_formula "exists x y z, x = z")
          (Parser.parse_formula "exists x, exists y, exists z, x = z"))
  then
    failwith "Multiple existentially quantified variables were parsed incorrectly";
  let check_formula_printing source expected =
    let formula = Parser.parse_formula source in
    let printed = Syntax.formula_to_string formula in
    if printed <> expected then
      failwith
        ("Unexpected formula rendering: " ^ printed ^
         " (expected " ^ expected ^ ")");
    if not (Syntax.alpha_equal formula (Parser.parse_formula printed)) then
      failwith "Rendered formula did not preserve its parse tree"
  in
  check_formula_printing
    "(forall x, P) -> Q"
    "(∀x, P) → Q";
  check_formula_printing
    "P and Q and R"
    "(P ∧ Q) ∧ R";
  check_formula_printing
    "P and (Q and R)"
    "P ∧ (Q ∧ R)";
  check_formula_printing
    "P and Q -> R"
    "P ∧ Q → R";
  check_formula_printing
    "P -> Q and R"
    "P → Q ∧ R";
  check_formula_printing
    "P -> Q -> R"
    "P → Q → R";
  check_formula_printing
    "P <-> Q <-> R"
    "P ↔ Q ↔ R";
  ignore
    (Proof_session.check_script
       "(* A multiline comment may contain periods.
           It may also contain a nested (* comment *).
        *)
        theorem multiline_comment : forall x, x = x.
        intro x.
        refl.
        qed.");
  let primitive_state =
    Proof_session.check_script
      (terminate_lines
         "theorem primitive_certificate : forall x, x = x
          intro x
          refl
          qed")
  in
  let primitive_certificate =
    Proof_session.certificate_rules primitive_state
  in
  begin match primitive_certificate with
  | Some ["all_intro x"; "equal_refl"] -> ()
  | _ ->
      failwith
        "Surface tactics were not recorded as their primitive rule sequence"
  end;
  let certificate_json = Api_json.success primitive_state in
  if not
       (contains certificate_json
          {|"certificate":["all_intro x","equal_refl"]|})
  then
    failwith "The checked primitive rule certificate was not exposed by the API";
  let choose_state =
    Proof_session.check_script
       "alias is_empty x := forall y, not (y in x).
       choose empty Hempty from empty_set.
       theorem choose_certificate : is_empty empty.
       put Hempty.
       exact Hempty.
       qed."
  in
  begin match Proof_session.certificate_rules choose_state with
  | Some ["hypothesis Hempty"] -> ()
  | _ ->
      failwith
        "The theorem certificate did not use the declared global fact"
  end;
  if Proof_session.global_constants choose_state <> ["empty"] then
    failwith "choose did not add its witness to the global constants";
  begin match Proof_session.global_facts choose_state with
  | [("Hempty", Syntax.Forall (_, Syntax.Not (Syntax.Mem (_, Syntax.Name "empty"))))] -> ()
  | _ -> failwith "choose did not add its instantiated global fact"
  end;
  let aliases_only, _ =
    Proof_session.analyze_script
      "alias is_empty x := forall y, not (y in x)."
  in
  let aliases_json = Api_json.step aliases_only ~has_qed:false in
  if not
       (contains aliases_json
          {|"aliasesOnly":true,"aliases":[{"name":"is_empty"|})
  then
    failwith "Proposition aliases were not exposed under the alias API";
  let choices_only, choices_have_qed =
    Proof_session.analyze_script
      "alias is_empty x := forall y, not (y in x).
       choose empty Hempty from empty_set."
  in
  let choices_json = Api_json.step choices_only ~has_qed:choices_have_qed in
  if choices_have_qed
     || Proof_session.theorem_name choices_only <> ""
     || Proof_session.step_count choices_only <> 1
     || Proof_session.global_constants choices_only <> ["empty"]
     || not (contains choices_json {|"aliasesOnly":true|})
     || not (contains choices_json {|"constants":["empty"]|})
     || not (contains choices_json {|"facts":[{"name":"Hempty"|})
     || not (contains choices_json {|"steps":1|})
  then
    failwith "A script prefix ending with choose was rejected or misreported";
  let interactive, has_qed =
    Proof_session.analyze_script
      (terminate_lines
         "theorem interactive : forall x, x = x\nintro x")
  in
  begin
    match has_qed, Proof_session.goals interactive with
    | false, [{ variables = ["x"]; context = [];
                target = Syntax.Eq (Syntax.Name "x", Syntax.Name "x") }] -> ()
    | _ ->
        failwith
          "Interactive analysis did not preserve the named current goal"
  end;
  let interactive_json = Api_json.step interactive ~has_qed:false in
  if not (contains interactive_json {|"variables":["x"]|}) then
    failwith "The proof-state JSON did not expose introduced variables";
  let union_specialized, _ =
    Proof_session.analyze_script
      (terminate_lines
         "choose pair Hpair from pairing
theorem union_specialized : forall x, forall y, exists u, forall z, (z in u <-> (z in x or z in y))
intro x
intro y
specialize union pair(x,y) as H")
  in
  begin match Proof_session.goals union_specialized with
  | [{ context; _ }] ->
      begin match List.assoc_opt "H" context with
      | Some (Syntax.Exists _) -> ()
      | _ -> failwith "Union specialization did not produce a named existential fact"
      end
  | _ -> failwith "Union specialization did not preserve the current goal"
  end;
  let named_context, _ =
    Proof_session.analyze_script
      (terminate_lines
         "theorem named_context : forall a, (a = a -> a = a)
intro a
intro H")
  in
  begin
    match Proof_session.goals named_context with
    | [{ variables = ["a"];
         context = [("H", Syntax.Eq (Syntax.Name "a", Syntax.Name "a"))];
         target = Syntax.Eq (Syntax.Name "a", Syntax.Name "a") }] -> ()
    | _ ->
        failwith
          "The extracted proof state did not preserve variable and hypothesis names"
  end;
  if not
       (rejected
          "theorem bad : forall x, forall y, x = y\nintro x\nintro y\nrefl\nqed")
  then
    failwith "The kernel accepted an invalid equality proof";
  if not
       (rejected
          "theorem bad_intro_name : forall x, x = x\nintro x y\nqed")
  then
    failwith "intro accepted multiple identifiers as one name";
  if not
       (rejected
          "theorem bad_intro_tab_name : forall x, x = x\nintro x\ty\nqed")
  then
    failwith "intro accepted a whitespace-containing identifier";
  if not
       (rejected
          "theorem ambiguous_apply : forall c, ((forall x, (x = x -> c = c)) -> c = c)\nintro c\nintro H\napply H\nqed")
  then
    failwith "apply guessed an unconstrained universal instantiation";
  if not
       (rejected
          "alias foo := forall x, x = x\ntheorem bad_alias_fact : foo\nexact foo\nqed")
  then
    failwith "A proposition alias was accepted as a proof";
  if not
       (rejected
          "choose empty Hempty from empty_set\nalias invalid_constant_alias := empty = missing")
  then
    failwith "An alias accepted an undeclared free variable beside a chosen constant";
  if not
       (rejected
          "choose empty Hempty from empty_set\nalias forward_constant_alias := empty = later\nchoose later Hlater from empty_set")
  then
    failwith "An alias accepted a constant before its choose declaration";
  if not
       (rejected
          "choose empty Hempty from empty_set\nalias empty_has_no_members := forall x, not (x in empty)\nalias captured_constant empty := empty_has_no_members")
  then
    failwith "An alias parameter was allowed to capture a declared constant";
  if not
       (rejected
          "Definition old := forall x, x = x\ntheorem old_definition : forall x, x = x\nintro x\nrefl\nqed")
  then
    failwith "The removed Definition keyword was accepted";
  if not
       (rejected
          "theorem obtain_nonexistential : forall x, (x = x -> x = x)\nintro x\nintro H\nobtain y Hy from H")
  then
    failwith "obtain accepted a non-existential fact";
  if not
       (rejected
          "theorem duplicate_cut : ((forall x, x = x) -> forall x, x = x)
rule impl_intro H
rule cut H : forall x, x = x")
  then
    failwith
      "The extracted rule layer accepted a duplicate cut hypothesis name";
  if not
       (rejected
          "theorem wrong_rule_shape : forall x, x = x
rule impl_intro H")
  then
    failwith
      "The extracted rule layer accepted a rule with the wrong goal shape";
  if not
       (rejected
          "choose empty Hempty from empty_set
choose empty Hempty2 from empty_set")
  then
    failwith "choose accepted a duplicate global constant";
  if not
       (rejected
          "choose empty Hempty from empty_set
choose empty2 Hempty from empty_set")
  then
    failwith "choose accepted a duplicate global fact name";
  if not
       (rejected
          "choose empty Hempty from empty_set
choose impossible Himpossible from Hempty")
  then
    failwith "choose accepted a non-existential global fact";
  if not
       (rejected "choose bad Hbad from extensionality")
  then
    failwith "choose accepted a source without a universal-existential shape";
  if not
       (rejected "Skolem pair Hpair from pairing")
  then
    failwith "The removed Skolem keyword was accepted";
  begin
    try
      ignore
        (Proof_session.check_script
           (terminate_lines
              "theorem bad_application : forall x, x = pair x x\nqed"));
      failwith "The parser accepted a whitespace function application"
    with
    | Proof_session.Proof_error (_, message) ->
        if not (contains message "Function applications use f(a, b), not f a b")
        then failwith "The function-application parser error was not informative"
  end;
  List.iter
    (fun (input, suggestion) ->
       try
         ignore (Parser.parse_formula input);
         failwith "The parser accepted a whitespace function before a relation"
       with
       | Parser.Parse_error (_, message) ->
           if not (contains message "Function applications require parentheses")
              || not (contains message suggestion)
           then failwith
             ("The parser did not suggest parentheses for: " ^ input))
    [
      ("zero in s and (forall x, x in s -> succ x in s)", "succ(x)");
      ("succ x = y", "succ(x)");
      ("succ x != y", "succ(x)");
      ("pair x y in s", "pair(x, y)");
    ];
  List.iter
    (fun input -> ignore (Parser.parse_formula input))
    ["P x"; "(P x)"; "P x -> Q x"; "succ(x) in s"];
  if not
       (rejected
          "choose empty Hempty from empty_set
theorem shadows_constant : forall empty, empty = empty
intro empty
refl
qed")
  then
    failwith "A theorem binder was allowed to shadow a global constant";
  if not
       (rejected
          "(* This comment never closes.
theorem hidden : forall x, x = x")
  then
    failwith "An unterminated block comment was accepted";
  if not
       (rejected
          "*) theorem unexpected_comment_end : forall x, x = x")
  then
    failwith "An unmatched block comment terminator was accepted";
  let missing_period_rejected =
    try
      ignore
        (Proof_session.analyze_script
           "theorem missing_period : forall x, x = x");
      false
    with Proof_session.Proof_error _ -> true
  in
  if not missing_period_rejected then
    failwith "A statement without a final period was accepted";
  let old_quantifier_syntax_rejected =
    try
      ignore
        (Proof_session.analyze_script
           "theorem old_quantifier : forall x. x = x.
            rule all_intro x.
            rule equal_refl.
            qed.");
      false
    with Proof_session.Proof_error _ -> true
  in
  if not old_quantifier_syntax_rejected then
    failwith "The old quantifier period syntax was accepted";
  ignore
    (Proof_session.check_script
       "theorem multiline :
          forall x,
            x = x.
        rule
          all_intro x.
        rule equal_refl.
        qed.");
  begin
    match Proof_session.find_axiom "choice" with
    | Some { parsed = Some _; _ } -> ()
    | _ -> failwith "The choice axiom did not parse"
  end;
  Printf.printf
    "All %d kernel tests passed (plus 20 rejection tests).\n%!"
    (List.length valid_scripts)
