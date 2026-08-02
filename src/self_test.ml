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
    "Choose pair Hpair from pairing\ntheorem resolution_forall_function : forall a, ((forall x, x = pair(a, a)) -> (not (pair(a, a) = pair(a, a)) -> pair(a, a) = pair(a, a)))\nintros a Hall Hnot\nresolution\nqed";
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
    "Choose pair Hpair from pairing\ntheorem sep_term : forall a, forall b, exists c, forall x, (x in c <-> (x in pair(a, b) and not (x in x)))\nintro a\nintro b\nseparation S pair(a, b) x : not (x in x)\nexact S\nqed";
    "theorem rep : forall a, ((forall x, exists y, (y = x and forall z, (z = x -> z = y))) -> exists b, forall y, (y in b <-> exists x, (x in a and y = x)))\nintro a\nreplacement R a x y : y = x\nexact R\nqed";
    "theorem universal_contradiction : forall a, forall b, ((forall x, not (x in b)) -> (a in b -> b in a))\nintro a\nintro b\nintro H\nintro Ha\nspecialize H a as Hna\ncontradiction\nqed";
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
    "theorem surface_cases_ex : ((exists x, x = x) -> exists y, y = y)\nintro H\ncases H x Hx\nuse x\nexact Hx\nqed";
    "alias is_empty x := forall y, not (y in x)\nalias empty_alias x := is_empty x\ntheorem alias_identity : forall a, (empty_alias a -> is_empty a)\nintro a\nintro H\nexact H\nqed";
    "alias has_equal x := exists y, y = x\ntheorem alias_avoids_capture : forall y, (has_equal y -> exists z, z = y)\nintro y\nintro H\nexact H\nqed";
    "alias relates x y := x = y\ntheorem simultaneous_arguments : forall x, forall y, (relates y x -> y = x)\nintro x\nintro y\nintro H\nexact H\nqed";
    "theorem obtain_local : ((exists x, x = x) -> exists y, y = y)\nintro H\nobtain x Hx from H\nuse x\nexact Hx\nqed";
    "theorem obtain_specialized : forall a, forall b, exists p, forall x, (x in p <-> (x = a or x = b))\nintro a\nintro b\nobtain p Hp from pairing a b\nuse p\nexact Hp\nqed";
    "alias is_empty x := forall y, not (y in x)\nChoose empty Hempty from empty_set\ntheorem choose_empty : is_empty empty\nexact Hempty\nqed";
    "Choose empty Hempty from empty_set\nChoose pair_empty Hpair from pairing empty empty\ntheorem choose_pair : forall x, (x in pair_empty <-> (x = empty or x = empty))\nexact Hpair\nqed";
    "Choose pair Hpair from pairing\ntheorem choose_function_pair : forall a, forall b, forall x, (x in pair(a, b) <-> (x = a or x = b))\nexact Hpair\nqed";
    "Choose pair Hpair from pairing\ntheorem choose_function_use : forall a, exists p, p = pair(a, a)\nintro a\nuse pair(a, a)\nrefl\nqed";
    "Choose pair Hpair from pairing\ntheorem choose_function_specialize : forall a, forall b, forall x, (x in pair(a,b) <-> (x = a or x = b))\nintro a\nintro b\nspecialize Hpair a b as Hab\nexact Hab\nqed";
    "(* A nested (* comment. *) is ignored. *) theorem commented : forall x, x = x\nintro (* binder name *) x\nrefl # legacy line comment\nqed";
    "theorem rule_identity : forall x, x = x\nrule all_intro x\nrule equal_refl\nqed";
    "theorem rule_default_all_intro : forall x, x = x\nrule all_intro\nrule equal_refl\nqed";
    "theorem rule_cut : forall x, x = x\nrule cut H : forall x, x = x\nrule all_intro x\nrule equal_refl\nrule hypothesis H\nqed";
    "theorem rule_equal_elim : forall s, forall t, (s = t -> (s in s -> s in t))\nrule all_intro s\nrule all_intro t\nrule impl_intro Heq\nrule impl_intro Hmem\nrule equal_elim s t x : s in x\nrule hypothesis Heq\nrule hypothesis Hmem\nqed";
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
    "theorem proof_then_declaration : forall x, x = x\nintro x\nrefl\nqed\nChoose empty Hempty from empty_set\ntheorem declaration_after_qed : forall x, not (x in empty)\nexact Hempty\nqed";
    "theorem proved_exists_pair : forall a, forall b, exists p, forall x, (x in p <-> (x = a or x = b))\nintro a\nintro b\nspecialize pairing a b as H\nobtain p Hp from H\nuse p\nexact Hp\nqed\nChoose pair_from_theorem Hpair from proved_exists_pair\ntheorem choose_function_from_theorem : forall a, forall b, forall x, (x in pair_from_theorem(a,b) <-> (x = a or x = b))\nexact Hpair\nqed";
  ]

let rejected script =
  try
    ignore (Proof_session.check_script (terminate_lines script));
    false
  with Proof_session.Proof_error _ -> true

let run () =
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
       Choose empty Hempty from empty_set.
       theorem choose_certificate : is_empty empty.
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
    failwith "Choose did not add its witness to the global constants";
  begin match Proof_session.global_facts choose_state with
  | [("Hempty", Syntax.Forall (_, Syntax.Not (Syntax.Mem (_, Syntax.Name "empty"))))] -> ()
  | _ -> failwith "Choose did not add its instantiated global fact"
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
       Choose empty Hempty from empty_set."
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
    failwith "A script prefix ending with Choose was rejected or misreported";
  let interactive, has_qed =
    Proof_session.analyze_script
      (terminate_lines
         "theorem interactive : forall x, x = x\nintro x")
  in
  begin
    match has_qed, Proof_session.goals interactive with
    | false, [{ context = []; target = Syntax.Eq (Syntax.Name "x", Syntax.Name "x") }] -> ()
    | _ ->
        failwith
          "Interactive analysis did not preserve the named current goal"
  end;
  let union_specialized, _ =
    Proof_session.analyze_script
      (terminate_lines
         "Choose pair Hpair from pairing
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
    | [{ context = [("H", Syntax.Eq (Syntax.Name "a", Syntax.Name "a"))];
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
          "alias foo := forall x, x = x\ntheorem bad_alias_fact : foo\nexact foo\nqed")
  then
    failwith "A proposition alias was accepted as a proof";
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
          "Choose empty Hempty from empty_set
Choose empty Hempty2 from empty_set")
  then
    failwith "Choose accepted a duplicate global constant";
  if not
       (rejected
          "Choose empty Hempty from empty_set
Choose empty2 Hempty from empty_set")
  then
    failwith "Choose accepted a duplicate global fact name";
  if not
       (rejected
          "Choose empty Hempty from empty_set
Choose impossible Himpossible from Hempty")
  then
    failwith "Choose accepted a non-existential global fact";
  if not
       (rejected "Choose bad Hbad from extensionality")
  then
    failwith "Choose accepted a source without a universal-existential shape";
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
  if not
       (rejected
          "Choose empty Hempty from empty_set
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
    "All %d kernel tests passed (plus 14 rejection tests).\n%!"
    (List.length valid_scripts)
