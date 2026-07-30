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
    "theorem empty : exists e, forall x, not (x in e)\nexact empty_set\nqed";
    "theorem ext : forall a, forall b, ((forall z, (z in a <-> z in b)) -> a = b)\nintro a\nintro b\nintro H\napply extensionality\nexact H\nqed";
    "theorem ext_specialized : forall a, forall b, ((forall z, (z in a <-> z in b)) -> a = b)\nintro a\nintro b\nintro H\nspecialize extensionality a b as E\napply E\nexact H\nqed";
    "theorem sep : forall a, exists b, forall x, (x in b <-> (x in a and not (x in x)))\nintro a\nseparation S a x : not (x in x)\nexact S\nqed";
    "theorem rep : forall a, ((forall x, exists y, (y = x and forall z, (z = x -> z = y))) -> exists b, forall y, (y in b <-> exists x, (x in a and y = x)))\nintro a\nreplacement R a x y : y = x\nexact R\nqed";
    "theorem universal_contradiction : forall a, forall b, ((forall x, not (x in b)) -> (a in b -> b in a))\nintro a\nintro b\nintro H\nintro Ha\nspecialize H a as Hna\ncontradiction\nqed";
    "theorem surface_split : forall a, (a = a and a = a)\nintro a\nsplit\nrefl\nrefl\nqed";
    "theorem surface_left : forall a, (a = a or false)\nintro a\nleft\nrefl\nqed";
    "theorem surface_right : forall a, (false or a = a)\nintro a\nright\nrefl\nqed";
    "theorem surface_use : forall a, exists x, x = a\nintro a\nuse a\nrefl\nqed";
    "theorem surface_cases_conj : forall a, ((a = a and a = a) -> a = a)\nintro a\nintro H\ncases H H1 H2\nassumption\nqed";
    "theorem surface_cases_iff : forall a, ((a = a <-> a = a) -> a = a)\nintro a\nintro H\ncases H Hforward Hbackward\napply Hforward\nrefl\nqed";
    "theorem surface_cases_ex : ((exists x, x = x) -> exists y, y = y)\nintro H\ncases H x Hx\nuse x\nexact Hx\nqed";
    "Definition is_empty x := forall y, not (y in x)\nDefinition empty_alias x := is_empty x\ntheorem definition_identity : forall a, (empty_alias a -> is_empty a)\nintro a\nintro H\nexact H\nqed";
    "Definition has_equal x := exists y, y = x\ntheorem definition_avoids_capture : forall y, (has_equal y -> exists z, z = y)\nintro y\nintro H\nexact H\nqed";
    "Definition relates x y := x = y\ntheorem simultaneous_arguments : forall x, forall y, (relates y x -> y = x)\nintro x\nintro y\nintro H\nexact H\nqed";
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
  ]

let rejected script =
  try
    ignore (Proof_session.check_script (terminate_lines script));
    false
  with Proof_session.Proof_error _ -> true

let run () =
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
  let interactive, has_qed =
    Proof_session.analyze_script
      (terminate_lines
         "theorem interactive : forall x, x = x\nintro x")
  in
  begin
    match has_qed, Proof_session.goals interactive with
    | false, [{ context = []; target = Syntax.Eq ("x", "x") }] -> ()
    | _ ->
        failwith
          "Interactive analysis did not preserve the named current goal"
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
    | [{ context = [("H", Syntax.Eq ("a", "a"))];
         target = Syntax.Eq ("a", "a") }] -> ()
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
          "Definition foo := forall x, x = x\ntheorem bad_definition_fact : foo\nexact foo\nqed")
  then
    failwith "A proposition definition was accepted as a proof";
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
    "All %d kernel tests passed (plus 6 rejection tests).\n%!"
    (List.length valid_scripts)
