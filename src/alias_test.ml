let checked name expected script =
  let state = Proof_session.check_script script in
  if Proof_session.theorem_name state <> name then
    failwith ("Alias test returned the wrong theorem: " ^ name);
  if not
       (Syntax.alpha_equal (Proof_session.theorem state)
          (Parser.parse_formula expected))
  then
    failwith
      ("Alias expansion changed the statement of " ^ name ^ ": "
       ^ Syntax.formula_to_string (Proof_session.theorem state));
  begin match Proof_session.certificate_rules state with
  | Some (_ :: _) -> ()
  | _ -> failwith ("Alias proof was not certified: " ^ name)
  end

let expect_error ?line script =
  match Proof_session.analyze_script script with
  | _ -> failwith ("An invalid alias script was accepted: " ^ script)
  | exception Proof_session.Proof_error (actual_line, message) ->
      Option.iter
        (fun expected ->
          if expected <> actual_line then
            failwith
              (Printf.sprintf "Alias error line: expected %d, got %d (%s)"
                 expected actual_line message))
        line

let check_syntax () =
  let open Syntax in
  let parsed = Parser.parse_formula "subset R prod(X, pair(Y, empty()))" in
  let expected = Named ("subset",
    [Name "R";
     App ("prod", [Name "X"; App ("pair", [Name "Y"; App ("empty", [])])])])
  in
  if parsed <> expected then
    failwith "Alias arguments were not parsed as structured terms";
  List.iter
    (fun text ->
      let formula = Parser.parse_formula text in
      let printed = formula_to_string formula in
      if Parser.parse_formula printed <> formula then
        failwith ("Alias formula did not roundtrip: " ^ printed))
    [ "subset R prod(X, pair(Y, empty()))";
      "forall x, (same pair(x, y) empty() -> not same x pair(y, x))";
      "(same pair(a, b) c and same a b) or no_arguments" ];
  let quantified = Parser.parse_formula
    "forall x, relation pair(x, y) pair(z, empty())" in
  if not (StringSet.equal (free_vars quantified) (StringSet.of_list ["y"; "z"]))
  then failwith "Alias free variables omitted variables inside function terms";
  if not
       (StringSet.equal (all_vars quantified) (StringSet.of_list ["x"; "y"; "z"]))
  then failwith "Alias all variables omitted nested term or bound variables";
  let renamed = rename_bound "x" "u"
    (Parser.parse_formula "relation pair(x, y) pair(z, x)") in
  if renamed <> Parser.parse_formula "relation pair(u, y) pair(z, u)" then
    failwith "Renaming did not descend into alias argument terms";
  let substituted = subst "x" (Parser.parse_term "pair(y, y0)")
    (Parser.parse_formula "forall y, relation pair(x, y) x") in
  let expected = Parser.parse_formula
    "forall z, relation pair(pair(y, y0), z) pair(y, y0)" in
  if not (alpha_equal substituted expected)
     || not (StringSet.equal (free_vars substituted)
               (StringSet.of_list ["y"; "y0"]))
  then failwith "Substitution into alias terms did not avoid variable capture";
  if subst "x" (Parser.parse_term "pair(y, y)") quantified <> quantified then
    failwith "Substitution changed a bound alias argument variable";
  if not (alpha_equal quantified
      (Parser.parse_formula "forall u, relation pair(u, y) pair(z, empty())"))
     || alpha_equal quantified
          (Parser.parse_formula "forall u, relation pair(y, u) pair(z, empty())")
     || alpha_equal quantified
          (Parser.parse_formula "forall u, relation other(u, y) pair(z, empty())")
  then failwith "Alpha equivalence did not compare structured alias terms"

let run () =
  check_syntax ();
  let pair = "choose pair Hpair from pairing.\n" in
  checked "chosen_term_in_alias"
    "forall a b z, (z in pair(a,b) <-> (z = a or z = b))"
    (pair ^
     "alias member_of x A := x in A.\n\
      alias in_pair x a b := member_of x pair(a,b).\n\
      theorem chosen_term_in_alias : forall a b z,\n\
        (in_pair z a b <-> (z = a or z = b)).\n\
      intros a b z.\n\
      specialize Hpair a b z as H.\n\
      exact H.\n\
      qed.");
  checked "nested_definition_alias_argument"
    "forall a, pair(pair(a,a),pair(a,a)) = pair(pair(a,a),pair(a,a))"
    (pair ^
     "definition singleton(x) := pair(x,x).\n\
      alias same x y := x = y.\n\
      alias nested x := same singleton(singleton(x)) pair(singleton(x),singleton(x)).\n\
      theorem nested_definition_alias_argument : forall a, nested a.\n\
      intro a.\n\
      refl.\n\
      qed.");
  checked "simultaneous_alias_terms"
    "forall x y, (pair(y,y) = pair(x,x) -> pair(y,y) = pair(x,x))"
    (pair ^
     "alias same x y := x = y.\n\
      alias reverse x y := same y x.\n\
      theorem simultaneous_alias_terms : forall x y,\n\
        (reverse pair(x,x) pair(y,y) -> pair(y,y) = pair(x,x)).\n\
      intros x y H.\n\
      exact H.\n\
      qed.");
  checked "alias_term_capture"
    "forall y y0, ((forall z, z = pair(y,pair(y0,y))) -> forall z, z = pair(y,pair(y0,y)))"
    (pair ^
     "alias all_equal x := forall y, y = x.\n\
      theorem alias_term_capture : forall y y0,\n\
        (all_equal pair(y,pair(y0,y)) -> forall z, z = pair(y,pair(y0,y))).\n\
      intros y y0 H.\n\
      exact H.\n\
      qed.");
  checked "alias_exists_term_capture"
    "forall y y0, exists z, z = pair(y,pair(y0,y))"
    (pair ^
     "alias has_equal x := exists y, y = x.\n\
      theorem alias_exists_term_capture : forall y y0, has_equal pair(y,pair(y0,y)).\n\
      intros y y0.\n\
      use pair(y,pair(y0,y)).\n\
      refl.\n\
      qed.");
  checked "alias_capture_reserves_function_names"
    "forall y, ((forall z, z = y0(y,y)) -> forall z, z = y0(y,y))"
    "choose y0 Hpair from pairing.\n\
     alias all_equal x := forall y, y = x.\n\
     theorem alias_capture_reserves_function_names : forall y,\n\
       (all_equal y0(y,y) -> forall z, z = y0(y,y)).\n\
     intros y H.\n\
     exact H.\n\
     qed.";
  let same_terms = pair ^ "alias same x y := x = y.\n" in
  checked "alias_rule_cut_terms"
    "forall x, pair(x,x) = pair(x,x)"
    (same_terms ^
     "theorem alias_rule_cut_terms : forall x, pair(x,x) = pair(x,x).\n\
      intro x.\n\
      rule cut H : same pair(x,x) pair(x,x).\n\
      refl.\n\
      exact H.\n\
      qed.");
  checked "alias_separation_terms"
    "forall a, exists b, forall x, (x in b <-> (x in a and pair(x,x) = pair(a,a)))"
    (same_terms ^
     "theorem alias_separation_terms : forall a, exists b, forall x,\n\
        (x in b <-> (x in a and pair(x,x) = pair(a,a))).\n\
      intro a.\n\
      separation S a x : same pair(x,x) pair(a,a).\n\
      exact S.\n\
      qed.");
  checked "alias_replacement_terms"
    "forall a, ((forall x, exists y, (y = pair(x,x) and forall z, (z = pair(x,x) -> z = y))) -> exists b, forall y, (y in b <-> exists x, (x in a and y = pair(x,x))))"
    (same_terms ^
     "theorem alias_replacement_terms : forall a,\n\
        ((forall x, exists y,\n\
          (y = pair(x,x) and forall z, (z = pair(x,x) -> z = y))) ->\n\
          exists b, forall y, (y in b <-> exists x, (x in a and y = pair(x,x)))).\n\
      intro a.\n\
      replacement R a x y : same y pair(x,x).\n\
      exact R.\n\
      qed.");
  let shadowing =
    "choose empty Hempty from empty_set.\n" ^ pair ^
    "definition zero := empty.\n\
     alias all_equal x := forall zero, zero = x.\n"
  in
  checked "alias_caller_definition_scope"
    "((forall z, z = empty) -> forall z, z = empty)"
    (shadowing ^
     "theorem alias_caller_definition_scope :\n\
        (all_equal zero -> forall z, z = empty).\n\
      intro H.\n\
      exact H.\n\
      qed.");
  checked "alias_caller_variable_scope"
    "forall zero, ((forall z, z = pair(zero,zero)) -> forall z, z = pair(zero,zero))"
    (shadowing ^
     "theorem alias_caller_variable_scope : forall zero,\n\
        (all_equal pair(zero,zero) -> forall z, z = pair(zero,zero)).\n\
      intros zero H.\n\
      exact H.\n\
      qed.");
  checked "nullary_alias_argument"
    "forall z, not (z in empty())"
    "choose empty Hempty from empty_set.\n\
     alias is_empty x := forall z, not (z in x).\n\
     alias chosen_empty := is_empty empty().\n\
     theorem nullary_alias_argument : chosen_empty.\n\
     exact Hempty.\n\
     qed.";
  let same = pair ^ "alias same x := x = x.\n" in
  List.iter (fun statement -> expect_error ~line:3 (same ^ statement))
    [ "theorem bad : forall x, same missing(x).";
      "theorem bad : forall x, same pair(x,,x).";
      "theorem bad : forall x, same pair(x,x.";
      "alias bad x := same pair(x,z)." ];
  let ignored = pair ^ "alias ignore x y := x = x.\n" in
  List.iter (fun statement -> expect_error ~line:3 (ignored ^ statement))
    [ "theorem bad : forall x, ignore x missing(x).";
      "alias bad x := ignore x missing(x).";
      "alias bad x := ignore x pair(x,z)." ];
  let definition =
    "definition identity(x) := x.\n\
     alias ignore x y := x = x.\n"
  in
  List.iter (fun statement -> expect_error ~line:3 (definition ^ statement))
    [ "theorem bad : forall x, ignore x identity(x,x).";
      "theorem bad : forall x, ignore x identity().";
      "alias bad x := ignore x identity(x,x).";
      "alias bad x := ignore x identity()." ];
  Printf.printf "Alias term argument tests passed.\n%!"
