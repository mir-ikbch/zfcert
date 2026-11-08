let contains text fragment =
  let rec search index =
    index + String.length fragment <= String.length text
    && (String.sub text index (String.length fragment) = fragment
        || search (index + 1))
  in
  search 0

let checked ?filename ?load_input name expected script =
  let state = Proof_session.check_script ?filename ?load_input script in
  if Proof_session.theorem_name state <> name then
    failwith ("Definition test returned the wrong theorem: " ^ name);
  if not
       (Syntax.alpha_equal (Proof_session.theorem state)
          (Parser.parse_formula expected))
  then
    failwith
      ("Definition expansion changed the statement of " ^ name ^ ": "
       ^ Syntax.formula_to_string (Proof_session.theorem state));
  begin match Proof_session.certificate_rules state with
  | Some (_ :: _) -> ()
  | _ -> failwith ("Definition proof was not certified: " ^ name)
  end;
  state

let expect_error ?line ?fragment script =
  match Proof_session.analyze_script script with
  | _ -> failwith ("An invalid definition script was accepted: " ^ script)
  | exception Proof_session.Proof_error (actual_line, message) ->
      Option.iter
        (fun expected ->
          if expected <> actual_line then
            failwith
              (Printf.sprintf
                 "Definition error line: expected %d, got %d (%s)"
                 expected actual_line message))
        line;
      Option.iter
        (fun expected ->
          if not (contains message expected) then
            failwith ("Definition error missing " ^ expected ^ ": " ^ message))
        fragment

let run () =
  let pair = "choose pair Hpair from pairing.\n" in
  let singleton =
    pair ^ "definition singleton(x) := pair(x, x).\n"
  in
  let nested = checked "nested_definition"
    "forall x z, (z in pair(x, pair(x, x)) <-> (z = x or z = pair(x, x)))"
    (pair ^
     "definition flip(x, y) := pair(y, x).\n\
      definition diagonal(x) := flip(x, x).\n\
      theorem nested_definition : forall x z,\n\
        (z in flip(diagonal(x), x) <-> (z = x or z = diagonal(x))).\n\
      intros x z.\n\
      specialize Hpair x diagonal(x) z as H.\n\
      exact H.\n\
      qed.")
  in
  begin match Proof_session.definitions nested with
  | [{ definition_name = "flip"; parameters = ["x"; "y"];
       body = Syntax.App ("pair", [Syntax.Name "y"; Syntax.Name "x"]) };
     { definition_name = "diagonal"; parameters = ["x"];
       body = Syntax.App ("pair", [Syntax.Name "x"; Syntax.Name "x"]) }] -> ()
  | _ -> failwith "Definition bodies were not expanded in source order"
  end;
  ignore (checked "simultaneous_definition"
    "forall x y z, (z in pair(x, y) <-> (z = x or z = y))"
    (pair ^
     "definition flip(x,y) := pair(y,x).\n\
      theorem simultaneous_definition : forall x y z,\n\
        (z in flip(y,x) <-> (z = x or z = y)).\n\
      intros x y z.\n\
      specialize Hpair x y z as H.\n\
      exact H.\n\
      qed."));
  ignore (checked "definition_in_alias"
    "forall x y, (x in pair(y,y) <-> (x = y or x = y))"
    (singleton ^
     "alias in_singleton x y := x in singleton(y).\n\
      theorem definition_in_alias : forall x y,\n\
        (in_singleton x y <-> (x = y or x = y)).\n\
      intros x y.\n\
      specialize Hpair y y x as H.\n\
      exact H.\n\
      qed."));
  let zero =
    "choose empty Hempty from empty_set.\n\
     definition zero := empty.\n\
     definition nullary() := zero().\n"
  in
  let nullary = checked "nullary_definition"
    "(forall x, not (x in empty)) and (forall y, not (y in empty))"
    (zero ^
     "theorem nullary_definition :\n\
        (forall x, not (x in zero)) and (forall y, not (y in nullary())).\n\
      split.\n\
      exact Hempty.\n\
      exact Hempty.\n\
      qed.")
  in
  ignore (checked "definition_shadowing"
    "forall zero, exists x, x = zero"
    (zero ^
     "definition keep(zero) := zero.\n\
      theorem definition_shadowing : forall zero, exists x, x = keep(zero).\n\
      intro zero.\n\
      use zero.\n\
      refl.\n\
      qed."));
  ignore (checked "alias_parameter_shadowing"
    "forall zero, zero = zero"
    (zero ^
     "alias same zero := zero = zero.\n\
      theorem alias_parameter_shadowing : forall zero, same zero.\n\
      intro zero.\n\
      refl.\n\
      qed."));
  ignore (checked "definition_witness"
    "forall x, exists y, y = pair(x, x)"
    (singleton ^
     "theorem definition_witness : forall x, exists y, y = singleton(x).\n\
      intro x.\n\
      use singleton(x).\n\
      refl.\n\
      qed."));
  ignore (checked "definition_choose"
    "forall z, (z in selected <-> (z = pair(empty, empty) or z = empty))"
    ("choose empty Hempty from empty_set.\n" ^ singleton ^
     "choose selected Hselected from pairing singleton(empty) empty.\n\
      theorem definition_choose : forall z,\n\
        (z in selected <-> (z = singleton(empty) or z = empty)).\n\
      exact Hselected.\n\
      qed."));
  ignore (checked "definition_separation"
    "forall a, exists b, forall x, (x in b <-> (x in pair(a,a) and x = a))"
    (singleton ^
     "definition identity(x) := x.\n\
      theorem definition_separation : forall a, exists b, forall x,\n\
        (x in b <-> (x in singleton(a) and identity(x) = a)).\n\
      intro a.\n\
      separation S singleton(a) x : identity(x) = a.\n\
      exact S.\n\
      qed."));
  ignore (checked "definition_rule_witness"
    "forall x, exists y, y = pair(x,x)"
    (singleton ^
     "theorem definition_rule_witness : forall x, exists y, y = singleton(x).\n\
      intro x.\n\
      rule ex_intro singleton(x).\n\
      refl.\n\
      qed."));
  ignore (checked "definition_rule_formula"
    "forall a, (a = pair(a,a) -> a = pair(a,a))"
    (singleton ^
     "theorem definition_rule_formula : forall a, (a = singleton(a) -> a = singleton(a)).\n\
      intros a H.\n\
      rule cut C : a = singleton(a).\n\
      exact H.\n\
      exact C.\n\
      qed."));
  ignore (checked "definition_rule_binder_shadowing"
    "forall a, ((forall zero, zero = a) -> a = a)"
    (zero ^
     "theorem definition_rule_binder_shadowing :\n\
        forall a, ((forall zero, zero = a) -> a = a).\n\
      intros a H.\n\
      rule all_elim a zero : zero = a.\n\
      exact H.\n\
      qed."));
  ignore (checked "definition_replacement_fact_name"
    "forall a, ((forall x, exists y, (y = empty and forall z, (z = empty -> z = y))) -> exists b, forall y, (y in b <-> exists x, (x in a and y = empty)))"
    (zero ^
     "theorem definition_replacement_fact_name :\n\
        forall a, ((forall x, exists y,\n\
          (y = zero and forall z, (z = zero -> z = y))) ->\n\
          exists b, forall y, (y in b <-> exists x, (x in a and y = zero))).\n\
      intro a.\n\
      replacement zero a x y : y = zero.\n\
      exact zero.\n\
      qed."));
  ignore (checked "definition_after_theorem"
    "forall x z, (z in pair(pair(x,x),pair(x,x)) <-> (z = pair(x,x) or z = pair(x,x)))"
    (singleton ^
     "theorem earlier_definition : forall x, singleton(x) = pair(x,x).\n\
      intro x.\n\
      refl.\n\
      qed.\n\
      definition composed(x) := singleton(singleton(x)).\n\
      theorem definition_after_theorem : forall x z,\n\
        (z in composed(x) <-> (z = singleton(x) or z = singleton(x))).\n\
      intros x z.\n\
      specialize Hpair singleton(x) singleton(x) z as H.\n\
      exact H.\n\
      qed."));
  let definitions_only, has_qed =
    Proof_session.analyze_script "definition identity(x) := x."
  in
  if has_qed || Proof_session.theorem_name definitions_only <> "" then
    failwith "Definitions without a theorem did not preserve declaration state";
  let metadata =
    {|"definitions":[{"name":"identity","parameters":["x"],"term":"x"}]|}
  in
  if not (contains (Api_json.step definitions_only ~has_qed:false) metadata)
     || not (contains (Api_json.success definitions_only) metadata)
  then failwith "Definition metadata were not exposed for declaration-only scripts";
  if not
       (contains (Api_json.success nullary)
          {|"definitions":[{"name":"zero","parameters":[],"term":"empty"},{"name":"nullary","parameters":[],"term":"empty"}]|})
  then failwith "Definition metadata were not exposed after a certified proof";
  let imported =
    pair ^ "definition imported(x,y) := pair(y,x)."
  in
  let load_input ~from:_ requested =
    match requested with
    | "definitions.zfp" -> ("/virtual/definitions.zfp", imported)
    | _ -> failwith "Unexpected definition test input filename"
  in
  ignore (checked ~filename:"/virtual/main.zfp" ~load_input "imported_definition"
    "forall x y z, (z in pair(y,x) <-> (z = y or z = x))"
    "input \"definitions.zfp\".\n\
     theorem imported_definition : forall x y z,\n\
       (z in imported(x,y) <-> (z = y or z = x)).\n\
     intros x y z.\n\
     specialize Hpair y x z as H.\n\
     exact H.\n\
     qed.");
  List.iter (fun script -> expect_error script)
    [ "definition self(x) := self(x).";
      "definition early(x) := later(x). definition later(x) := x.";
      "definition unknown(x) := missing(x).";
      "definition free(x) := y.";
      "definition first(x,y) := x. definition erased_free(x) := first(x,z).";
      "definition first(x,y) := x. definition erased_function(x) := first(x,missing(x)).";
      "definition identity(x) := x. definition first(x,y) := x. definition erased_arity(x) := first(x,identity(x,x)).";
      "definition duplicate(x,x) := x.";
      "definition same(x) := x. definition same(y) := y.";
      "choose empty Hempty from empty_set. definition empty := empty.";
      pair ^ "definition pair(x,y) := x.";
      "definition occupied(x) := x. choose occupied H from union.";
      "choose empty Hempty from empty_set. definition f(empty) := empty.";
      "definition f(x) := x. theorem bad : forall x, f(x,x) = x.";
      "definition f(x) := x. theorem bad : forall x, f() = x.";
      "definition f(x) := x. theorem bad : forall x, f = x.";
      "definition f() := missing.";
      "definition f(x) := x = x.";
      "definition f(pair(x,x)) := x.";
      "definition f(x) x.";
      "definition f(x) := ." ];
  expect_error ~line:3
    "# declaration errors keep their source line\n\n\
     definition bad(x) := missing(x).";
  Printf.printf "Term definition tests passed.\n%!"
