module Kernel = Zfcert_kernel

exception Error of string

let trim = String.trim

let words text =
  text
  |> String.split_on_char ' '
  |> List.map trim
  |> List.filter (fun word -> word <> "")

let split_first_word line =
  match String.index_opt line ' ' with
  | None -> (line, "")
  | Some index ->
      (String.sub line 0 index,
       trim
         (String.sub line (index + 1)
           (String.length line - index - 1)))

let split_formula argument =
  match String.index_opt argument ':' with
  | None -> raise (Error "This rule requires a formula after :.")
  | Some index ->
      let parameters =
        String.sub argument 0 index |> trim |> words
      in
      let formula =
        String.sub argument (index + 1)
          (String.length argument - index - 1)
        |> trim
      in
      if formula = "" then
        raise (Error "Expected a formula after :.");
      (parameters, formula)

let require_no_arguments rule_name argument =
  if trim argument <> "" then
    raise (Error ("rule " ^ rule_name ^ " takes no arguments."))

let require_one_name usage argument =
  match words argument with
  | [name] -> name
  | _ -> raise (Error usage)

let parse_kernel_term parse_formula text =
  match parse_formula (trim text ^ " = " ^ trim text) with
  | Syntax.Eq (term, _) -> Kernel_syntax.to_kernel_term term
  | _ -> raise (Error "Expected a term.")

let parse_schema parse_formula schema argument =
  let names, formula_text = split_formula argument in
  let predicate = parse_formula formula_text in
  match String.lowercase_ascii schema, names with
  | "separation", [source; element] ->
      if source = element then
        raise (Error
          "The source set and element variable must have different names.");
      Kernel.NSeparationAxiomRule
        (source, element, Kernel_syntax.to_kernel predicate)
  | "replacement", [source; input; output] ->
      if source = input || input = output || source = output then
        raise (Error
          "The source, input, and output variables must have distinct names.");
      Kernel.NReplacementAxiomRule
        (source, input, output, Kernel_syntax.to_kernel predicate)
  | "separation", _ ->
      raise (Error "Use: rule axiom separation source x : P.")
  | "replacement", _ ->
      raise (Error "Use: rule axiom replacement source x y : P.")
  | _ ->
      raise (Error
        "rule axiom accepts only separation or replacement here.")

let parse ~parse_formula argument =
  let rule_name, rule_argument = split_first_word (trim argument) in
  match String.lowercase_ascii rule_name with
  | "" -> raise (Error "Expected a rule name.")
  | "axiom" ->
      let schema, schema_argument =
        split_first_word (trim rule_argument)
      in
      if schema = "" then Kernel.NFixedAxiomRule
      else parse_schema parse_formula schema schema_argument
  | "hypothesis" ->
      let name =
        require_one_name
          "Use rule hypothesis H with a hypothesis name."
          rule_argument
      in
      Kernel.NPrimitiveRule (Kernel.NRHypothesis name)
  | "falsum_elim" ->
      require_no_arguments "falsum_elim" rule_argument;
      Kernel.NPrimitiveRule Kernel.NRFalsumElim
  | "impl_intro" ->
      let name =
        require_one_name
          "Use rule impl_intro H with a hypothesis name."
          rule_argument
      in
      Kernel.NPrimitiveRule (Kernel.NRImplIntro name)
  | "impl_elim" ->
      let parameters, formula_text = split_formula rule_argument in
      if parameters <> [] then
        raise (Error "Use: rule impl_elim : P.");
      Kernel.NPrimitiveRule
        (Kernel.NRImplElim
          (Kernel_syntax.to_kernel (parse_formula formula_text)))
  | "conj_intro" ->
      require_no_arguments "conj_intro" rule_argument;
      Kernel.NPrimitiveRule Kernel.NRConjIntro
  | "conj_elim_l" ->
      let parameters, formula_text = split_formula rule_argument in
      if parameters <> [] then
        raise (Error "Use: rule conj_elim_l : P.");
      Kernel.NPrimitiveRule
        (Kernel.NRConjElimL
          (Kernel_syntax.to_kernel (parse_formula formula_text)))
  | "conj_elim_r" ->
      let parameters, formula_text = split_formula rule_argument in
      if parameters <> [] then
        raise (Error "Use: rule conj_elim_r : P.");
      Kernel.NPrimitiveRule
        (Kernel.NRConjElimR
          (Kernel_syntax.to_kernel (parse_formula formula_text)))
  | "disj_intro_l" ->
      require_no_arguments "disj_intro_l" rule_argument;
      Kernel.NPrimitiveRule Kernel.NRDisjIntroL
  | "disj_intro_r" ->
      require_no_arguments "disj_intro_r" rule_argument;
      Kernel.NPrimitiveRule Kernel.NRDisjIntroR
  | "disj_elim" ->
      let parameters, formulas = split_formula rule_argument in
      let left_name, right_name =
        match parameters with
        | [left_name; right_name] -> (left_name, right_name)
        | _ -> raise (Error "Use: rule disj_elim HL HR : P ; Q.")
      in
      let separator =
        match String.index_opt formulas ';' with
        | Some index -> index
        | None -> raise (Error "Separate the two formulas with ;.")
      in
      let left =
        String.sub formulas 0 separator |> parse_formula
      in
      let right =
        String.sub formulas (separator + 1)
          (String.length formulas - separator - 1)
        |> parse_formula
      in
      Kernel.NPrimitiveRule
        (Kernel.NRDisjElim
          (Kernel_syntax.to_kernel left,
           Kernel_syntax.to_kernel right,
           left_name, right_name))
  | "all_intro" ->
      begin match words rule_argument with
      | [] -> Kernel.NDefaultAllIntroRule
      | [name] ->
          Kernel.NPrimitiveRule (Kernel.NRAllIntro name)
      | _ -> raise (Error "Use: rule all_intro x.")
      end
  | "all_elim" ->
      let parameters, formula_text = split_formula rule_argument in
      let term, binder =
        match parameters with
        | [term; binder] -> (term, binder)
        | _ -> raise (Error "Use: rule all_elim term x : P.")
      in
      let universal =
        Syntax.Forall (binder, parse_formula formula_text)
      in
      Kernel.NPrimitiveRule
        (Kernel.NRAllElim
          (parse_kernel_term parse_formula term,
           Kernel_syntax.to_kernel universal))
  | "ex_intro" ->
      let term =
        require_one_name
          "Use rule ex_intro term to provide a witness."
          rule_argument
      in
      Kernel.NPrimitiveRule (Kernel.NRExIntro (parse_kernel_term parse_formula term))
  | "ex_elim" ->
      let parameters, formula_text = split_formula rule_argument in
      let witness, hypothesis =
        match parameters with
        | [witness; hypothesis] -> (witness, hypothesis)
        | _ -> raise (Error "Use: rule ex_elim x H : P.")
      in
      let existential =
        Syntax.Exists (witness, parse_formula formula_text)
      in
      Kernel.NPrimitiveRule
        (Kernel.NRExElim
          (witness, hypothesis, Kernel_syntax.to_kernel existential))
  | "equal_refl" ->
      require_no_arguments "equal_refl" rule_argument;
      Kernel.NPrimitiveRule Kernel.NREqualRefl
  | "equal_elim" ->
      let parameters, formula_text = split_formula rule_argument in
      let left, right, binder =
        match parameters with
        | [left; right; binder] -> (left, right, binder)
        | _ -> raise (Error "Use: rule equal_elim s t x : P.")
      in
      let predicate =
        Syntax.Forall (binder, parse_formula formula_text)
      in
      Kernel.NPrimitiveRule
        (Kernel.NREqualElim
          (left, right, Kernel_syntax.to_kernel predicate))
  | "cut" ->
      let parameters, formula_text = split_formula rule_argument in
      let hypothesis =
        match parameters with
        | [name] -> name
        | _ -> raise (Error "Use: rule cut H : P.")
      in
      Kernel.NPrimitiveRule
        (Kernel.NRCut
          (hypothesis,
           Kernel_syntax.to_kernel (parse_formula formula_text)))
  | unknown ->
      raise (Error ("Unknown inference rule: " ^ unknown))

let description argument =
  "rule " ^ trim argument
