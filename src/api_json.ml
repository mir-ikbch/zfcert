open Proof_session

let escape text =
  let buffer = Buffer.create (String.length text + 16) in
  String.iter
    (function
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '\n' -> Buffer.add_string buffer "\\n"
      | '\r' -> Buffer.add_string buffer "\\r"
      | '\t' -> Buffer.add_string buffer "\\t"
      | character when Char.code character < 32 ->
          Buffer.add_string buffer
            (Printf.sprintf "\\u%04x" (Char.code character))
      | character -> Buffer.add_char buffer character)
    text;
  Buffer.contents buffer

let quote text = "\"" ^ escape text ^ "\""

let axiom axiom =
  Printf.sprintf
    {|{"key":%s,"title":%s,"statement":%s,"note":%s,"kernel":%s}|}
    (quote axiom.key)
    (quote axiom.title)
    (quote axiom.statement)
    (quote axiom.note)
    (if Option.is_some axiom.parsed then "true" else "false")

let axioms () =
  "[" ^ String.concat "," (List.map axiom Proof_session.axioms) ^ "]"

let definition definition =
  let parameters =
    definition.parameters
    |> List.map quote
    |> String.concat ","
  in
  Printf.sprintf
    {|{"name":%s,"parameters":[%s],"statement":%s}|}
    (quote definition.definition_name)
    parameters
    (quote (Syntax.formula_to_string definition.body))

let definitions definitions =
  "[" ^ String.concat "," (List.map definition definitions) ^ "]"

let success state =
  if theorem_name state = "" then
    Printf.sprintf
      {|{"ok":true,"definitionsOnly":true,"definitions":%s,"steps":0,"message":%s}|}
      (definitions (Proof_session.definitions state))
      (quote "Proposition definitions loaded.")
  else
    Printf.sprintf
      {|{"ok":true,"definitionsOnly":false,"theorem":%s,"statement":%s,"definitions":%s,"steps":%d,"message":%s}|}
      (quote (theorem_name state))
      (quote (Syntax.formula_to_string (theorem state)))
      (definitions (Proof_session.definitions state))
      (step_count state)
      (quote "The proof was verified by the extracted kernel.")

let context_entry (name, formula) =
  Printf.sprintf {|{"name":%s,"formula":%s}|}
    (quote name)
    (quote (Syntax.formula_to_string formula))

let goal goal =
  let context =
    List.rev goal.context
    |> List.map context_entry
    |> String.concat ","
  in
  Printf.sprintf {|{"target":%s,"context":[%s]}|}
    (quote (Syntax.formula_to_string goal.target))
    context

let step state ~has_qed =
  if theorem_name state = "" then
    Printf.sprintf
      {|{"ok":true,"definitionsOnly":true,"definitions":%s,"steps":0,"complete":true,"qed":false,"goals":[],"message":%s}|}
      (definitions (Proof_session.definitions state))
      (quote "Proposition definitions loaded. You can now write a theorem.")
  else
    let complete = is_complete state in
    let goals =
      List.map goal (Proof_session.goals state) |> String.concat ","
    in
    let message =
      if has_qed then
        "The proof is complete and was verified by the extracted kernel."
      else if complete then
        "All goals are solved. Add qed. to finish the proof."
      else
        "Enter a tactic for the current goal."
    in
    Printf.sprintf
      {|{"ok":true,"definitionsOnly":false,"theorem":%s,"statement":%s,"definitions":%s,"steps":%d,"complete":%s,"qed":%s,"goals":[%s],"message":%s}|}
      (quote (theorem_name state))
      (quote (Syntax.formula_to_string (theorem state)))
      (definitions (Proof_session.definitions state))
      (step_count state)
      (if complete then "true" else "false")
      (if has_qed then "true" else "false")
      goals
      (quote message)

let error ~line message =
  Printf.sprintf {|{"ok":false,"line":%d,"message":%s}|}
    line (quote message)
