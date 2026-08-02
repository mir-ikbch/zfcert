type formula =
  | Bottom
  | Named of string * string list
  | Eq of term * term
  | Mem of term * term
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imp of formula * formula
  | Iff of formula * formula
  | Forall of string * formula
  | Exists of string * formula

and term =
  | Name of string
  | App of string * term list

module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

let precedence = function
  | Forall _ | Exists _ -> 0
  | Iff _ -> 1 | Imp _ -> 2 | Or _ -> 3 | And _ -> 4
  | Not _ -> 5
  | Bottom | Named _ | Eq _ | Mem _ -> 6

let rec term_to_string = function
  | Name name -> name
  | App (name, arguments) ->
      name ^ "(" ^ String.concat ", " (List.map term_to_string arguments) ^ ")"

let rec formula_to_string ?(outer = 0) formula =
  let precedence = precedence formula in
  let body =
    match formula with
    | Bottom -> "⊥"
    | Named (name, arguments) ->
        String.concat " " (name :: arguments)
    | Eq (left, right) -> term_to_string left ^ " = " ^ term_to_string right
    | Mem (left, right) -> term_to_string left ^ " ∈ " ^ term_to_string right
    | Not inner ->
        "¬" ^ formula_to_string ~outer:precedence inner
    | And (left, right) ->
        formula_to_string ~outer:precedence left
        ^ " ∧ "
        ^ formula_to_string ~outer:precedence right
    | Or (left, right) ->
        formula_to_string ~outer:precedence left
        ^ " ∨ "
        ^ formula_to_string ~outer:precedence right
    | Imp (left, right) ->
        formula_to_string ~outer:(precedence + 1) left
        ^ " → "
        ^ formula_to_string ~outer:precedence right
    | Iff (left, right) ->
        formula_to_string ~outer:(precedence + 1) left
        ^ " ↔ "
        ^ formula_to_string ~outer:precedence right
    | Forall (name, body) ->
        "∀" ^ name ^ ", " ^ formula_to_string ~outer:precedence body
    | Exists (name, body) ->
        "∃" ^ name ^ ", " ^ formula_to_string ~outer:precedence body
  in
  if precedence < outer then "(" ^ body ^ ")" else body

let rec term_free_vars = function
  | Name name -> StringSet.singleton name
  | App (_name, arguments) ->
      List.fold_left
        (fun names argument -> StringSet.union names (term_free_vars argument))
        StringSet.empty arguments

let term_all_vars = term_free_vars

let rec free_vars = function
  | Bottom -> StringSet.empty
  | Named (_, arguments) -> StringSet.of_list arguments
  | Eq (left, right) | Mem (left, right) ->
      StringSet.union (term_free_vars left) (term_free_vars right)
  | Not formula -> free_vars formula
  | And (left, right)
  | Or (left, right)
  | Imp (left, right)
  | Iff (left, right) ->
      StringSet.union (free_vars left) (free_vars right)
  | Forall (name, formula) | Exists (name, formula) ->
      StringSet.remove name (free_vars formula)

let rec all_vars = function
  | Bottom -> StringSet.empty
  | Named (_, arguments) -> StringSet.of_list arguments
  | Eq (left, right) | Mem (left, right) ->
      StringSet.union (term_all_vars left) (term_all_vars right)
  | Not formula -> all_vars formula
  | And (left, right)
  | Or (left, right)
  | Imp (left, right)
  | Iff (left, right) ->
      StringSet.union (all_vars left) (all_vars right)
  | Forall (name, formula) | Exists (name, formula) ->
      StringSet.add name (all_vars formula)

let fresh_name base used =
  let rec try_index index =
    let candidate = base ^ string_of_int index in
    if StringSet.mem candidate used then try_index (index + 1)
    else candidate
  in
  try_index 0

let rec rename_term_bound old_name new_name = function
  | Name name -> Name (if name = old_name then new_name else name)
  | App (name, arguments) ->
      App (name, List.map (rename_term_bound old_name new_name) arguments)

let rec rename_bound old_name new_name = function
  | Bottom -> Bottom
  | Named (name, arguments) -> Named (name, List.map (fun argument ->
      if argument = old_name then new_name else argument) arguments)
  | Eq (left, right) ->
      Eq (rename_term_bound old_name new_name left,
          rename_term_bound old_name new_name right)
  | Mem (left, right) ->
      Mem (rename_term_bound old_name new_name left,
           rename_term_bound old_name new_name right)
  | Not formula -> Not (rename_bound old_name new_name formula)
  | And (left, right) ->
      And
        (rename_bound old_name new_name left,
         rename_bound old_name new_name right)
  | Or (left, right) ->
      Or
        (rename_bound old_name new_name left,
         rename_bound old_name new_name right)
  | Imp (left, right) ->
      Imp
        (rename_bound old_name new_name left,
         rename_bound old_name new_name right)
  | Iff (left, right) ->
      Iff
        (rename_bound old_name new_name left,
         rename_bound old_name new_name right)
  | Forall (name, formula) when name = old_name ->
      Forall (name, formula)
  | Exists (name, formula) when name = old_name ->
      Exists (name, formula)
  | Forall (name, formula) ->
      Forall (name, rename_bound old_name new_name formula)
  | Exists (name, formula) ->
      Exists (name, rename_bound old_name new_name formula)

let rec subst_term variable replacement = function
  | Name name -> if name = variable then replacement else Name name
  | App (name, arguments) ->
      App (name, List.map (subst_term variable replacement) arguments)

let rec subst variable replacement = function
  | Bottom -> Bottom
  | Named (name, arguments) ->
      Named (name,
        List.map (fun argument -> if argument = variable then term_to_string replacement else argument)
          arguments)
  | Eq (left, right) ->
      Eq (subst_term variable replacement left,
          subst_term variable replacement right)
  | Mem (left, right) ->
      Mem (subst_term variable replacement left,
           subst_term variable replacement right)
  | Not formula -> Not (subst variable replacement formula)
  | And (left, right) ->
      And (subst variable replacement left, subst variable replacement right)
  | Or (left, right) ->
      Or (subst variable replacement left, subst variable replacement right)
  | Imp (left, right) ->
      Imp (subst variable replacement left, subst variable replacement right)
  | Iff (left, right) ->
      Iff (subst variable replacement left, subst variable replacement right)
  | Forall (name, formula) when name = variable ->
      Forall (name, formula)
  | Exists (name, formula) when name = variable ->
      Exists (name, formula)
  | Forall (name, formula)
      when StringSet.mem name (term_free_vars replacement)
           && StringSet.mem variable (free_vars formula) ->
      let fresh =
        fresh_name name
          (StringSet.union (term_free_vars replacement) (all_vars formula))
      in
      Forall
        (fresh,
         subst variable replacement (rename_bound name fresh formula))
  | Exists (name, formula)
      when StringSet.mem name (term_free_vars replacement)
           && StringSet.mem variable (free_vars formula) ->
      let fresh =
        fresh_name name
          (StringSet.union (term_free_vars replacement) (all_vars formula))
      in
      Exists
        (fresh,
         subst variable replacement (rename_bound name fresh formula))
  | Forall (name, formula) ->
      Forall (name, subst variable replacement formula)
  | Exists (name, formula) ->
      Exists (name, subst variable replacement formula)

let alpha_equal left right =
  let rec equal left_environment right_environment next left right =
    let rec term_equal left right =
      match left, right with
      | Name left, Name right ->
          begin match
            StringMap.find_opt left left_environment,
            StringMap.find_opt right right_environment
          with
          | Some left_index, Some right_index -> left_index = right_index
          | None, None -> left = right
          | _ -> false
          end
      | App (left_name, left_arguments), App (right_name, right_arguments) ->
          left_name = right_name
          && List.length left_arguments = List.length right_arguments
          && List.for_all2 term_equal left_arguments right_arguments
      | _ -> false
    in
    match left, right with
    | Bottom, Bottom -> true
    | Named (left_name, left_arguments),
      Named (right_name, right_arguments) ->
        left_name = right_name
        && List.length left_arguments = List.length right_arguments
        && List.for_all2
             (fun left right -> term_equal (Name left) (Name right))
             left_arguments right_arguments
    | Eq (left_first, left_second),
      Eq (right_first, right_second)
    | Mem (left_first, left_second),
      Mem (right_first, right_second) ->
        term_equal left_first right_first
        && term_equal left_second right_second
    | Not left, Not right ->
        equal left_environment right_environment next left right
    | And (left_first, left_second),
      And (right_first, right_second)
    | Or (left_first, left_second),
      Or (right_first, right_second)
    | Imp (left_first, left_second),
      Imp (right_first, right_second)
    | Iff (left_first, left_second),
      Iff (right_first, right_second) ->
        equal left_environment right_environment next
          left_first right_first
        && equal left_environment right_environment next
             left_second right_second
    | Forall (left_name, left_body),
      Forall (right_name, right_body)
    | Exists (left_name, left_body),
      Exists (right_name, right_body) ->
        equal
          (StringMap.add left_name next left_environment)
          (StringMap.add right_name next right_environment)
          (next + 1)
          left_body right_body
    | _ -> false
  in
  equal StringMap.empty StringMap.empty 0 left right
