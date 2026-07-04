type formula =
  | Bottom
  | Named of string * string list
  | Eq of string * string
  | Mem of string * string
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imp of formula * formula
  | Iff of formula * formula
  | Forall of string * formula
  | Exists of string * formula

module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

let precedence = function
  | Forall _ | Exists _ -> 0
  | Iff _ -> 1 | Imp _ -> 2 | Or _ -> 3 | And _ -> 4
  | Not _ -> 5
  | Bottom | Named _ | Eq _ | Mem _ -> 6

let rec formula_to_string ?(outer = 0) formula =
  let precedence = precedence formula in
  let body =
    match formula with
    | Bottom -> "⊥"
    | Named (name, arguments) ->
        String.concat " " (name :: arguments)
    | Eq (left, right) -> left ^ " = " ^ right
    | Mem (left, right) -> left ^ " ∈ " ^ right
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

let rec free_vars = function
  | Bottom -> StringSet.empty
  | Named (_, arguments) -> StringSet.of_list arguments
  | Eq (left, right) | Mem (left, right) ->
      StringSet.of_list [left; right]
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
      StringSet.of_list [left; right]
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
    let candidate =
      if index = 0 then base ^ "'"
      else base ^ "'" ^ string_of_int index
    in
    if StringSet.mem candidate used then try_index (index + 1)
    else candidate
  in
  try_index 0

let rec rename_bound old_name new_name = function
  | Bottom -> Bottom
  | Named (name, arguments) ->
      Named
        (name,
         List.map
           (fun argument ->
              if argument = old_name then new_name else argument)
           arguments)
  | Eq (left, right) ->
      Eq
        ((if left = old_name then new_name else left),
         (if right = old_name then new_name else right))
  | Mem (left, right) ->
      Mem
        ((if left = old_name then new_name else left),
         (if right = old_name then new_name else right))
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

let rec subst variable term = function
  | Bottom -> Bottom
  | Named (name, arguments) ->
      Named
        (name,
         List.map
           (fun argument ->
              if argument = variable then term else argument)
           arguments)
  | Eq (left, right) ->
      Eq
        ((if left = variable then term else left),
         (if right = variable then term else right))
  | Mem (left, right) ->
      Mem
        ((if left = variable then term else left),
         (if right = variable then term else right))
  | Not formula -> Not (subst variable term formula)
  | And (left, right) ->
      And (subst variable term left, subst variable term right)
  | Or (left, right) ->
      Or (subst variable term left, subst variable term right)
  | Imp (left, right) ->
      Imp (subst variable term left, subst variable term right)
  | Iff (left, right) ->
      Iff (subst variable term left, subst variable term right)
  | Forall (name, formula) when name = variable ->
      Forall (name, formula)
  | Exists (name, formula) when name = variable ->
      Exists (name, formula)
  | Forall (name, formula)
      when name = term && StringSet.mem variable (free_vars formula) ->
      let fresh =
        fresh_name name (StringSet.add term (all_vars formula))
      in
      Forall
        (fresh,
         subst variable term (rename_bound name fresh formula))
  | Exists (name, formula)
      when name = term && StringSet.mem variable (free_vars formula) ->
      let fresh =
        fresh_name name (StringSet.add term (all_vars formula))
      in
      Exists
        (fresh,
         subst variable term (rename_bound name fresh formula))
  | Forall (name, formula) ->
      Forall (name, subst variable term formula)
  | Exists (name, formula) ->
      Exists (name, subst variable term formula)

let alpha_equal left right =
  let rec equal left_environment right_environment next left right =
    let term_equal left right =
      match
        StringMap.find_opt left left_environment,
        StringMap.find_opt right right_environment
      with
      | Some left_index, Some right_index ->
          left_index = right_index
      | None, None -> left = right
      | _ -> false
    in
    match left, right with
    | Bottom, Bottom -> true
    | Named (left_name, left_arguments),
      Named (right_name, right_arguments) ->
        left_name = right_name
        && List.length left_arguments = List.length right_arguments
        && List.for_all2 term_equal left_arguments right_arguments
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
