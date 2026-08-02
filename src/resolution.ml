(* A small propositional-resolution planner.

   This module is deliberately only a planner.  It searches over clauses in
   the OCaml syntax and emits ordinary named primitive rules.  The resulting
   certificate is checked by the extracted kernel before it changes a proof
   state.

   The planner decomposes conjunctions and disjunctions.  A hypothesis whose
   outer connective is outside that fragment is deliberately kept opaque and
   treated as one propositional atom.  This lets resolution ignore unrelated
   first-order hypotheses while still using them when they happen to match a
   literal in the refutation. *)

module Kernel = Zfcert_kernel

open Syntax

type literal = bool * formula
type clause = literal list

type input = {
  source_name : string;
  source_formula : formula;
  clause : clause;
  existing : bool;
}

type node_kind =
  | Input of input
  | Resolve of node * node * literal

and node = {
  name : string;
  clause : clause;
  kind : node_kind;
}

type builder = {
  mutable used_names : StringSet.t;
  mutable steps_reverse : Kernel.certificate_step list;
}

let make_builder hypotheses target =
  let names =
    List.fold_left
      (fun names (name, formula) ->
         StringSet.add name (StringSet.union names (all_vars formula)))
      (all_vars target) hypotheses
  in
  { used_names = names; steps_reverse = [] }

let fresh builder base =
  let name = fresh_name base builder.used_names in
  builder.used_names <- StringSet.add name builder.used_names;
  name

let emit ?(axioms = []) builder rule =
  builder.steps_reverse <-
    Kernel.certificate_step ~axioms rule :: builder.steps_reverse

let finish builder = List.rev builder.steps_reverse

let kernel_formula = Kernel_syntax.to_kernel

let literal_formula (positive, atom) =
  if positive then atom else Not atom

let kernel_literal (positive, atom) =
  kernel_formula (literal_formula (positive, atom))

let compare_literal (left_positive, left_atom)
    (right_positive, right_atom) =
  let atom_order = compare left_atom right_atom in
  if atom_order <> 0 then atom_order
  else compare left_positive right_positive

let same_literal left right = compare_literal left right = 0

let complementary (left_positive, left_atom)
    (right_positive, right_atom) =
  left_positive <> right_positive && left_atom = right_atom

let clause_contains literal clause =
  List.exists (same_literal literal) clause

let normalize_clause literals =
  let rec collect result = function
    | [] -> Some (List.sort compare_literal result)
    | literal :: rest ->
        if List.exists (complementary literal) result then None
        else if clause_contains literal result then collect result rest
        else collect (literal :: result) rest
  in
  collect [] literals

let union_clause left right =
  normalize_clause (left @ right)

let clause_equal left right =
  List.length left = List.length right
  && List.for_all2 same_literal left right

let clause_formula clause =
  let rec build = function
    | [] -> Bottom
    | [literal] -> literal_formula literal
    | literal :: rest -> Or (literal_formula literal, build rest)
  in
  build clause

let rec cnf formula =
  match formula with
  | Bottom -> Ok [ [] ]
  | Eq _ | Mem _ | Named _ -> Ok [ [ (true, formula) ] ]
  | Not inner ->
      begin match inner with
      | Bottom -> Ok []
      | _ -> Ok [ [ (false, inner) ] ]
      end
  | And (left, right) ->
      begin match cnf left, cnf right with
      | Ok left_clauses, Ok right_clauses ->
          Ok (left_clauses @ right_clauses)
      | Error message, _ | _, Error message -> Error message
      end
  | Or (left, right) ->
      begin match cnf left, cnf right with
      | Ok [], _ | _, Ok [] -> Ok []
      | Ok left_clauses, Ok right_clauses ->
          let products =
            List.concat_map
              (fun left_clause ->
                 List.filter_map
                   (fun right_clause ->
                      union_clause left_clause right_clause)
                   right_clauses)
              left_clauses
          in
          Ok products
      | Error message, _ | _, Error message -> Error message
      end
  (* Quantifiers, implications, equivalences, and compound formulas under a
     negation are not expanded.  At this level the complete formula is an
     opaque propositional atom. *)
  | formula -> Ok [ [ (true, formula) ] ]

let find_clause clauses wanted =
  List.find_opt (fun clause -> clause_equal clause wanted) clauses

let find_clause_pair left_clauses right_clauses target =
  let rec search_left = function
    | [] -> None
    | left_clause :: rest ->
        begin match
          List.find_opt
            (fun right_clause ->
               match union_clause left_clause right_clause with
               | Some combined -> clause_equal combined target
               | None -> false)
            right_clauses
        with
        | Some right_clause -> Some (left_clause, right_clause)
        | None -> search_left rest
        end
  in
  search_left left_clauses

(* Derive a clause from a literal hypothesis by weakening it into a
   disjunction.  The current goal is [clause_formula target]. *)
let rec derive_from_literal builder hypothesis literal target =
  match target with
  | [] -> Error "a non-falsum literal cannot prove the empty clause"
  | [target_literal] ->
      if same_literal literal target_literal then begin
        emit builder (Kernel.NRHypothesis hypothesis);
        Ok ()
      end else
        Error "the resolution trace contained an invalid weakening"
  | head :: tail ->
      if same_literal literal head then begin
        emit builder Kernel.NRDisjIntroL;
        emit builder (Kernel.NRHypothesis hypothesis);
        Ok ()
      end else if clause_contains literal tail then begin
        emit builder Kernel.NRDisjIntroR;
        derive_from_literal builder hypothesis literal tail
      end else
        Error "the resolution trace contained an invalid weakening"

(* Derive a target clause from a hypothesis whose formula is exactly a
   (possibly nested) disjunction. *)
let rec weaken_clause builder hypothesis source target =
  match source with
  | [] ->
      emit builder Kernel.NRFalsumElim;
      emit builder (Kernel.NRHypothesis hypothesis);
      Ok ()
  | [literal] -> derive_from_literal builder hypothesis literal target
  | literal :: rest ->
      let left_name = fresh builder "resolution_literal" in
      let right_name = fresh builder "resolution_rest" in
      emit builder
        (Kernel.NRDisjElim
           (kernel_literal literal,
            kernel_formula (clause_formula rest),
            left_name, right_name));
      emit builder (Kernel.NRHypothesis hypothesis);
      begin match derive_from_literal builder left_name literal target with
      | Error message -> Error message
      | Ok () -> weaken_clause builder right_name rest target
      end

(* Derive one CNF clause from the named hypothesis [source_name].  Cuts are
   used for conjunction and disjunction subformulas, so every generated
   obligation remains an ordinary primitive-rule proof. *)
let rec derive_clause_from_hyp builder source_name source_formula target =
  match source_formula with
  | Bottom ->
      if target = [] then begin
        emit builder (Kernel.NRHypothesis source_name);
        Ok ()
      end else Error "the source falsum does not match the requested clause"
  | Eq _ | Mem _ | Named _ ->
      begin match target with
      | [literal] when literal = (true, source_formula) ->
          emit builder (Kernel.NRHypothesis source_name);
          Ok ()
      | _ -> Error "the source atom does not match the requested clause"
      end
  | Not inner ->
      begin match inner, target with
      | _, [literal] when literal = (false, inner) ->
          emit builder (Kernel.NRHypothesis source_name);
          Ok ()
      | _ -> Error "the source negation does not match the requested clause"
      end
  | And (left, right) ->
      begin match cnf left, cnf right with
      | Ok left_clauses, Ok right_clauses ->
          if Option.is_some (find_clause left_clauses target) then begin
            let part_name = fresh builder "resolution_part" in
            emit builder
              (Kernel.NRCut (part_name, kernel_formula left));
            emit builder
              (Kernel.NRConjElimL (kernel_formula right));
            emit builder (Kernel.NRHypothesis source_name);
            derive_clause_from_hyp builder part_name left target
          end else if Option.is_some (find_clause right_clauses target) then begin
            let part_name = fresh builder "resolution_part" in
            emit builder
              (Kernel.NRCut (part_name, kernel_formula right));
            emit builder
              (Kernel.NRConjElimR (kernel_formula left));
            emit builder (Kernel.NRHypothesis source_name);
            derive_clause_from_hyp builder part_name right target
          end else
            Error "the source conjunction does not contain the requested clause"
      | Error message, _ | _, Error message -> Error message
      end
  | Or (left, right) ->
      begin match cnf left, cnf right with
      | Ok left_clauses, Ok right_clauses ->
          begin match find_clause_pair left_clauses right_clauses target with
          | None -> Error "the source disjunction does not contain the requested clause"
          | Some (left_clause, right_clause) ->
              let left_name = fresh builder "resolution_left" in
              let right_name = fresh builder "resolution_right" in
              emit builder
                (Kernel.NRDisjElim
                   (kernel_formula left,
                    kernel_formula right,
                    left_name, right_name));
              emit builder (Kernel.NRHypothesis source_name);
              let left_clause_name = fresh builder "resolution_clause" in
              emit builder
                (Kernel.NRCut
                   (left_clause_name, kernel_formula (clause_formula left_clause)));
              begin match
                derive_clause_from_hyp builder left_name left left_clause
              with
              | Error message -> Error message
              | Ok () ->
                  begin match
                    weaken_clause builder left_clause_name left_clause target
                  with
                  | Error message -> Error message
                  | Ok () ->
                      let right_clause_name = fresh builder "resolution_clause" in
                      emit builder
                        (Kernel.NRCut
                           (right_clause_name,
                            kernel_formula (clause_formula right_clause)));
                      begin match
                        derive_clause_from_hyp builder right_name right right_clause
                      with
                      | Error message -> Error message
                      | Ok () ->
                          weaken_clause builder right_clause_name right_clause target
                      end
                  end
              end
          end
      | Error message, _ | _, Error message -> Error message
      end
  (* An unsupported source formula is an opaque positive atom. *)
  | formula ->
      begin match target with
      | [literal] when literal = (true, formula) ->
          emit builder (Kernel.NRHypothesis source_name);
          Ok ()
      | _ -> Error "the opaque source formula does not match the requested clause"
      end

let derive_contradiction builder first_literal first_name second_literal second_name =
  match first_literal, second_literal with
  | (true, atom), (false, other_atom)
    when atom = other_atom ->
      emit builder (Kernel.NRImplElim (kernel_formula atom));
      emit builder (Kernel.NRHypothesis second_name);
      emit builder (Kernel.NRHypothesis first_name);
      Ok ()
  | (false, atom), (true, other_atom)
    when atom = other_atom ->
      emit builder (Kernel.NRImplElim (kernel_formula atom));
      emit builder (Kernel.NRHypothesis first_name);
      emit builder (Kernel.NRHypothesis second_name);
      Ok ()
  | _ -> Error "the resolution trace contained non-complementary literals"

let rec prove_second_parent builder first_literal first_name target
    second_name second_clause second_literal_handler =
  match second_clause with
  | [] -> Error "an empty parent clause was used before the final refutation"
  | [literal] -> second_literal_handler literal second_name
  | literal :: rest ->
      let left_name = fresh builder "resolution_literal" in
      let right_name = fresh builder "resolution_rest" in
      emit builder
        (Kernel.NRDisjElim
           (kernel_literal literal,
            kernel_formula (clause_formula rest),
            left_name, right_name));
      emit builder (Kernel.NRHypothesis second_name);
      begin match second_literal_handler literal left_name with
      | Error message -> Error message
      | Ok () ->
          prove_second_parent builder first_literal first_name target
            right_name rest second_literal_handler
      end

let prove_resolution builder first_node second_node pivot target =
  let complement_pivot = (not (fst pivot), snd pivot) in
  let process_first_literal literal first_name =
    if same_literal literal pivot then begin
      let process_second_literal literal second_name =
        if same_literal literal complement_pivot then begin
          emit builder Kernel.NRFalsumElim;
          derive_contradiction builder pivot first_name literal second_name
        end else
          derive_from_literal builder second_name literal target
      in
      prove_second_parent builder pivot first_name target
        second_node.name second_node.clause process_second_literal
    end else
      derive_from_literal builder first_name literal target
  in
  let rec split_first_parent name = function
    | [] -> Error "an empty parent clause was used before the final refutation"
    | [literal] -> process_first_literal literal name
    | literal :: rest ->
        let left_name = fresh builder "resolution_literal" in
        let right_name = fresh builder "resolution_rest" in
        emit builder
          (Kernel.NRDisjElim
             (kernel_literal literal,
              kernel_formula (clause_formula rest),
              left_name, right_name));
        emit builder (Kernel.NRHypothesis name);
        begin match process_first_literal literal left_name with
        | Error message -> Error message
        | Ok () -> split_first_parent right_name rest
        end
  in
  split_first_parent first_node.name first_node.clause

let all_pairs nodes =
  let rec with_tail first = function
    | [] -> []
    | second :: rest -> (first, second) :: with_tail first rest
  in
  let rec loop = function
    | [] -> []
    | first :: rest -> with_tail first rest @ loop rest
  in
  loop nodes

let resolvents first second =
  let rec for_literals = function
    | [] -> []
    | literal :: rest ->
        let complement = (not (fst literal), snd literal) in
        let generated =
          if clause_contains complement second then
            match
              normalize_clause
                (List.filter (fun item -> not (same_literal item literal)) first
                 @ List.filter
                     (fun item -> not (same_literal item complement)) second)
            with
            | Some clause -> [ (clause, literal) ]
            | None -> []
          else []
        in
        generated @ for_literals rest
  in
  for_literals first

let saturate builder initial_nodes =
  let rec loop nodes =
    match List.find_opt (fun node -> node.clause = []) nodes with
    | Some empty -> Ok (nodes, empty)
    | None ->
        let additions =
          all_pairs nodes
          |> List.concat_map (fun (first, second) ->
               resolvents first.clause second.clause
               |> List.filter_map (fun (clause, pivot) ->
                    if List.exists (fun node -> clause_equal node.clause clause) nodes
                    then None
                    else
                      let name = fresh builder "resolution_clause" in
                      Some { name; clause; kind = Resolve (first, second, pivot) }))
        in
        let additions =
          List.fold_left
            (fun result node ->
               if List.exists (fun old -> clause_equal old.clause node.clause)
                    (nodes @ result)
               then result
               else result @ [node])
            [] additions
        in
        if additions = [] then
          Error "no propositional resolution refutation was found"
        else if List.length nodes + List.length additions > 512 then
          Error "the propositional resolution search exceeded its 512-clause limit"
        else
          loop (nodes @ additions)
  in
  loop initial_nodes

let initial_inputs hypotheses =
  let sources = hypotheses in
  let rec loop (result : input list) = function
    | [] -> Ok (List.rev result)
    | (source_name, source_formula) :: rest ->
        let clauses =
          match cnf source_formula with
          | Ok clauses -> clauses
          | Error _ -> [ [ (true, source_formula) ] ]
        in
        let result =
          List.fold_left
            (fun (result : input list) (clause : clause) ->
               if List.exists
                    (fun (input : input) ->
                       clause_equal input.clause clause)
                    result
               then result
               else
                 ({ source_name; source_formula; clause; existing = false }
                   : input)
                 :: result)
            result clauses
        in
        loop result rest
  in
  loop [] sources

let plan hypotheses target =
  let target_kernel = kernel_formula target in
  let target_is_literal =
    match target with
    | Bottom -> true
    | Eq _ | Mem _ | Named _ -> true
    | _ -> false
  in
  if not target_is_literal then
    Error
      "resolution currently requires a literal or falsum as its goal"
  else
    let refutation_formula =
      match target with
      | Bottom -> Bottom
      | _ -> Not target
    in
    match initial_inputs hypotheses with
    | Error message -> Error message
    | Ok inputs ->
        let builder = make_builder hypotheses target in
        let excluded_middle =
          if target = Bottom then None else Some (Or (target, Not target))
        in
        let excluded_middle_name =
          Option.map (fun _ -> fresh builder "resolution_em") excluded_middle
        in
        let target_name =
          Option.map (fun _ -> fresh builder "resolution_goal") excluded_middle
        in
        let negated_target_name =
          Option.map (fun _ -> fresh builder "resolution_negated") excluded_middle
        in
        let inputs =
          match excluded_middle, negated_target_name with
          | Some _, Some source_name ->
              begin match cnf refutation_formula with
              | Error _ -> inputs
              | Ok clauses ->
                  List.fold_left
                    (fun result clause ->
                       if List.exists
                            (fun (input : input) -> clause_equal input.clause clause)
                            result
                       then result
                       else
                         ({ source_name; source_formula = refutation_formula;
                            clause; existing = true } : input)
                         :: result)
                    inputs clauses
              end
          | _ -> inputs
        in
        let input_nodes =
          List.map
            (fun (input : input) ->
               { name =
                   if input.existing then input.source_name
                   else fresh builder "resolution_clause";
                 clause = input.clause;
                 kind = Input input })
            inputs
        in
        begin match saturate builder input_nodes with
        | Error message -> Error message
        | Ok (nodes, empty_node) ->
            let refutation_steps builder =
              let rec emit_input = function
                | [] -> Ok ()
                | node :: rest ->
                    begin match node.kind with
                    | Input input when input.existing -> emit_input rest
                    | Input input ->
                        emit builder
                          (Kernel.NRCut
                             (node.name, kernel_formula (clause_formula node.clause)));
                        begin match
                          derive_clause_from_hyp builder input.source_name
                            input.source_formula node.clause
                        with
                        | Error message -> Error message
                        | Ok () -> emit_input rest
                        end
                    | Resolve _ -> emit_input rest
                    end
              in
              let rec emit_derived = function
                | [] -> Ok ()
                | node :: rest ->
                    begin match node.kind with
                    | Input _ -> emit_derived rest
                    | Resolve (first, second, pivot) ->
                        emit builder
                          (Kernel.NRCut
                             (node.name, kernel_formula (clause_formula node.clause)));
                        begin match
                          prove_resolution builder first second pivot node.clause
                        with
                        | Error message -> Error message
                        | Ok () -> emit_derived rest
                        end
                    end
              in
              match emit_input nodes with
              | Error message -> Error message
              | Ok () ->
                  begin match emit_derived nodes with
                  | Error message -> Error message
                  | Ok () ->
                      emit builder Kernel.NRFalsumElim;
                      emit builder (Kernel.NRHypothesis empty_node.name);
                      Ok ()
                  end
            in
            if target = Bottom then begin
              match refutation_steps builder with
              | Error message -> Error message
              | Ok () -> Ok (finish builder)
            end else begin
              let em_name = Option.get excluded_middle_name in
              let goal_name = Option.get target_name in
              let negated_name = Option.get negated_target_name in
              emit builder
                (Kernel.NRCut
                   (em_name, kernel_formula (Or (target, Not target))));
              emit ~axioms:[Kernel.classical_axiom target_kernel]
                builder Kernel.NRAxiom;
              emit builder
                (Kernel.NRDisjElim
                   (target_kernel,
                    kernel_formula (Not target),
                    goal_name, negated_name));
              emit builder (Kernel.NRHypothesis em_name);
              emit builder (Kernel.NRHypothesis goal_name);
              begin match refutation_steps builder with
              | Error message -> Error message
              | Ok () -> Ok (finish builder)
              end
            end
        end
