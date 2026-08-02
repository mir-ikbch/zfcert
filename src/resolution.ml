(* A small propositional-resolution planner.

   This module is deliberately only a planner.  It searches over clauses in
   the OCaml syntax and emits ordinary named primitive rules.  The resulting
   certificate is checked by the extracted kernel before it changes a proof
   state.

   The planner decomposes propositional conjunctions, disjunctions,
   implications, and equivalences.  Leading universal quantifiers are
   instantiated by first-order unification.  Top-level existential
   hypotheses are opened with eigenvariables and the generated certificate
   keeps the corresponding elimination scopes.  A hypothesis whose outer
   connective is outside that fragment is deliberately kept opaque and
   treated as one propositional atom.  This lets resolution ignore unrelated
   first-order hypotheses while still using them when they happen to match a
   literal in the refutation.  Saturation uses a given-clause worklist and a
   coarse literal index; optional counters are enabled by
   [ZFCERT_RESOLUTION_STATS]. *)

module Kernel = Zfcert_kernel

open Syntax

type literal = bool * formula
type clause = literal list
type term_substitution = (string * term) list

type input = {
  source_name : string;
  source_formula : formula;
  universal_binders : string list;
  instantiation : term list;
  clause : clause;
  existing : bool;
  normalized_from : (string * formula) option;
}

type existential_wrapper = {
  source_name : string;
  existential : formula;
  witness : string;
  hypothesis : string;
}

type normalized_source = {
  origin_name : string;
  origin_formula : formula;
  source_formula : formula;
  universal_binders : string list;
  body_formula : formula;
}

type node_kind =
  | Input of input
  | Resolve of node * node * literal

and node = {
  name : string;
  clause : clause;
  variables : StringSet.t;
  kind : node_kind;
}

type atom_index_key =
  | IndexEquality
  | IndexMembership
  | IndexNamed of string
  | IndexOther

type literal_index_key = bool * atom_index_key

type search_stats = {
  started_at : float;
  mutable given_clauses : int;
  mutable indexed_candidates : int;
  mutable unification_attempts : int;
  mutable generated_resolvents : int;
  mutable duplicate_clauses : int;
  mutable max_clauses : int;
  mutable proof_steps : int;
  mutable reported : bool;
}

type builder = {
  mutable used_names : StringSet.t;
  mutable steps_reverse : Kernel.certificate_step list;
  stats : search_stats;
}

let make_builder hypotheses target =
  let names =
    List.fold_left
      (fun names (name, formula) ->
         StringSet.add name (StringSet.union names (all_vars formula)))
      (all_vars target) hypotheses
  in
  { used_names = names;
    steps_reverse = [];
    stats = {
      started_at = Sys.time ();
      given_clauses = 0;
      indexed_candidates = 0;
      unification_attempts = 0;
      generated_resolvents = 0;
      duplicate_clauses = 0;
      max_clauses = 0;
      proof_steps = 0;
      reported = false;
    } }

let fresh builder base =
  let name = fresh_name base builder.used_names in
  builder.used_names <- StringSet.add name builder.used_names;
  name

let emit ?(axioms = []) builder rule =
  builder.steps_reverse <-
    Kernel.certificate_step ~axioms rule :: builder.steps_reverse

let resolution_stats_enabled () =
  match Sys.getenv_opt "ZFCERT_RESOLUTION_STATS" with
  | Some value -> value <> "" && value <> "0"
  | None -> false

let report_search_stats builder =
  let stats = builder.stats in
  if resolution_stats_enabled () && not stats.reported then begin
    stats.reported <- true;
    Printf.eprintf
      ("ZFCert resolution: given=%d candidates=%d unifications=%d "
       ^^ "resolvents=%d duplicates=%d max-clauses=%d proof-steps=%d "
       ^^ "cpu=%.3fs\n")
      stats.given_clauses
      stats.indexed_candidates
      stats.unification_attempts
      stats.generated_resolvents
      stats.duplicate_clauses
      stats.max_clauses
      stats.proof_steps
      (Sys.time () -. stats.started_at)
  end

let finish builder =
  let steps = List.rev builder.steps_reverse in
  builder.stats.proof_steps <- List.length steps;
  report_search_stats builder;
  steps

let kernel_formula = Kernel_syntax.to_kernel

(* Push a negation through one or more leading existential quantifiers.  The
   returned binders are fresh eigenvariable names, and the final body is
   quantifier-free at its outermost level. *)
let normalize_negated_exists occupied = function
  | Not existential ->
      let rec peel occupied binders = function
        | Exists (binder, body) ->
            let witness = fresh_name binder occupied in
            let body = rename_bound binder witness body in
            peel (StringSet.add witness (StringSet.union occupied (all_vars body)))
              (binders @ [witness]) body
        | body -> (occupied, binders, body)
      in
      let occupied, binders, body = peel occupied [] existential in
      if binders = [] then None
      else
        let source_formula =
          List.fold_right
            (fun binder body -> Forall (binder, body)) binders (Not body)
        in
        Some (occupied, source_formula, binders, Not body)
  | _ -> None

(* Open leading existential quantifiers in hypotheses.  The generated body
   hypotheses are only available inside the corresponding [ex_elim] scopes;
   the wrappers are emitted before the resolution proof so no eigenvariable
   can escape into a cut outside its scope. *)
let prepare_existential_hypotheses hypotheses target =
  let occupied =
    List.fold_left
      (fun names (name, formula) ->
         StringSet.add name (StringSet.union names (all_vars formula)))
      (all_vars target) hypotheses
  in
  let rec peel occupied source_name formula wrappers =
    match formula with
    | Exists (binder, body) ->
        let witness = fresh_name binder occupied in
        let occupied = StringSet.add witness occupied in
        let hypothesis = fresh_name (source_name ^ "_witness") occupied in
        let body = rename_bound binder witness body in
        let occupied =
          StringSet.add hypothesis (StringSet.union occupied (all_vars body))
        in
        let wrapper =
          { source_name; existential = formula; witness; hypothesis }
        in
        peel occupied hypothesis body (wrappers @ [wrapper])
    | body -> (occupied, source_name, body, wrappers)
  in
  let rec loop occupied result wrappers normalized_sources = function
    | [] -> (List.rev result, wrappers, normalized_sources)
    | (source_name, formula) :: rest ->
        let occupied, body_name, body, source_wrappers =
          peel occupied source_name formula []
        in
        let occupied, source_normalization =
          match normalize_negated_exists occupied body with
          | Some (occupied, source_formula, universal_binders, body_formula) ->
              (occupied,
               Some
                 { origin_name = body_name;
                   origin_formula = body;
                   source_formula;
                   universal_binders;
                   body_formula })
          | None -> (occupied, None)
        in
        let normalized_sources =
          match source_normalization with
          | None -> normalized_sources
          | Some source -> source :: normalized_sources
        in
        loop occupied ((body_name, body) :: result)
          (wrappers @ source_wrappers) normalized_sources rest
  in
  loop occupied [] [] [] hypotheses

let emit_existential_wrappers builder wrappers =
  List.iter
    (fun wrapper ->
       emit builder
         (Kernel.NRExElim
            (wrapper.witness, wrapper.hypothesis,
             kernel_formula wrapper.existential));
       emit builder (Kernel.NRHypothesis wrapper.source_name))
    wrappers

(* Prove [forall w, not (body w)] from [not (exists x, body x)].  This is the
   quantifier-duality step needed when the negated goal is existential. *)
let prove_not_exists_to_forall builder source_name original normalized =
  match original with
  | Not existential ->
      let rec match_chain existential normalized witnesses =
        match existential, normalized with
        | Exists (binder, body), Forall (witness, rest) ->
            let body = rename_bound binder witness body in
            match_chain body rest (witness :: witnesses)
        | body, Not normalized_body when body = normalized_body ->
            Some (List.rev witnesses, body)
        | _ -> None
      in
      begin match match_chain existential normalized [] with
      | None ->
          Error "the normalized existential negation does not match its source"
      | Some (witnesses, _) ->
          let hypothesis = fresh builder "resolution_exists" in
          List.iter
            (fun witness -> emit builder (Kernel.NRAllIntro witness))
            witnesses;
          emit builder (Kernel.NRImplIntro hypothesis);
          emit builder (Kernel.NRImplElim (kernel_formula existential));
          emit builder (Kernel.NRHypothesis source_name);
          List.iter
            (fun witness ->
               emit builder
                 (Kernel.NRExIntro
                    (Kernel_syntax.to_kernel_term (Name witness))))
            witnesses;
          emit builder (Kernel.NRHypothesis hypothesis);
          Ok ()
      end
  | _ -> Error "the existential negation normalization has the wrong shape"

let rec apply_term substitution = function
  | Name name ->
      begin match List.assoc_opt name substitution with
      | None -> Name name
      | Some replacement when replacement = Name name -> Name name
      | Some replacement -> apply_term substitution replacement
      end
  | App (name, arguments) ->
      App (name, List.map (apply_term substitution) arguments)

let rec apply_formula substitution = function
  | Bottom -> Bottom
  | Named (name, arguments) -> Named (name, arguments)
  | Eq (left, right) ->
      Eq (apply_term substitution left, apply_term substitution right)
  | Mem (left, right) ->
      Mem (apply_term substitution left, apply_term substitution right)
  | Not formula -> Not (apply_formula substitution formula)
  | And (left, right) ->
      And (apply_formula substitution left, apply_formula substitution right)
  | Or (left, right) ->
      Or (apply_formula substitution left, apply_formula substitution right)
  | Imp (left, right) ->
      Imp (apply_formula substitution left, apply_formula substitution right)
  | Iff (left, right) ->
      Iff (apply_formula substitution left, apply_formula substitution right)
  | Forall (name, body) ->
      Forall (name,
        apply_formula (List.remove_assoc name substitution) body)
  | Exists (name, body) ->
      Exists (name,
        apply_formula (List.remove_assoc name substitution) body)

let apply_literal substitution (positive, atom) =
  (positive, apply_formula substitution atom)

let apply_clause substitution clause =
  List.map (apply_literal substitution) clause

let rec occurs variable = function
  | Name name -> name = variable
  | App (_, arguments) -> List.exists (occurs variable) arguments

let add_substitution variable replacement substitution =
  let replacement = apply_term substitution replacement in
  if replacement = Name variable || occurs variable replacement then
    None
  else
    Some
      ((variable, replacement)
       :: List.map
            (fun (name, term) -> (name, apply_term [variable, replacement] term))
            substitution)

let rec unify_terms flexible (substitution : term_substitution) left right =
  let left = apply_term substitution left in
  let right = apply_term substitution right in
  if left = right then Some substitution
  else
    match left, right with
    | Name left_name, _ when StringSet.mem left_name flexible ->
        add_substitution left_name right substitution
    | _, Name right_name when StringSet.mem right_name flexible ->
        add_substitution right_name left substitution
    | App (left_name, left_arguments), App (right_name, right_arguments)
      when left_name = right_name
           && List.length left_arguments = List.length right_arguments ->
        List.fold_left2
          (fun result left right ->
             match result with
             | None -> None
             | Some substitution ->
                 unify_terms flexible substitution left right)
          (Some substitution) left_arguments right_arguments
    | _ -> None

let unify_atoms flexible substitution left right =
  match left, right with
  | Eq (left_first, left_second), Eq (right_first, right_second)
  | Mem (left_first, left_second), Mem (right_first, right_second) ->
      begin match unify_terms flexible substitution left_first right_first with
      | None -> None
      | Some substitution ->
          unify_terms flexible substitution left_second right_second
      end
  | Named _, Named _ when left = right -> Some substitution
  | _ when left = right -> Some substitution
  | _ -> None

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
  | Not inner -> cnf_neg inner
  | And (left, right) ->
      begin match cnf left, cnf right with
      | Ok left_clauses, Ok right_clauses ->
          Ok (left_clauses @ right_clauses)
      | Error message, _ | _, Error message -> Error message
      end
  | Or (left, right) ->
      cnf_or (cnf left) (cnf right)
  | Imp (left, right) ->
      cnf_or (cnf_neg left) (cnf right)
  | Iff (left, right) ->
      cnf (And (Imp (left, right), Imp (right, left)))
  (* Quantifiers and other non-propositional formulas remain opaque atoms. *)
  | formula -> Ok [ [ (true, formula) ] ]

and cnf_neg formula =
  match formula with
  | Bottom -> Ok []
  | Eq _ | Mem _ | Named _ | Forall _ | Exists _ ->
      Ok [ [ (false, formula) ] ]
  | Not inner -> cnf inner
  | And (left, right) ->
      cnf_or (cnf_neg left) (cnf_neg right)
  | Or (left, right) ->
      begin match cnf_neg left, cnf_neg right with
      | Ok left_clauses, Ok right_clauses ->
          Ok (left_clauses @ right_clauses)
      | Error message, _ | _, Error message -> Error message
      end
  | Imp (left, right) ->
      begin match cnf left, cnf_neg right with
      | Ok left_clauses, Ok right_clauses ->
          Ok (left_clauses @ right_clauses)
      | Error message, _ | _, Error message -> Error message
      end
  | Iff (left, right) ->
      (* not (A <-> B) is the XOR, (A or B) and (not A or not B). *)
      cnf
        (And
           (Or (left, right),
            Or (Not left, Not right)))

and cnf_or left_result right_result =
  match left_result, right_result with
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
      derive_negated_formula builder source_name inner target
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
  | Imp (left, right) ->
      (* A -> B is classically equivalent to (not A or B).  Prove that
         disjunction from the implication by a classical case split on A,
         then derive the requested CNF clause from it. *)
      let normalized = Or (Not left, right) in
      let normalized_name = fresh builder "resolution_implication" in
      emit builder
        (Kernel.NRCut (normalized_name, kernel_formula normalized));
      let excluded_middle_name = fresh builder "resolution_em" in
      emit builder
        (Kernel.NRCut
           (excluded_middle_name,
            kernel_formula (Or (left, Not left))));
      emit ~axioms:[Kernel.classical_axiom (kernel_formula left)]
        builder Kernel.NRAxiom;
      let left_name = fresh builder "resolution_left" in
      let negated_left_name = fresh builder "resolution_not_left" in
      emit builder
        (Kernel.NRDisjElim
           (kernel_formula left,
            kernel_formula (Not left),
            left_name, negated_left_name));
      emit builder (Kernel.NRHypothesis excluded_middle_name);
      emit builder Kernel.NRDisjIntroR;
      emit builder (Kernel.NRImplElim (kernel_formula left));
      emit builder (Kernel.NRHypothesis source_name);
      emit builder (Kernel.NRHypothesis left_name);
      emit builder Kernel.NRDisjIntroL;
      emit builder (Kernel.NRHypothesis negated_left_name);
      derive_clause_from_hyp builder normalized_name normalized target
  | Iff (left, right) ->
      (* A <-> B is represented by the conjunction of both implications in
         the extracted kernel.  Select the implication containing the target
         clause and expose it with the corresponding conjunction elimination
         rule. *)
      let forward = Imp (left, right) in
      let backward = Imp (right, left) in
      begin match cnf forward, cnf backward with
      | Ok forward_clauses, Ok backward_clauses ->
          if Option.is_some (find_clause forward_clauses target) then begin
            let part_name = fresh builder "resolution_forward" in
            emit builder
              (Kernel.NRCut (part_name, kernel_formula forward));
            emit builder (Kernel.NRConjElimL (kernel_formula backward));
            emit builder (Kernel.NRHypothesis source_name);
            derive_clause_from_hyp builder part_name forward target
          end else if Option.is_some (find_clause backward_clauses target) then begin
            let part_name = fresh builder "resolution_backward" in
            emit builder
              (Kernel.NRCut (part_name, kernel_formula backward));
            emit builder (Kernel.NRConjElimR (kernel_formula forward));
            emit builder (Kernel.NRHypothesis source_name);
            derive_clause_from_hyp builder part_name backward target
          end else
            Error "the source equivalence does not contain the requested clause"
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

and derive_negated_formula builder source_name inner target =
  match inner with
  | Bottom -> Error "the negated falsum does not contain a requested clause"
  | Eq _ | Mem _ | Named _ | Forall _ | Exists _ ->
      begin match target with
      | [literal] when literal = (false, inner) ->
          emit builder (Kernel.NRHypothesis source_name);
          Ok ()
      | _ -> Error "the source negation does not match the requested clause"
      end
  | Iff (left, right) ->
      derive_negated_iff builder source_name left right target
  | Not body ->
      (* Double negation is eliminated by a classical case split on [body]. *)
      begin match cnf body with
      | Error message -> Error message
      | Ok clauses when Option.is_some (find_clause clauses target) ->
          let excluded_middle_name = fresh builder "resolution_em" in
          emit builder
            (Kernel.NRCut
               (excluded_middle_name,
                kernel_formula (Or (body, Not body))));
          emit ~axioms:[Kernel.classical_axiom (kernel_formula body)]
            builder Kernel.NRAxiom;
          let body_name = fresh builder "resolution_body" in
          let negated_body_name = fresh builder "resolution_not_body" in
          emit builder
            (Kernel.NRDisjElim
               (kernel_formula body,
                kernel_formula (Not body),
                body_name, negated_body_name));
          emit builder (Kernel.NRHypothesis excluded_middle_name);
          begin match derive_clause_from_hyp builder body_name body target with
          | Error message -> Error message
          | Ok () ->
              emit builder Kernel.NRFalsumElim;
              emit builder (Kernel.NRImplElim (kernel_formula (Not body)));
              emit builder (Kernel.NRHypothesis source_name);
              emit builder (Kernel.NRHypothesis negated_body_name);
              Ok ()
          end
      | Ok _ -> Error "the double negation does not contain the requested clause"
      end
  | And (left, right) ->
      (* not (A and B) implies (not A or not B). *)
      let normalized = Or (Not left, Not right) in
      begin match cnf normalized with
      | Error message -> Error message
      | Ok clauses when Option.is_some (find_clause clauses target) ->
          let normalized_name = fresh builder "resolution_not_and" in
          emit builder
            (Kernel.NRCut (normalized_name, kernel_formula normalized));
          let excluded_middle_name = fresh builder "resolution_em" in
          emit builder
            (Kernel.NRCut
               (excluded_middle_name,
                kernel_formula (Or (left, Not left))));
          emit ~axioms:[Kernel.classical_axiom (kernel_formula left)]
            builder Kernel.NRAxiom;
          let left_name = fresh builder "resolution_left" in
          let negated_left_name = fresh builder "resolution_not_left" in
          emit builder
            (Kernel.NRDisjElim
               (kernel_formula left,
                kernel_formula (Not left),
                left_name, negated_left_name));
          emit builder (Kernel.NRHypothesis excluded_middle_name);
          emit builder Kernel.NRDisjIntroR;
          let right_name = fresh builder "resolution_right" in
          emit builder (Kernel.NRImplIntro right_name);
          emit builder
            (Kernel.NRImplElim (kernel_formula (And (left, right))));
          emit builder (Kernel.NRHypothesis source_name);
          emit builder Kernel.NRConjIntro;
          emit builder (Kernel.NRHypothesis left_name);
          emit builder (Kernel.NRHypothesis right_name);
          emit builder Kernel.NRDisjIntroL;
          emit builder (Kernel.NRHypothesis negated_left_name);
          derive_clause_from_hyp builder normalized_name normalized target
      | Ok _ -> Error "the negated conjunction does not contain the requested clause"
      end
  | Or (left, right) ->
      (* not (A or B) implies (not A and not B). *)
      let normalized = And (Not left, Not right) in
      begin match cnf normalized with
      | Error message -> Error message
      | Ok clauses when Option.is_some (find_clause clauses target) ->
          let normalized_name = fresh builder "resolution_not_or" in
          emit builder
            (Kernel.NRCut (normalized_name, kernel_formula normalized));
          emit builder Kernel.NRConjIntro;
          let left_name = fresh builder "resolution_left" in
          emit builder (Kernel.NRImplIntro left_name);
          emit builder (Kernel.NRImplElim (kernel_formula (Or (left, right))));
          emit builder (Kernel.NRHypothesis source_name);
          emit builder Kernel.NRDisjIntroL;
          emit builder (Kernel.NRHypothesis left_name);
          let right_name = fresh builder "resolution_right" in
          emit builder (Kernel.NRImplIntro right_name);
          emit builder (Kernel.NRImplElim (kernel_formula (Or (left, right))));
          emit builder (Kernel.NRHypothesis source_name);
          emit builder Kernel.NRDisjIntroR;
          emit builder (Kernel.NRHypothesis right_name);
          derive_clause_from_hyp builder normalized_name normalized target
      | Ok _ -> Error "the negated disjunction does not contain the requested clause"
      end
  | Imp (left, right) ->
      (* not (A -> B) implies (A and not B).  The proof of A uses excluded
         middle: the not-A branch contradicts the source negated implication. *)
      let normalized = And (left, Not right) in
      begin match cnf normalized with
      | Error message -> Error message
      | Ok clauses when Option.is_some (find_clause clauses target) ->
          let normalized_name = fresh builder "resolution_not_imp" in
          emit builder
            (Kernel.NRCut (normalized_name, kernel_formula normalized));
          let excluded_middle_name = fresh builder "resolution_em" in
          emit builder
            (Kernel.NRCut
               (excluded_middle_name,
                kernel_formula (Or (left, Not left))));
          emit ~axioms:[Kernel.classical_axiom (kernel_formula left)]
            builder Kernel.NRAxiom;
          let left_name = fresh builder "resolution_left" in
          let negated_left_name = fresh builder "resolution_not_left" in
          emit builder
            (Kernel.NRDisjElim
               (kernel_formula left,
                kernel_formula (Not left),
                left_name, negated_left_name));
          emit builder (Kernel.NRHypothesis excluded_middle_name);
          let right_name = fresh builder "resolution_right" in
          emit builder Kernel.NRConjIntro;
          emit builder (Kernel.NRHypothesis left_name);
          emit builder (Kernel.NRImplIntro right_name);
          emit builder
            (Kernel.NRImplElim (kernel_formula (Imp (left, right))));
          emit builder (Kernel.NRHypothesis source_name);
          let left_for_right = fresh builder "resolution_left" in
          emit builder (Kernel.NRImplIntro left_for_right);
          emit builder (Kernel.NRHypothesis right_name);
          emit builder Kernel.NRFalsumElim;
          emit builder
            (Kernel.NRImplElim (kernel_formula (Imp (left, right))));
          emit builder (Kernel.NRHypothesis source_name);
          let left_again = fresh builder "resolution_left" in
          emit builder (Kernel.NRImplIntro left_again);
          emit builder Kernel.NRFalsumElim;
          emit builder (Kernel.NRImplElim (kernel_formula left));
          emit builder (Kernel.NRHypothesis negated_left_name);
          emit builder (Kernel.NRHypothesis left_again);
          derive_clause_from_hyp builder normalized_name normalized target
      | Ok _ -> Error "the negated implication does not contain the requested clause"
      end

and derive_negated_iff builder source_name left right target =
  let normalized =
    And (Or (left, right), Or (Not left, Not right))
  in
  begin match cnf normalized with
  | Error message -> Error message
  | Ok clauses when Option.is_some (find_clause clauses target) ->
      let normalized_name = fresh builder "resolution_not_iff" in
      emit builder
        (Kernel.NRCut (normalized_name, kernel_formula normalized));
      emit builder Kernel.NRConjIntro;

      (* First conjunct: A or B. *)
      let first_em_name = fresh builder "resolution_em" in
      emit builder
        (Kernel.NRCut
           (first_em_name, kernel_formula (Or (left, Not left))));
      emit ~axioms:[Kernel.classical_axiom (kernel_formula left)]
        builder Kernel.NRAxiom;
      let first_left_name = fresh builder "resolution_left" in
      let first_not_left_name = fresh builder "resolution_not_left" in
      emit builder
        (Kernel.NRDisjElim
           (kernel_formula left,
            kernel_formula (Not left),
            first_left_name, first_not_left_name));
      emit builder (Kernel.NRHypothesis first_em_name);
      emit builder Kernel.NRDisjIntroL;
      emit builder (Kernel.NRHypothesis first_left_name);

      (* In the not-A branch, split on B. *)
      let second_em_name = fresh builder "resolution_em" in
      emit builder
        (Kernel.NRCut
           (second_em_name, kernel_formula (Or (right, Not right))));
      emit ~axioms:[Kernel.classical_axiom (kernel_formula right)]
        builder Kernel.NRAxiom;
      let first_right_name = fresh builder "resolution_right" in
      let first_not_right_name = fresh builder "resolution_not_right" in
      emit builder
        (Kernel.NRDisjElim
           (kernel_formula right,
            kernel_formula (Not right),
            first_right_name, first_not_right_name));
      emit builder (Kernel.NRHypothesis second_em_name);
      emit builder Kernel.NRDisjIntroR;
      emit builder (Kernel.NRHypothesis first_right_name);
      emit builder Kernel.NRFalsumElim;
      emit builder (Kernel.NRImplElim (kernel_formula (Iff (left, right))));
      emit builder (Kernel.NRHypothesis source_name);
      emit builder Kernel.NRConjIntro;
      let first_forward = fresh builder "resolution_forward" in
      emit builder (Kernel.NRImplIntro first_forward);
      emit builder Kernel.NRFalsumElim;
      emit builder (Kernel.NRImplElim (kernel_formula left));
      emit builder (Kernel.NRHypothesis first_not_left_name);
      emit builder (Kernel.NRHypothesis first_forward);
      let first_backward = fresh builder "resolution_backward" in
      emit builder (Kernel.NRImplIntro first_backward);
      emit builder Kernel.NRFalsumElim;
      emit builder (Kernel.NRImplElim (kernel_formula right));
      emit builder (Kernel.NRHypothesis first_not_right_name);
      emit builder (Kernel.NRHypothesis first_backward);

      (* Second conjunct: not A or not B. *)
      let third_em_name = fresh builder "resolution_em" in
      emit builder
        (Kernel.NRCut
           (third_em_name, kernel_formula (Or (left, Not left))));
      emit ~axioms:[Kernel.classical_axiom (kernel_formula left)]
        builder Kernel.NRAxiom;
      let second_left_name = fresh builder "resolution_left" in
      let second_not_left_name = fresh builder "resolution_not_left" in
      emit builder
        (Kernel.NRDisjElim
           (kernel_formula left,
            kernel_formula (Not left),
            second_left_name, second_not_left_name));
      emit builder (Kernel.NRHypothesis third_em_name);

      (* In the A branch, split on B. *)
      let fourth_em_name = fresh builder "resolution_em" in
      emit builder
        (Kernel.NRCut
           (fourth_em_name, kernel_formula (Or (right, Not right))));
      emit ~axioms:[Kernel.classical_axiom (kernel_formula right)]
        builder Kernel.NRAxiom;
      let second_right_name = fresh builder "resolution_right" in
      let second_not_right_name = fresh builder "resolution_not_right" in
      emit builder
        (Kernel.NRDisjElim
           (kernel_formula right,
            kernel_formula (Not right),
            second_right_name, second_not_right_name));
      emit builder (Kernel.NRHypothesis fourth_em_name);
      emit builder Kernel.NRFalsumElim;
      emit builder (Kernel.NRImplElim (kernel_formula (Iff (left, right))));
      emit builder (Kernel.NRHypothesis source_name);
      emit builder Kernel.NRConjIntro;
      let second_forward = fresh builder "resolution_forward" in
      emit builder (Kernel.NRImplIntro second_forward);
      emit builder (Kernel.NRHypothesis second_right_name);
      let second_backward = fresh builder "resolution_backward" in
      emit builder (Kernel.NRImplIntro second_backward);
      emit builder (Kernel.NRHypothesis second_left_name);
      emit builder Kernel.NRDisjIntroR;
      emit builder (Kernel.NRHypothesis second_not_right_name);
      emit builder Kernel.NRDisjIntroL;
      emit builder (Kernel.NRHypothesis second_not_left_name);
      derive_clause_from_hyp builder normalized_name normalized target
  | Ok _ -> Error "the negated equivalence does not contain the requested clause"
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

let clause_variables clause =
  List.fold_left
    (fun variables (_, atom) -> StringSet.union variables (all_vars atom))
    StringSet.empty clause

let rec instantiate_node substitution node =
  let clause = apply_clause substitution node.clause in
  let kind =
    match node.kind with
    | Input input ->
        Input
          { input with
            clause;
            instantiation =
              List.map (apply_term substitution) input.instantiation }
    | Resolve (first, second, pivot) ->
        Resolve
          (instantiate_node substitution first,
           instantiate_node substitution second,
           apply_literal substitution pivot)
  in
  let variables =
    match kind with
    | Input input -> StringSet.of_list input.universal_binders
    | Resolve (first, second, _) ->
        StringSet.union first.variables second.variables
  in
  { node with clause; variables; kind }

let atom_index_key = function
  | Eq _ -> IndexEquality
  | Mem _ -> IndexMembership
  | Named (name, _) -> IndexNamed name
  | _ -> IndexOther

let literal_index_key (positive, atom) =
  (positive, atom_index_key atom)

type literal_index = (literal_index_key, (node * literal) list) Hashtbl.t

let add_to_literal_index index node =
  List.iter
    (fun literal ->
       let key = literal_index_key literal in
       let previous =
         match Hashtbl.find_opt index key with
         | Some candidates -> candidates
         | None -> []
       in
       Hashtbl.replace index key ((node, literal) :: previous))
    node.clause

let indexed_candidates index literal =
  let positive, atom = literal in
  match Hashtbl.find_opt index (not positive, atom_index_key atom) with
  | Some candidates -> candidates
  | None -> []

module ClauseTable = Hashtbl.Make (struct
  type t = clause
  let equal = clause_equal
  let hash = Hashtbl.hash
end)

let indexed_resolvents builder index first =
  let stats = builder.stats in
  List.concat_map
    (fun first_literal ->
       let candidates = indexed_candidates index first_literal in
       List.filter_map
         (fun (second, second_literal) ->
            stats.indexed_candidates <- stats.indexed_candidates + 1;
            stats.unification_attempts <- stats.unification_attempts + 1;
            let flexible = StringSet.union first.variables second.variables in
            match
              unify_atoms flexible [] (snd first_literal) (snd second_literal)
            with
            | None -> None
            | Some substitution ->
                let first_instantiated =
                  instantiate_node substitution first
                in
                let second_instantiated =
                  instantiate_node substitution second
                in
                let first_pivot =
                  apply_literal substitution first_literal
                in
                let second_pivot =
                  apply_literal substitution second_literal
                in
                begin match
                  normalize_clause
                    (List.filter
                       (fun item -> not (same_literal item first_pivot))
                       first_instantiated.clause
                     @ List.filter
                         (fun item ->
                            not (same_literal item second_pivot))
                         second_instantiated.clause)
                with
                | None -> None
                | Some clause ->
                    stats.generated_resolvents <-
                      stats.generated_resolvents + 1;
                    Some (clause, first_instantiated,
                          second_instantiated, first_pivot)
                end)
         candidates)
    first.clause

let saturate builder initial_nodes =
  let seen = ClauseTable.create (max 17 (List.length initial_nodes * 2)) in
  let index : literal_index = Hashtbl.create 31 in
  let pending = Queue.create () in
  let all_nodes = ref [] in
  let add_node node =
    if ClauseTable.mem seen node.clause then false
    else begin
      ClauseTable.add seen node.clause node;
      Queue.add node pending;
      all_nodes := node :: !all_nodes;
      builder.stats.max_clauses <-
        max builder.stats.max_clauses (ClauseTable.length seen);
      true
    end
  in
  List.iter (fun node -> ignore (add_node node)) initial_nodes;
  let rec loop () =
    if Queue.is_empty pending then
      Error "no resolution refutation was found"
    else
      let given = Queue.take pending in
      builder.stats.given_clauses <- builder.stats.given_clauses + 1;
      if given.clause = [] then
        Ok (!all_nodes, given)
      else begin
        let additions = indexed_resolvents builder index given in
        List.iter
          (fun (clause, first, second, pivot) ->
             if ClauseTable.mem seen clause then
               builder.stats.duplicate_clauses <-
                 builder.stats.duplicate_clauses + 1
             else
               let name = fresh builder "resolution_clause" in
               let variables =
                 StringSet.union first.variables second.variables
                 |> StringSet.filter
                      (fun variable ->
                         StringSet.mem variable
                           (clause_variables clause))
               in
               ignore
                 (add_node
                    { name; clause; variables;
                      kind = Resolve (first, second, pivot) }))
          additions;
        add_to_literal_index index given;
        if ClauseTable.length seen > 512 then
          Error "the resolution search exceeded its 512-clause limit"
        else
          loop ()
      end
  in
  let result = loop () in
  begin match result with
  | Ok _ -> ()
  | Error _ -> report_search_stats builder
  end;
  result

let prepare_universal_source used source_formula =
  let rec peel occupied binders formula =
    match formula with
    | Forall (name, body) ->
        let fresh = fresh_name name occupied in
        let body = rename_bound name fresh body in
        peel
          (StringSet.add fresh (StringSet.union occupied (all_vars body)))
          (binders @ [fresh]) body
    | body -> (binders, body)
  in
  let binders, body =
    peel (StringSet.union used (all_vars source_formula)) [] source_formula
  in
  let source_formula =
    List.fold_right (fun binder body -> Forall (binder, body)) binders body
  in
  (source_formula, binders, body)

let initial_inputs used_names hypotheses =
  let sources = hypotheses in
  let rec loop occupied (result : input list) = function
    | [] -> Ok (List.rev result)
    | (source_name, source_formula) :: rest ->
        let source_formula, universal_binders, body_formula =
          prepare_universal_source occupied source_formula
        in
        let occupied =
          StringSet.union occupied (StringSet.of_list universal_binders)
        in
        let clauses =
          match cnf body_formula with
          | Ok clauses -> clauses
          | Error _ -> [ [ (true, body_formula) ] ]
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
                 ({ source_name; source_formula; universal_binders;
                    instantiation = List.map (fun name -> Name name)
                      universal_binders;
                    clause; existing = false; normalized_from = None }
                   : input)
                 :: result)
            result clauses
        in
        loop occupied result rest
  in
  loop used_names [] sources

let rec terms_in_term bound = function
  | Name name ->
      if StringSet.mem name bound then [] else [Name name]
  | App (_name, arguments) as term ->
      if List.exists
           (fun argument ->
              not (StringSet.is_empty
                     (StringSet.inter bound (term_free_vars argument))))
           arguments
      then []
      else
        term
        :: List.concat_map (terms_in_term bound) arguments

let rec terms_in_formula bound = function
  | Bottom | Named _ -> []
  | Eq (left, right) | Mem (left, right) ->
      terms_in_term bound left @ terms_in_term bound right
  | Not formula -> terms_in_formula bound formula
  | And (left, right)
  | Or (left, right)
  | Imp (left, right)
  | Iff (left, right) ->
      terms_in_formula bound left @ terms_in_formula bound right
  | Forall (name, formula) | Exists (name, formula) ->
      terms_in_formula (StringSet.add name bound) formula

let unique_terms terms =
  List.fold_left
    (fun result term -> if List.mem term result then result else term :: result)
    [] terms
  |> List.rev

(* Candidate witnesses for an existential goal.  Choosing a term already
   present in the context keeps the subsequent resolution problem ground at
   the witness position and avoids introducing an unnecessary existential
   search variable.  Compound terms are tried after names because names are
   the usual eigenvariables and constants introduced by [obtain]. *)
let existential_witness_terms hypotheses target =
  let terms =
    unique_terms
      (List.concat_map
         (fun (_, formula) -> terms_in_formula StringSet.empty formula)
         hypotheses
       @ terms_in_formula StringSet.empty target)
  in
  let names, applications =
    List.partition
      (function
       | Name _ -> true
       | App _ -> false)
      terms
  in
  names @ applications

let rec node_variables node =
  match node.kind with
  | Input _ -> node.variables
  | Resolve (first, second, _) ->
      StringSet.union (node_variables first) (node_variables second)

let ground_node substitution node = instantiate_node substitution node

let ground_resolution_nodes hypotheses target empty_node =
  let available_terms =
    unique_terms
      (List.concat_map (fun (_, formula) -> terms_in_formula StringSet.empty formula)
         hypotheses
       @ terms_in_formula StringSet.empty target)
  in
  let variables = node_variables empty_node in
  if StringSet.is_empty variables then Ok empty_node
  else
    match available_terms with
    | [] ->
        Error
          "resolution needs a ground term to instantiate a universal hypothesis"
    | first_term :: _ ->
        let substitution =
          StringSet.elements variables
          |> List.map (fun variable -> (variable, first_term))
        in
        Ok (ground_node substitution empty_node)

let emit_input_proof builder input target =
  let rec eliminate formula binders terms rules =
    match binders, terms, formula with
    | [], [], body -> Ok (body, List.rev rules)
    | _binder :: binders, term :: terms, Forall (name, body) ->
        let rule =
          Kernel.NRAllElim
            (Kernel_syntax.to_kernel_term term,
             kernel_formula formula)
        in
        eliminate (subst name term body) binders terms (rules @ [rule])
    | _ -> Error "the universal source and its instantiation do not match"
  in
  let source_name =
    match input.normalized_from with
    | None -> Ok input.source_name
    | Some (origin_name, origin_formula) ->
        let normalized_name = fresh builder "resolution_normalized" in
        emit builder
          (Kernel.NRCut
             (normalized_name, kernel_formula input.source_formula));
        begin match
          prove_not_exists_to_forall builder origin_name origin_formula
            input.source_formula
        with
        | Error message -> Error message
        | Ok () -> Ok normalized_name
        end
  in
  match source_name with
  | Error message -> Error message
  | Ok source_name ->
      begin match
        eliminate input.source_formula input.universal_binders
          input.instantiation []
      with
      | Error message -> Error message
      | Ok (body, []) -> derive_clause_from_hyp builder source_name body target
      | Ok (body, rules) ->
          let instance_name = fresh builder "resolution_instance" in
          emit builder
            (Kernel.NRCut (instance_name, kernel_formula body));
          List.iter (emit builder) rules;
          emit builder (Kernel.NRHypothesis source_name);
          derive_clause_from_hyp builder instance_name body target
      end

let rec emit_node builder node =
  match node.kind with
  | Input input -> emit_input_proof builder input node.clause
  | Resolve (first, second, pivot) ->
      let first_name = fresh builder "resolution_parent" in
      emit builder
        (Kernel.NRCut
           (first_name, kernel_formula (clause_formula first.clause)));
      begin match emit_node builder first with
      | Error message -> Error message
      | Ok () ->
          let second_name = fresh builder "resolution_parent" in
          emit builder
            (Kernel.NRCut
               (second_name, kernel_formula (clause_formula second.clause)));
          begin match emit_node builder second with
          | Error message -> Error message
          | Ok () ->
              let first = { first with name = first_name } in
              let second = { second with name = second_name } in
              prove_resolution builder first second pivot node.clause
          end
      end

let plan_non_forall hypotheses target =
  let target_kernel = kernel_formula target in
  let refutation_formula =
    match target with
    | Bottom -> Bottom
    | _ -> Not target
  in
  let hypotheses, existential_wrappers, normalized_sources =
    prepare_existential_hypotheses hypotheses target
  in
  let builder = make_builder hypotheses target in
  builder.used_names <-
    List.fold_left
      (fun names source ->
         StringSet.union names (all_vars source.source_formula))
      builder.used_names normalized_sources;
  emit_existential_wrappers builder existential_wrappers;
  let refutation_source, refutation_binders, refutation_body =
    match normalize_negated_exists builder.used_names refutation_formula with
    | Some (occupied, source_formula, binders, body_formula) ->
        builder.used_names <- occupied;
        (source_formula, binders, body_formula)
    | None -> (refutation_formula, [], refutation_formula)
  in
  let resolution_hypotheses =
    let normalized_names =
      List.fold_left
        (fun names source -> StringSet.add source.origin_name names)
        StringSet.empty normalized_sources
    in
    List.filter
      (fun (name, _) -> not (StringSet.mem name normalized_names))
      hypotheses
  in
  match initial_inputs builder.used_names resolution_hypotheses with
    | Error message -> Error message
    | Ok inputs ->
        let inputs =
          List.fold_left
            (fun inputs source ->
               match cnf source.body_formula with
               | Error _ -> inputs
               | Ok clauses ->
                   List.fold_left
                     (fun result clause ->
                        if List.exists
                             (fun (input : input) ->
                                clause_equal input.clause clause)
                             result
                        then result
                        else
                          ({ source_name = source.origin_name;
                             source_formula = source.source_formula;
                             universal_binders = source.universal_binders;
                             instantiation =
                               List.map (fun name -> Name name)
                                 source.universal_binders;
                             clause; existing = true;
                             normalized_from =
                               Some (source.origin_name, source.origin_formula) }
                           : input)
                          :: result)
                     inputs clauses)
            inputs normalized_sources
        in
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
              begin match cnf refutation_body with
              | Error _ -> inputs
              | Ok clauses ->
                  List.fold_left
                    (fun result clause ->
                       if List.exists
                            (fun (input : input) -> clause_equal input.clause clause)
                            result
                       then result
                       else
                         ({ source_name;
                            source_formula = refutation_source;
                            universal_binders = refutation_binders;
                            instantiation =
                              List.map (fun name -> Name name)
                                refutation_binders;
                            clause; existing = true;
                            normalized_from =
                              (match target with
                               | Exists _ -> Some (source_name, refutation_formula)
                               | _ -> None) } : input)
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
                 variables = StringSet.of_list input.universal_binders;
                 kind = Input input })
            inputs
        in
        begin match saturate builder input_nodes with
        | Error message -> Error message
        | Ok (_nodes, empty_node) ->
            begin match ground_resolution_nodes hypotheses target empty_node with
            | Error message -> Error message
            | Ok empty_node ->
                let refutation_steps () =
                  let empty_name = fresh builder "resolution_empty" in
                  emit builder
                    (Kernel.NRCut (empty_name, kernel_formula Bottom));
                  begin match emit_node builder empty_node with
                  | Error message -> Error message
                  | Ok () ->
                      emit builder Kernel.NRFalsumElim;
                      emit builder (Kernel.NRHypothesis empty_name);
                      Ok ()
                  end
                in
            if target = Bottom then begin
              match refutation_steps () with
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
              begin match refutation_steps () with
              | Error message -> Error message
              | Ok () -> Ok (finish builder)
              end
            end
            end
        end

let rec plan hypotheses target =
  match target with
  | Forall (binder, body) ->
      let used =
        List.fold_left
          (fun names (_, formula) ->
             StringSet.union names (all_vars formula))
          (all_vars target) hypotheses
      in
      let fresh = fresh_name binder used in
      let body = rename_bound binder fresh body in
      begin match plan hypotheses body with
      | Error message -> Error message
      | Ok steps ->
          Ok
            (Kernel.certificate_step ~axioms:[]
             (Kernel.NRAllIntro fresh)
             :: steps)
      end
  | Exists (binder, body) ->
      let occupied =
        List.fold_left
          (fun names (name, formula) ->
             StringSet.add name (StringSet.union names (all_vars formula)))
          (all_vars target) hypotheses
      in
      let existential_sources =
        List.filter_map
          (fun (source_name, source_formula) ->
             match source_formula with
             | Exists (source_binder, source_body) ->
                 Some (source_name, source_formula, source_binder, source_body)
             | _ -> None)
          hypotheses
      in
      (* When an existential hypothesis is available, open it before
         selecting the witness for the existential goal.  This is the
         certificate-level equivalent of [obtain p Hp from H; use p], and
         keeps the eigenvariable introduced by [ex_elim] in scope for the
         subsequent [ex_intro]. *)
      let rec try_existential_sources = function
        | (source_name, source_formula, source_binder, source_body) :: rest ->
            let witness = fresh_name source_binder occupied in
            let opened_body = rename_bound source_binder witness source_body in
            let hypothesis =
              fresh_name (source_name ^ "_witness")
                (StringSet.add witness occupied)
            in
            let remaining =
              List.filter (fun (name, _) -> name <> source_name) hypotheses
            in
            let opened_hypotheses = (hypothesis, opened_body) :: remaining in
            let instantiated_target = subst binder (Name witness) body in
            begin match plan opened_hypotheses instantiated_target with
            | Ok steps ->
                Ok
                  ([ Kernel.certificate_step ~axioms:[]
                       (Kernel.NRExElim
                          (witness, hypothesis,
                           kernel_formula source_formula));
                     Kernel.certificate_step ~axioms:[]
                       (Kernel.NRHypothesis source_name);
                     Kernel.certificate_step ~axioms:[]
                       (Kernel.NRExIntro
                          (Kernel_syntax.to_kernel_term (Name witness)))]
                   @ steps)
            | Error _ -> try_existential_sources rest
            end
        | [] ->
            let rec try_witnesses = function
              | witness :: rest ->
                  let instantiated = subst binder witness body in
                  begin match plan hypotheses instantiated with
                  | Ok steps ->
                      Ok
                        (Kernel.certificate_step ~axioms:[]
                           (Kernel.NRExIntro
                              (Kernel_syntax.to_kernel_term witness))
                         :: steps)
                  | Error _ -> try_witnesses rest
                  end
              | [] -> plan_non_forall hypotheses target
            in
            try_witnesses (existential_witness_terms hypotheses target)
      in
      try_existential_sources existential_sources
  | _ -> plan_non_forall hypotheses target
