
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

module Nat =
 struct
 end

(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> None
              | x :: _ -> Some x)
    (fun n0 -> match l with
               | [] -> None
               | _ :: l0 -> nth_error l0 n0)
    n

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

type formula =
| Falsum
| Equal of int * int
| Member of int * int
| Conj of formula * formula
| Disj of formula * formula
| Impl of formula * formula
| All of formula
| Ex of formula

(** val formula_eq_dec : formula -> formula -> bool **)

let rec formula_eq_dec f x =
  match f with
  | Falsum -> (match x with
               | Falsum -> true
               | _ -> false)
  | Equal (n, n0) ->
    (match x with
     | Equal (n1, n2) -> if (=) n n1 then (=) n0 n2 else false
     | _ -> false)
  | Member (n, n0) ->
    (match x with
     | Member (n1, n2) -> if (=) n n1 then (=) n0 n2 else false
     | _ -> false)
  | Conj (f0, f1) ->
    (match x with
     | Conj (f2, f3) ->
       if formula_eq_dec f0 f2 then formula_eq_dec f1 f3 else false
     | _ -> false)
  | Disj (f0, f1) ->
    (match x with
     | Disj (f2, f3) ->
       if formula_eq_dec f0 f2 then formula_eq_dec f1 f3 else false
     | _ -> false)
  | Impl (f0, f1) ->
    (match x with
     | Impl (f2, f3) ->
       if formula_eq_dec f0 f2 then formula_eq_dec f1 f3 else false
     | _ -> false)
  | All f0 -> (match x with
               | All f1 -> formula_eq_dec f0 f1
               | _ -> false)
  | Ex f0 -> (match x with
              | Ex f1 -> formula_eq_dec f0 f1
              | _ -> false)

(** val formula_eqb : formula -> formula -> bool **)

let formula_eqb a b =
  if formula_eq_dec a b then true else false

(** val neg : formula -> formula **)

let neg a =
  Impl (a, Falsum)

(** val up : (int -> int) -> int -> int **)

let up xi n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun k -> Stdlib.Int.succ (xi k))
    n

(** val rename : (int -> int) -> formula -> formula **)

let rec rename xi = function
| Falsum -> Falsum
| Equal (x, y) -> Equal ((xi x), (xi y))
| Member (x, y) -> Member ((xi x), (xi y))
| Conj (b, c) -> Conj ((rename xi b), (rename xi c))
| Disj (b, c) -> Disj ((rename xi b), (rename xi c))
| Impl (b, c) -> Impl ((rename xi b), (rename xi c))
| All b -> All (rename (up xi) b)
| Ex b -> Ex (rename (up xi) b)

(** val lift : formula -> formula **)

let lift a =
  rename (fun x -> Stdlib.Int.succ x) a

(** val subst_zero : int -> int -> int **)

let subst_zero t n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> t)
    (fun k -> k)
    n

(** val instantiate : int -> formula -> formula **)

let instantiate t a =
  rename (subst_zero t) a

type goal = { assumptions : formula list; conclusion : formula }

type proof_state = goal list

type rule =
| RAxiom
| RHypothesis of int
| RFalsumElim
| RImplIntro
| RImplElim of formula
| RConjIntro
| RConjElimL of formula
| RConjElimR of formula
| RDisjIntroL
| RDisjIntroR
| RDisjElim of formula * formula
| RAllIntro
| RAllElim of formula * int
| RExIntro of int
| RExElim of formula
| REqualRefl
| REqualElim of formula * int * int
| RCut of formula

type tactic =
| TacRule of rule
| TacIntro
| TacExact of int
| TacApply of int
| TacSpecialize of int * int
| TacSplit
| TacLeft
| TacRight
| TacUse of int
| TacRefl
| TacContradiction
| TacCases of int

type step_error =
| NoGoals
| HypothesisNotFound
| FormulaMismatch
| WrongGoalShape

type 'a outcome =
| Success of 'a
| Failure of step_error

(** val rule_step_focus :
    (formula -> bool) -> rule -> goal -> goal list outcome **)

let rule_step_focus is_axiom primitive g =
  let gamma = g.assumptions in
  let c = g.conclusion in
  (match primitive with
   | RAxiom -> if is_axiom c then Success [] else Failure FormulaMismatch
   | RHypothesis n ->
     (match nth_error gamma n with
      | Some a ->
        if formula_eqb a c then Success [] else Failure FormulaMismatch
      | None -> Failure HypothesisNotFound)
   | RFalsumElim ->
     Success ({ assumptions = gamma; conclusion = Falsum } :: [])
   | RImplIntro ->
     (match c with
      | Impl (a, b) ->
        Success ({ assumptions = (a :: gamma); conclusion = b } :: [])
      | _ -> Failure WrongGoalShape)
   | RImplElim a ->
     Success ({ assumptions = gamma; conclusion = (Impl (a,
       c)) } :: ({ assumptions = gamma; conclusion = a } :: []))
   | RConjIntro ->
     (match c with
      | Conj (a, b) ->
        Success ({ assumptions = gamma; conclusion = a } :: ({ assumptions =
          gamma; conclusion = b } :: []))
      | _ -> Failure WrongGoalShape)
   | RConjElimL b ->
     Success ({ assumptions = gamma; conclusion = (Conj (c, b)) } :: [])
   | RConjElimR a ->
     Success ({ assumptions = gamma; conclusion = (Conj (a, c)) } :: [])
   | RDisjIntroL ->
     (match c with
      | Disj (a, _) -> Success ({ assumptions = gamma; conclusion = a } :: [])
      | _ -> Failure WrongGoalShape)
   | RDisjIntroR ->
     (match c with
      | Disj (_, b) -> Success ({ assumptions = gamma; conclusion = b } :: [])
      | _ -> Failure WrongGoalShape)
   | RDisjElim (a, b) ->
     Success ({ assumptions = gamma; conclusion = (Disj (a,
       b)) } :: ({ assumptions = (a :: gamma); conclusion =
       c } :: ({ assumptions = (b :: gamma); conclusion = c } :: [])))
   | RAllIntro ->
     (match c with
      | All a ->
        Success ({ assumptions = (map lift gamma); conclusion = a } :: [])
      | _ -> Failure WrongGoalShape)
   | RAllElim (a, t) ->
     if formula_eqb (instantiate t a) c
     then Success ({ assumptions = gamma; conclusion = (All a) } :: [])
     else Failure FormulaMismatch
   | RExIntro t ->
     (match c with
      | Ex a ->
        Success ({ assumptions = gamma; conclusion =
          (instantiate t a) } :: [])
      | _ -> Failure WrongGoalShape)
   | RExElim a ->
     Success ({ assumptions = gamma; conclusion = (Ex
       a) } :: ({ assumptions = (a :: (map lift gamma)); conclusion =
       (lift c) } :: []))
   | REqualRefl ->
     (match c with
      | Equal (s, t) ->
        if (=) s t then Success [] else Failure FormulaMismatch
      | _ -> Failure WrongGoalShape)
   | REqualElim (p, s, t) ->
     if formula_eqb (instantiate t p) c
     then Success ({ assumptions = gamma; conclusion = (Equal (s,
            t)) } :: ({ assumptions = gamma; conclusion =
            (instantiate s p) } :: []))
     else Failure FormulaMismatch
   | RCut a ->
     Success ({ assumptions = gamma; conclusion = a } :: ({ assumptions =
       (a :: gamma); conclusion = c } :: [])))

(** val contains_formula : formula -> formula list -> bool **)

let rec contains_formula a = function
| [] -> false
| b :: rest -> (||) (formula_eqb a b) (contains_formula a rest)

(** val contradictory : formula list -> bool **)

let rec contradictory gamma = match gamma with
| [] -> false
| a :: rest ->
  (||) (contains_formula (neg a) gamma)
    (match a with
     | Impl (p, f) ->
       (match f with
        | Falsum -> (||) (contains_formula p gamma) (contradictory rest)
        | _ -> contradictory rest)
     | _ -> contradictory rest)

(** val step_focus :
    (formula -> bool) -> tactic -> goal -> goal list outcome **)

let step_focus is_axiom command g =
  let gamma = g.assumptions in
  let c = g.conclusion in
  (match command with
   | TacRule primitive -> rule_step_focus is_axiom primitive g
   | TacIntro ->
     (match c with
      | Impl (a, b) ->
        Success ({ assumptions = (a :: gamma); conclusion = b } :: [])
      | All a ->
        Success ({ assumptions = (map lift gamma); conclusion = a } :: [])
      | _ -> Failure WrongGoalShape)
   | TacExact n ->
     (match nth_error gamma n with
      | Some a ->
        if formula_eqb a c then Success [] else Failure FormulaMismatch
      | None -> Failure HypothesisNotFound)
   | TacApply n ->
     (match nth_error gamma n with
      | Some f ->
        (match f with
         | Impl (a, b) ->
           if formula_eqb b c
           then Success ({ assumptions = gamma; conclusion = a } :: [])
           else Failure FormulaMismatch
         | _ -> Failure WrongGoalShape)
      | None -> Failure HypothesisNotFound)
   | TacSpecialize (n, t) ->
     (match nth_error gamma n with
      | Some f ->
        (match f with
         | All a ->
           Success ({ assumptions = ((instantiate t a) :: gamma);
             conclusion = c } :: [])
         | _ -> Failure WrongGoalShape)
      | None -> Failure HypothesisNotFound)
   | TacSplit ->
     (match c with
      | Conj (a, b) ->
        Success ({ assumptions = gamma; conclusion = a } :: ({ assumptions =
          gamma; conclusion = b } :: []))
      | _ -> Failure WrongGoalShape)
   | TacLeft ->
     (match c with
      | Disj (a, _) -> Success ({ assumptions = gamma; conclusion = a } :: [])
      | _ -> Failure WrongGoalShape)
   | TacRight ->
     (match c with
      | Disj (_, b) -> Success ({ assumptions = gamma; conclusion = b } :: [])
      | _ -> Failure WrongGoalShape)
   | TacUse t ->
     (match c with
      | Ex a ->
        Success ({ assumptions = gamma; conclusion =
          (instantiate t a) } :: [])
      | _ -> Failure WrongGoalShape)
   | TacRefl ->
     (match c with
      | Equal (s, t) ->
        if (=) s t then Success [] else Failure FormulaMismatch
      | _ -> Failure WrongGoalShape)
   | TacContradiction ->
     if contradictory gamma then Success [] else Failure FormulaMismatch
   | TacCases n ->
     (match nth_error gamma n with
      | Some f ->
        (match f with
         | Conj (a, b) ->
           Success ({ assumptions = (b :: (a :: gamma)); conclusion =
             c } :: [])
         | Ex a ->
           Success ({ assumptions = (a :: (map lift gamma)); conclusion =
             (lift c) } :: [])
         | _ -> Failure WrongGoalShape)
      | None -> Failure HypothesisNotFound))

(** val step :
    (formula -> bool) -> tactic -> proof_state -> proof_state outcome **)

let step is_axiom command = function
| [] -> Failure NoGoals
| g :: rest ->
  (match step_focus is_axiom command g with
   | Success generated -> Success (app generated rest)
   | Failure error -> Failure error)

(** val run :
    (formula -> bool) -> tactic list -> proof_state -> proof_state outcome **)

let rec run is_axiom commands state =
  match commands with
  | [] -> Success state
  | command :: rest ->
    (match step is_axiom command state with
     | Success next -> run is_axiom rest next
     | Failure error -> Failure error)

(** val rule_step :
    (formula -> bool) -> rule -> proof_state -> proof_state outcome **)

let rule_step is_axiom primitive = function
| [] -> Failure NoGoals
| g :: rest ->
  (match rule_step_focus is_axiom primitive g with
   | Success generated -> Success (app generated rest)
   | Failure error -> Failure error)

(** val rule_run :
    (formula -> bool) -> rule list -> proof_state -> proof_state outcome **)

let rec rule_run is_axiom rules state =
  match rules with
  | [] -> Success state
  | primitive :: rest ->
    (match rule_step is_axiom primitive state with
     | Success next -> rule_run is_axiom rest next
     | Failure error -> Failure error)
