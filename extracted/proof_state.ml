
(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val add : int -> int -> int **)

let rec add = (+)

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

module Nat =
 struct
  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (Stdlib.Int.succ n) m
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

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t -> fold_left f t (f a0 b)

type term =
| Var of int
| Const of string

(** val term_eq_dec : term -> term -> bool **)

let term_eq_dec s t =
  match s with
  | Var n -> (match t with
              | Var n0 -> (=) n n0
              | Const _ -> false)
  | Const s0 -> (match t with
                 | Var _ -> false
                 | Const s1 -> (=) s0 s1)

(** val term_eqb : term -> term -> bool **)

let term_eqb s t =
  if term_eq_dec s t then true else false

type formula =
| Falsum
| Equal of term * term
| Member of term * term
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
  | Equal (t, t0) ->
    (match x with
     | Equal (t1, t2) -> if term_eq_dec t t1 then term_eq_dec t0 t2 else false
     | _ -> false)
  | Member (t, t0) ->
    (match x with
     | Member (t1, t2) ->
       if term_eq_dec t t1 then term_eq_dec t0 t2 else false
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

(** val iff : formula -> formula -> formula **)

let iff a b =
  Conj ((Impl (a, b)), (Impl (b, a)))

(** val up : (int -> int) -> int -> int **)

let up xi n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun k -> Stdlib.Int.succ (xi k))
    n

(** val rename_term : (int -> int) -> term -> term **)

let rename_term xi = function
| Var n -> Var (xi n)
| Const name -> Const name

(** val rename : (int -> int) -> formula -> formula **)

let rec rename xi = function
| Falsum -> Falsum
| Equal (x, y) -> Equal ((rename_term xi x), (rename_term xi y))
| Member (x, y) -> Member ((rename_term xi x), (rename_term xi y))
| Conj (b, c) -> Conj ((rename xi b), (rename xi c))
| Disj (b, c) -> Disj ((rename xi b), (rename xi c))
| Impl (b, c) -> Impl ((rename xi b), (rename xi c))
| All b -> All (rename (up xi) b)
| Ex b -> Ex (rename (up xi) b)

(** val lift : formula -> formula **)

let lift a =
  rename (fun x -> Stdlib.Int.succ x) a

(** val lift_term : term -> term **)

let lift_term t =
  rename_term (fun x -> Stdlib.Int.succ x) t

(** val up_substitution : (int -> term) -> int -> term **)

let up_substitution sigma n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Var 0)
    (fun k -> lift_term (sigma k))
    n

(** val substitute_term : (int -> term) -> term -> term **)

let substitute_term sigma = function
| Var n -> sigma n
| Const name -> Const name

(** val substitute : (int -> term) -> formula -> formula **)

let rec substitute sigma = function
| Falsum -> Falsum
| Equal (x, y) -> Equal ((substitute_term sigma x), (substitute_term sigma y))
| Member (x, y) ->
  Member ((substitute_term sigma x), (substitute_term sigma y))
| Conj (b, c) -> Conj ((substitute sigma b), (substitute sigma c))
| Disj (b, c) -> Disj ((substitute sigma b), (substitute sigma c))
| Impl (b, c) -> Impl ((substitute sigma b), (substitute sigma c))
| All b -> All (substitute (up_substitution sigma) b)
| Ex b -> Ex (substitute (up_substitution sigma) b)

(** val subst_zero : term -> int -> term **)

let subst_zero t n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> t)
    (fun k -> Var k)
    n

(** val instantiate : term -> formula -> formula **)

let instantiate t a =
  substitute (subst_zero t) a

type goal = { assumptions : formula list; conclusion : formula }

type proof_state = goal list

(** val start : formula -> proof_state **)

let start c =
  { assumptions = []; conclusion = c } :: []

(** val state_goals : proof_state -> goal list **)

let state_goals state =
  state

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
| RAllElim of formula * term
| RExIntro of term
| RExElim of formula
| REqualRefl
| REqualElim of formula * term * term
| RCut of formula

type tactic =
| TacRule of rule
| TacIntro
| TacExact of int
| TacApply of int
| TacSpecialize of int * term
| TacSplit
| TacLeft
| TacRight
| TacUse of term
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
        if term_eqb s t then Success [] else Failure FormulaMismatch
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
        if term_eqb s t then Success [] else Failure FormulaMismatch
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

(** val empty_set_axiom : formula **)

let empty_set_axiom =
  Ex (All (neg (Member ((Var 0), (Var (Stdlib.Int.succ 0))))))

(** val extensionality_axiom : formula **)

let extensionality_axiom =
  All (All (Impl ((All
    (iff (Member ((Var 0), (Var (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
      (Member ((Var 0), (Var (Stdlib.Int.succ 0)))))), (Equal ((Var
    (Stdlib.Int.succ 0)), (Var 0))))))

(** val pairing_axiom : formula **)

let pairing_axiom =
  All (All (Ex (All
    (iff (Member ((Var 0), (Var (Stdlib.Int.succ 0)))) (Disj ((Equal ((Var
      0), (Var (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))),
      (Equal ((Var 0), (Var (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))

(** val union_axiom : formula **)

let union_axiom =
  All (Ex (All
    (iff (Member ((Var 0), (Var (Stdlib.Int.succ 0)))) (Ex (Conj ((Member
      ((Var (Stdlib.Int.succ 0)), (Var 0))), (Member ((Var 0), (Var
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))

(** val power_set_axiom : formula **)

let power_set_axiom =
  All (Ex (All
    (iff (Member ((Var 0), (Var (Stdlib.Int.succ 0)))) (All (Impl ((Member
      ((Var 0), (Var (Stdlib.Int.succ 0)))), (Member ((Var 0), (Var
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))

(** val foundation_axiom : formula **)

let foundation_axiom =
  All (Impl ((Ex (Member ((Var 0), (Var (Stdlib.Int.succ 0))))), (Ex (Conj
    ((Member ((Var 0), (Var (Stdlib.Int.succ 0)))), (All (Impl ((Member ((Var
    0), (Var (Stdlib.Int.succ 0)))),
    (neg (Member ((Var 0), (Var (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))

(** val infinity_axiom : formula **)

let infinity_axiom =
  Ex (Conj ((Ex (Conj ((All
    (neg (Member ((Var 0), (Var (Stdlib.Int.succ 0)))))), (Member ((Var 0),
    (Var (Stdlib.Int.succ 0))))))), (All (Impl ((Member ((Var 0), (Var
    (Stdlib.Int.succ 0)))), (Ex (Conj ((Member ((Var 0), (Var
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (All
    (iff (Member ((Var 0), (Var (Stdlib.Int.succ 0)))) (Disj ((Member ((Var
      0), (Var (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (Equal ((Var 0),
      (Var (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))

(** val insert_subset : int -> int **)

let insert_subset n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun k -> Stdlib.Int.succ (Stdlib.Int.succ k))
    n

(** val separation_instance : formula -> formula **)

let separation_instance p =
  All (Ex (All
    (iff (Member ((Var 0), (Var (Stdlib.Int.succ 0)))) (Conj ((Member ((Var
      0), (Var (Stdlib.Int.succ (Stdlib.Int.succ 0))))),
      (rename insert_subset p))))))

(** val replacement_alternate : int -> int **)

let replacement_alternate n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ (Stdlib.Int.succ 0))
      (fun k -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ k)))
      n0)
    n

(** val replacement_image : int -> int **)

let replacement_image n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Stdlib.Int.succ 0)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun k -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ k))))
      n0)
    n

(** val replacement_instance : formula -> formula **)

let replacement_instance p =
  Impl ((All (Ex (Conj (p, (All (Impl ((rename replacement_alternate p),
    (Equal ((Var 0), (Var (Stdlib.Int.succ 0))))))))))), (All (Ex (All
    (iff (Member ((Var 0), (Var (Stdlib.Int.succ 0)))) (Ex (Conj ((Member
      ((Var 0), (Var (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0)))))), (rename replacement_image p)))))))))

(** val choice_axiom : formula **)

let choice_axiom =
  All (Impl ((All (Impl ((Member ((Var 0), (Var (Stdlib.Int.succ 0)))), (Ex
    (Member ((Var 0), (Var (Stdlib.Int.succ 0)))))))), (Ex (All (Impl
    ((Member ((Var 0), (Var (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (Ex
    (Conj ((Conj ((Member ((Var 0), (Var (Stdlib.Int.succ 0)))), (Member
    ((Var 0), (Var (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (All (Impl
    ((Conj ((Member ((Var 0), (Var (Stdlib.Int.succ (Stdlib.Int.succ 0))))),
    (Member ((Var 0), (Var (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (Equal ((Var 0), (Var (Stdlib.Int.succ 0))))))))))))))))

type named_formula =
| NFalsum
| NEqual of string * string
| NMember of string * string
| NConj of named_formula * named_formula
| NDisj of named_formula * named_formula
| NImpl of named_formula * named_formula
| NNeg of named_formula
| NIff of named_formula * named_formula
| NAll of string * named_formula
| NEx of string * named_formula

type named_hypothesis = { named_hypothesis_name : string;
                          named_hypothesis_formula : named_formula }

type named_goal = { named_assumptions : named_hypothesis list;
                    named_conclusion : named_formula }

type named_error =
| NCoreError of step_error
| NUnknownVariable of string
| NHypothesisNotFound of string
| NHypothesisAlreadyUsed of string
| NVariableAlreadyUsed of string
| NMetadataMismatch
| NWrongNamedShape

type 'a named_result =
| NOk of 'a
| NError of named_error

(** val named_bind :
    'a1 named_result -> ('a1 -> 'a2 named_result) -> 'a2 named_result **)

let named_bind result next =
  match result with
  | NOk value -> next value
  | NError error -> NError error

(** val string_mem : string -> string list -> bool **)

let rec string_mem name = function
| [] -> false
| candidate :: rest ->
  if (=) name candidate then true else string_mem name rest

(** val string_index_from : string -> int -> string list -> int option **)

let rec string_index_from name index = function
| [] -> None
| candidate :: rest ->
  if (=) name candidate
  then Some index
  else string_index_from name (Stdlib.Int.succ index) rest

(** val string_index : string -> string list -> int option **)

let string_index name names =
  string_index_from name 0 names

(** val add_name : string list -> string -> string list **)

let add_name names name =
  if string_mem name names then names else app names (name :: [])

(** val remove_name : string -> string list -> string list **)

let rec remove_name name = function
| [] -> []
| candidate :: rest ->
  if (=) name candidate
  then remove_name name rest
  else candidate :: (remove_name name rest)

(** val merge_names : string list -> string list -> string list **)

let rec merge_names left = function
| [] -> left
| name :: rest -> merge_names (add_name left name) rest

(** val filter_environment : string list -> string list -> string list **)

let rec filter_environment excluded = function
| [] -> []
| name :: rest ->
  if string_mem name excluded
  then filter_environment excluded rest
  else name :: (filter_environment excluded rest)

(** val shared_name : string list -> string list -> string option **)

let rec shared_name left right =
  match left with
  | [] -> None
  | name :: rest ->
    if string_mem name right then Some name else shared_name rest right

(** val add_environment_name :
    string list -> string list -> string -> string list **)

let add_environment_name constants environment name =
  if string_mem name constants then environment else add_name environment name

(** val named_free_variables : named_formula -> string list **)

let rec named_free_variables = function
| NFalsum -> []
| NEqual (first, second) -> add_name (first :: []) second
| NMember (first, second) -> add_name (first :: []) second
| NConj (first, second) ->
  merge_names (named_free_variables first) (named_free_variables second)
| NDisj (first, second) ->
  merge_names (named_free_variables first) (named_free_variables second)
| NImpl (first, second) ->
  merge_names (named_free_variables first) (named_free_variables second)
| NNeg body -> named_free_variables body
| NIff (first, second) ->
  merge_names (named_free_variables first) (named_free_variables second)
| NAll (binder, body) -> remove_name binder (named_free_variables body)
| NEx (binder, body) -> remove_name binder (named_free_variables body)

(** val named_binder_names : named_formula -> string list **)

let rec named_binder_names = function
| NConj (first, second) ->
  app (named_binder_names first) (named_binder_names second)
| NDisj (first, second) ->
  app (named_binder_names first) (named_binder_names second)
| NImpl (first, second) ->
  app (named_binder_names first) (named_binder_names second)
| NNeg body -> named_binder_names body
| NIff (first, second) ->
  app (named_binder_names first) (named_binder_names second)
| NAll (binder, body) -> binder :: (named_binder_names body)
| NEx (binder, body) -> binder :: (named_binder_names body)
| _ -> []

(** val extend_environment :
    string list -> string list -> named_formula -> string list **)

let extend_environment constants environment source =
  fold_left (add_environment_name constants) (named_free_variables source)
    environment

(** val extend_environments :
    string list -> string list -> named_formula list -> string list **)

let extend_environments constants environment sources =
  fold_left (extend_environment constants) sources environment

(** val variable_index :
    string list -> string list -> string -> int named_result **)

let variable_index bound environment name =
  match string_index name bound with
  | Some index -> NOk index
  | None ->
    (match string_index name environment with
     | Some index -> NOk (add (length bound) index)
     | None -> NError (NUnknownVariable name))

(** val elaborate_term :
    string list -> string list -> string list -> string -> term named_result **)

let elaborate_term constants bound environment name =
  match variable_index bound environment name with
  | NOk index -> NOk (Var index)
  | NError _ ->
    if string_mem name constants
    then NOk (Const name)
    else NError (NUnknownVariable name)

(** val elaborate :
    string list -> string list -> string list -> named_formula -> formula
    named_result **)

let rec elaborate constants bound environment = function
| NFalsum -> NOk Falsum
| NEqual (first, second) ->
  named_bind (elaborate_term constants bound environment first)
    (fun first_term ->
    named_bind (elaborate_term constants bound environment second)
      (fun second_term -> NOk (Equal (first_term, second_term))))
| NMember (first, second) ->
  named_bind (elaborate_term constants bound environment first)
    (fun first_term ->
    named_bind (elaborate_term constants bound environment second)
      (fun second_term -> NOk (Member (first_term, second_term))))
| NConj (first, second) ->
  named_bind (elaborate constants bound environment first)
    (fun first_formula ->
    named_bind (elaborate constants bound environment second)
      (fun second_formula -> NOk (Conj (first_formula, second_formula))))
| NDisj (first, second) ->
  named_bind (elaborate constants bound environment first)
    (fun first_formula ->
    named_bind (elaborate constants bound environment second)
      (fun second_formula -> NOk (Disj (first_formula, second_formula))))
| NImpl (first, second) ->
  named_bind (elaborate constants bound environment first)
    (fun first_formula ->
    named_bind (elaborate constants bound environment second)
      (fun second_formula -> NOk (Impl (first_formula, second_formula))))
| NNeg body ->
  named_bind (elaborate constants bound environment body)
    (fun body_formula -> NOk (neg body_formula))
| NIff (first, second) ->
  named_bind (elaborate constants bound environment first)
    (fun first_formula ->
    named_bind (elaborate constants bound environment second)
      (fun second_formula -> NOk (iff first_formula second_formula)))
| NAll (binder, body) ->
  if string_mem binder constants
  then NError (NVariableAlreadyUsed binder)
  else named_bind (elaborate constants (binder :: bound) environment body)
         (fun body_formula -> NOk (All body_formula))
| NEx (binder, body) ->
  if string_mem binder constants
  then NError (NVariableAlreadyUsed binder)
  else named_bind (elaborate constants (binder :: bound) environment body)
         (fun body_formula -> NOk (Ex body_formula))

(** val elaborate_closed :
    string list -> named_formula -> formula named_result **)

let elaborate_closed constants source =
  elaborate constants []
    (filter_environment constants (named_free_variables source)) source

(** val nth_name :
    string list -> string list -> int -> string named_result **)

let nth_name bound environment index =
  if Nat.ltb index (length bound)
  then (match nth_error bound index with
        | Some name -> NOk name
        | None -> NError NMetadataMismatch)
  else (match nth_error environment (sub index (length bound)) with
        | Some name -> NOk name
        | None -> NError NMetadataMismatch)

(** val reify_term :
    string list -> string list -> term -> string named_result **)

let reify_term bound environment = function
| Var index -> nth_name bound environment index
| Const name -> NOk name

(** val fresh_string_with_fuel : int -> string -> string list -> string **)

let rec fresh_string_with_fuel fuel candidate used =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> candidate)
    (fun remaining ->
    if string_mem candidate used
    then fresh_string_with_fuel remaining ((^) candidate "'") used
    else candidate)
    fuel

(** val fresh_string : string -> string list -> string **)

let fresh_string base used =
  fresh_string_with_fuel (Stdlib.Int.succ (length used)) base used

(** val choose_binder :
    string list -> string list -> string list -> string list ->
    string * string list **)

let choose_binder constants bound environment preferred =
  let used = app constants (app bound environment) in
  (match preferred with
   | [] -> ((fresh_string "x" used), [])
   | candidate :: rest ->
     if string_mem candidate used
     then ((fresh_string "x" used), rest)
     else (candidate, rest))

(** val reify_with_names :
    string list -> string list -> string list -> string list -> formula ->
    (named_formula * string list) named_result **)

let rec reify_with_names constants bound environment preferred = function
| Falsum -> NOk (NFalsum, preferred)
| Equal (first, second) ->
  named_bind (reify_term bound environment first) (fun first_name ->
    named_bind (reify_term bound environment second) (fun second_name -> NOk
      ((NEqual (first_name, second_name)), preferred)))
| Member (first, second) ->
  named_bind (reify_term bound environment first) (fun first_name ->
    named_bind (reify_term bound environment second) (fun second_name -> NOk
      ((NMember (first_name, second_name)), preferred)))
| Conj (first, second) ->
  (match first with
   | Falsum ->
     named_bind
       (reify_with_names constants bound environment preferred first)
       (fun pat ->
       let (first_named, after_first) = pat in
       named_bind
         (reify_with_names constants bound environment after_first second)
         (fun pat0 ->
         let (second_named, after_second) = pat0 in
         NOk ((NConj (first_named, second_named)), after_second)))
   | Equal (_, _) ->
     named_bind
       (reify_with_names constants bound environment preferred first)
       (fun pat ->
       let (first_named, after_first) = pat in
       named_bind
         (reify_with_names constants bound environment after_first second)
         (fun pat0 ->
         let (second_named, after_second) = pat0 in
         NOk ((NConj (first_named, second_named)), after_second)))
   | Member (_, _) ->
     named_bind
       (reify_with_names constants bound environment preferred first)
       (fun pat ->
       let (first_named, after_first) = pat in
       named_bind
         (reify_with_names constants bound environment after_first second)
         (fun pat0 ->
         let (second_named, after_second) = pat0 in
         NOk ((NConj (first_named, second_named)), after_second)))
   | Conj (_, _) ->
     named_bind
       (reify_with_names constants bound environment preferred first)
       (fun pat ->
       let (first_named, after_first) = pat in
       named_bind
         (reify_with_names constants bound environment after_first second)
         (fun pat0 ->
         let (second_named, after_second) = pat0 in
         NOk ((NConj (first_named, second_named)), after_second)))
   | Disj (_, _) ->
     named_bind
       (reify_with_names constants bound environment preferred first)
       (fun pat ->
       let (first_named, after_first) = pat in
       named_bind
         (reify_with_names constants bound environment after_first second)
         (fun pat0 ->
         let (second_named, after_second) = pat0 in
         NOk ((NConj (first_named, second_named)), after_second)))
   | Impl (first_left, first_right) ->
     (match second with
      | Falsum ->
        named_bind
          (reify_with_names constants bound environment preferred first)
          (fun pat ->
          let (first_named, after_first) = pat in
          named_bind
            (reify_with_names constants bound environment after_first second)
            (fun pat0 ->
            let (second_named, after_second) = pat0 in
            NOk ((NConj (first_named, second_named)), after_second)))
      | Equal (_, _) ->
        named_bind
          (reify_with_names constants bound environment preferred first)
          (fun pat ->
          let (first_named, after_first) = pat in
          named_bind
            (reify_with_names constants bound environment after_first second)
            (fun pat0 ->
            let (second_named, after_second) = pat0 in
            NOk ((NConj (first_named, second_named)), after_second)))
      | Member (_, _) ->
        named_bind
          (reify_with_names constants bound environment preferred first)
          (fun pat ->
          let (first_named, after_first) = pat in
          named_bind
            (reify_with_names constants bound environment after_first second)
            (fun pat0 ->
            let (second_named, after_second) = pat0 in
            NOk ((NConj (first_named, second_named)), after_second)))
      | Conj (_, _) ->
        named_bind
          (reify_with_names constants bound environment preferred first)
          (fun pat ->
          let (first_named, after_first) = pat in
          named_bind
            (reify_with_names constants bound environment after_first second)
            (fun pat0 ->
            let (second_named, after_second) = pat0 in
            NOk ((NConj (first_named, second_named)), after_second)))
      | Disj (_, _) ->
        named_bind
          (reify_with_names constants bound environment preferred first)
          (fun pat ->
          let (first_named, after_first) = pat in
          named_bind
            (reify_with_names constants bound environment after_first second)
            (fun pat0 ->
            let (second_named, after_second) = pat0 in
            NOk ((NConj (first_named, second_named)), after_second)))
      | Impl (second_left, second_right) ->
        if (&&) (formula_eqb first_left second_right)
             (formula_eqb first_right second_left)
        then named_bind
               (reify_with_names constants bound environment preferred
                 first_left) (fun pat ->
               let (left_named, after_left) = pat in
               named_bind
                 (reify_with_names constants bound environment after_left
                   first_right) (fun pat0 ->
                 let (right_named, after_right) = pat0 in
                 NOk ((NIff (left_named, right_named)), after_right)))
        else named_bind
               (reify_with_names constants bound environment preferred first)
               (fun pat ->
               let (first_named, after_first) = pat in
               named_bind
                 (reify_with_names constants bound environment after_first
                   second) (fun pat0 ->
                 let (second_named, after_second) = pat0 in
                 NOk ((NConj (first_named, second_named)), after_second)))
      | All _ ->
        named_bind
          (reify_with_names constants bound environment preferred first)
          (fun pat ->
          let (first_named, after_first) = pat in
          named_bind
            (reify_with_names constants bound environment after_first second)
            (fun pat0 ->
            let (second_named, after_second) = pat0 in
            NOk ((NConj (first_named, second_named)), after_second)))
      | Ex _ ->
        named_bind
          (reify_with_names constants bound environment preferred first)
          (fun pat ->
          let (first_named, after_first) = pat in
          named_bind
            (reify_with_names constants bound environment after_first second)
            (fun pat0 ->
            let (second_named, after_second) = pat0 in
            NOk ((NConj (first_named, second_named)), after_second))))
   | All _ ->
     named_bind
       (reify_with_names constants bound environment preferred first)
       (fun pat ->
       let (first_named, after_first) = pat in
       named_bind
         (reify_with_names constants bound environment after_first second)
         (fun pat0 ->
         let (second_named, after_second) = pat0 in
         NOk ((NConj (first_named, second_named)), after_second)))
   | Ex _ ->
     named_bind
       (reify_with_names constants bound environment preferred first)
       (fun pat ->
       let (first_named, after_first) = pat in
       named_bind
         (reify_with_names constants bound environment after_first second)
         (fun pat0 ->
         let (second_named, after_second) = pat0 in
         NOk ((NConj (first_named, second_named)), after_second))))
| Disj (first, second) ->
  named_bind (reify_with_names constants bound environment preferred first)
    (fun pat ->
    let (first_named, after_first) = pat in
    named_bind
      (reify_with_names constants bound environment after_first second)
      (fun pat0 ->
      let (second_named, after_second) = pat0 in
      NOk ((NDisj (first_named, second_named)), after_second)))
| Impl (first, second) ->
  (match second with
   | Falsum ->
     named_bind
       (reify_with_names constants bound environment preferred first)
       (fun pat ->
       let (body_named, after_body) = pat in
       NOk ((NNeg body_named), after_body))
   | Equal (_, _) ->
     named_bind
       (reify_with_names constants bound environment preferred first)
       (fun pat ->
       let (first_named, after_first) = pat in
       named_bind
         (reify_with_names constants bound environment after_first second)
         (fun pat0 ->
         let (second_named, after_second) = pat0 in
         NOk ((NImpl (first_named, second_named)), after_second)))
   | Member (_, _) ->
     named_bind
       (reify_with_names constants bound environment preferred first)
       (fun pat ->
       let (first_named, after_first) = pat in
       named_bind
         (reify_with_names constants bound environment after_first second)
         (fun pat0 ->
         let (second_named, after_second) = pat0 in
         NOk ((NImpl (first_named, second_named)), after_second)))
   | Conj (_, _) ->
     named_bind
       (reify_with_names constants bound environment preferred first)
       (fun pat ->
       let (first_named, after_first) = pat in
       named_bind
         (reify_with_names constants bound environment after_first second)
         (fun pat0 ->
         let (second_named, after_second) = pat0 in
         NOk ((NImpl (first_named, second_named)), after_second)))
   | Disj (_, _) ->
     named_bind
       (reify_with_names constants bound environment preferred first)
       (fun pat ->
       let (first_named, after_first) = pat in
       named_bind
         (reify_with_names constants bound environment after_first second)
         (fun pat0 ->
         let (second_named, after_second) = pat0 in
         NOk ((NImpl (first_named, second_named)), after_second)))
   | Impl (_, _) ->
     named_bind
       (reify_with_names constants bound environment preferred first)
       (fun pat ->
       let (first_named, after_first) = pat in
       named_bind
         (reify_with_names constants bound environment after_first second)
         (fun pat0 ->
         let (second_named, after_second) = pat0 in
         NOk ((NImpl (first_named, second_named)), after_second)))
   | All _ ->
     named_bind
       (reify_with_names constants bound environment preferred first)
       (fun pat ->
       let (first_named, after_first) = pat in
       named_bind
         (reify_with_names constants bound environment after_first second)
         (fun pat0 ->
         let (second_named, after_second) = pat0 in
         NOk ((NImpl (first_named, second_named)), after_second)))
   | Ex _ ->
     named_bind
       (reify_with_names constants bound environment preferred first)
       (fun pat ->
       let (first_named, after_first) = pat in
       named_bind
         (reify_with_names constants bound environment after_first second)
         (fun pat0 ->
         let (second_named, after_second) = pat0 in
         NOk ((NImpl (first_named, second_named)), after_second))))
| All body ->
  let (binder, after_binder) =
    choose_binder constants bound environment preferred
  in
  named_bind
    (reify_with_names constants (binder :: bound) environment after_binder
      body) (fun pat ->
    let (body_named, after_body) = pat in
    NOk ((NAll (binder, body_named)), after_body))
| Ex body ->
  let (binder, after_binder) =
    choose_binder constants bound environment preferred
  in
  named_bind
    (reify_with_names constants (binder :: bound) environment after_binder
      body) (fun pat ->
    let (body_named, after_body) = pat in
    NOk ((NEx (binder, body_named)), after_body))

(** val reify :
    string list -> string list -> string list -> formula -> named_formula
    named_result **)

let reify constants environment preferred source =
  named_bind (reify_with_names constants [] environment preferred source)
    (fun pat -> let (named, _) = pat in NOk named)

type goal_metadata = { metadata_hypothesis_names : string list;
                       metadata_assumption_binders : string list list;
                       metadata_conclusion_binders : string list;
                       metadata_environment : string list;
                       metadata_constants : string list }

type named_state = { named_kernel_state : proof_state;
                     named_goal_metadata : goal_metadata list }

(** val initial_metadata : string list -> named_formula -> goal_metadata **)

let initial_metadata constants source =
  { metadata_hypothesis_names = []; metadata_assumption_binders = [];
    metadata_conclusion_binders = (named_binder_names source);
    metadata_environment =
    (filter_environment constants (named_free_variables source));
    metadata_constants = constants }

(** val named_start_with_constants :
    string list -> named_formula -> named_state named_result **)

let named_start_with_constants constants source =
  named_bind (elaborate_closed constants source) (fun core -> NOk
    { named_kernel_state = (start core); named_goal_metadata =
    ((initial_metadata constants source) :: []) })

(** val named_start : named_formula -> named_state named_result **)

let named_start source =
  named_start_with_constants [] source

(** val reify_assumptions :
    string list -> string list -> string list -> string list list -> formula
    list -> named_hypothesis list named_result **)

let rec reify_assumptions constants environment names binders sources =
  match names with
  | [] ->
    (match binders with
     | [] ->
       (match sources with
        | [] -> NOk []
        | _ :: _ -> NError NMetadataMismatch)
     | _ :: _ -> NError NMetadataMismatch)
  | name :: name_rest ->
    (match binders with
     | [] -> NError NMetadataMismatch
     | preferred :: binder_rest ->
       (match sources with
        | [] -> NError NMetadataMismatch
        | source :: source_rest ->
          named_bind (reify constants environment preferred source)
            (fun named_source ->
            named_bind
              (reify_assumptions constants environment name_rest binder_rest
                source_rest) (fun rest -> NOk ({ named_hypothesis_name =
              name; named_hypothesis_formula = named_source } :: rest)))))

(** val reify_goal : goal_metadata -> goal -> named_goal named_result **)

let reify_goal metadata source =
  named_bind
    (reify_assumptions metadata.metadata_constants
      metadata.metadata_environment metadata.metadata_hypothesis_names
      metadata.metadata_assumption_binders source.assumptions)
    (fun named_context ->
    named_bind
      (reify metadata.metadata_constants metadata.metadata_environment
        metadata.metadata_conclusion_binders source.conclusion)
      (fun named_target -> NOk { named_assumptions = named_context;
      named_conclusion = named_target }))

(** val reify_goals :
    goal_metadata list -> goal list -> named_goal list named_result **)

let rec reify_goals metadata sources =
  match metadata with
  | [] ->
    (match sources with
     | [] -> NOk []
     | _ :: _ -> NError NMetadataMismatch)
  | names :: name_rest ->
    (match sources with
     | [] -> NError NMetadataMismatch
     | source :: source_rest ->
       named_bind (reify_goal names source) (fun named_source ->
         named_bind (reify_goals name_rest source_rest) (fun rest -> NOk
           (named_source :: rest))))

(** val named_goals : named_state -> named_goal list named_result **)

let named_goals state =
  reify_goals state.named_goal_metadata (state_goals state.named_kernel_state)

(** val named_solved : named_state -> bool **)

let named_solved state =
  match state.named_kernel_state with
  | [] -> true
  | _ :: _ -> false

type named_fixed_axiom =
| NEmptySet
| NExtensionality
| NPairing
| NUnion
| NPowerSet
| NFoundation
| NInfinity
| NChoice

type named_axiom =
| NFixedAxiom of named_fixed_axiom
| NSeparationAxiom of string * string * named_formula
| NReplacementAxiom of string * string * named_formula

(** val fixed_axiom_formula : named_fixed_axiom -> formula **)

let fixed_axiom_formula = function
| NEmptySet -> empty_set_axiom
| NExtensionality -> extensionality_axiom
| NPairing -> pairing_axiom
| NUnion -> union_axiom
| NPowerSet -> power_set_axiom
| NFoundation -> foundation_axiom
| NInfinity -> infinity_axiom
| NChoice -> choice_axiom

(** val elaborate_schema_predicate :
    string list -> string list -> string list -> named_formula -> formula
    named_result **)

let elaborate_schema_predicate constants binders environment predicate =
  match shared_name binders constants with
  | Some name -> NError (NVariableAlreadyUsed name)
  | None ->
    elaborate constants binders (filter_environment binders environment)
      predicate

(** val compile_axiom :
    string list -> string list -> named_axiom -> formula named_result **)

let compile_axiom constants environment = function
| NFixedAxiom kind -> NOk (fixed_axiom_formula kind)
| NSeparationAxiom (source, element, predicate) ->
  named_bind
    (elaborate_schema_predicate constants (element :: (source :: []))
      environment predicate) (fun core_predicate -> NOk
    (separation_instance core_predicate))
| NReplacementAxiom (input, output, predicate) ->
  named_bind
    (elaborate_schema_predicate constants (output :: (input :: []))
      environment predicate) (fun core_predicate -> NOk
    (replacement_instance core_predicate))

(** val compile_axioms :
    string list -> string list -> named_axiom list -> formula list
    named_result **)

let rec compile_axioms constants environment = function
| [] -> NOk []
| axiom :: rest ->
  named_bind (compile_axiom constants environment axiom) (fun core_axiom ->
    named_bind (compile_axioms constants environment rest) (fun core_rest ->
      NOk (core_axiom :: core_rest)))

(** val formula_in : formula -> formula list -> bool **)

let rec formula_in candidate = function
| [] -> false
| axiom :: rest ->
  (||) (formula_eqb axiom candidate) (formula_in candidate rest)

type named_rule =
| NRAxiom
| NRHypothesis of string
| NRFalsumElim
| NRImplIntro of string
| NRImplElim of named_formula
| NRConjIntro
| NRConjElimL of named_formula
| NRConjElimR of named_formula
| NRDisjIntroL
| NRDisjIntroR
| NRDisjElim of named_formula * named_formula * string * string
| NRAllIntro of string
| NRAllElim of string * named_formula
| NRExIntro of string
| NRExElim of string * string * named_formula
| NREqualRefl
| NREqualElim of string * string * named_formula
| NRCut of string * named_formula

type rule_plan = { planned_rule : rule;
                   planned_generated_metadata : goal_metadata list;
                   planned_environment : string list }

(** val metadata_with_conclusion :
    goal_metadata -> string list -> string list -> goal_metadata **)

let metadata_with_conclusion metadata binders environment =
  { metadata_hypothesis_names = metadata.metadata_hypothesis_names;
    metadata_assumption_binders = metadata.metadata_assumption_binders;
    metadata_conclusion_binders = binders; metadata_environment =
    environment; metadata_constants = metadata.metadata_constants }

(** val metadata_with_hypothesis :
    goal_metadata -> string -> string list -> string list -> string list ->
    goal_metadata **)

let metadata_with_hypothesis metadata hypothesis hypothesis_binders conclusion_binders environment =
  { metadata_hypothesis_names =
    (hypothesis :: metadata.metadata_hypothesis_names);
    metadata_assumption_binders =
    (hypothesis_binders :: metadata.metadata_assumption_binders);
    metadata_conclusion_binders = conclusion_binders; metadata_environment =
    environment; metadata_constants = metadata.metadata_constants }

(** val ensure_hypothesis_fresh :
    goal_metadata -> string -> unit named_result **)

let ensure_hypothesis_fresh metadata name =
  if string_mem name metadata.metadata_hypothesis_names
  then NError (NHypothesisAlreadyUsed name)
  else NOk ()

(** val ensure_variable_fresh :
    goal_metadata -> string -> unit named_result **)

let ensure_variable_fresh metadata name =
  if (||) (string_mem name metadata.metadata_constants)
       (string_mem name metadata.metadata_environment)
  then NError (NVariableAlreadyUsed name)
  else NOk ()

(** val hypothesis_index : goal_metadata -> string -> int named_result **)

let hypothesis_index metadata name =
  match string_index name metadata.metadata_hypothesis_names with
  | Some index -> NOk index
  | None -> NError (NHypothesisNotFound name)

(** val find_named_hypothesis :
    string -> named_hypothesis list -> named_formula option **)

let rec find_named_hypothesis name = function
| [] -> None
| hypothesis :: rest ->
  if (=) name hypothesis.named_hypothesis_name
  then Some hypothesis.named_hypothesis_formula
  else find_named_hypothesis name rest

(** val elaborate_in_environment :
    string list -> string list -> named_formula -> formula named_result **)

let elaborate_in_environment constants environment source =
  elaborate constants [] environment source

(** val term_index :
    string list -> string list -> string -> term named_result **)

let term_index constants environment source =
  elaborate_term constants [] environment source

(** val plan_named_rule :
    goal_metadata -> named_goal -> named_rule -> rule_plan named_result **)

let plan_named_rule metadata view primitive =
  let constants = metadata.metadata_constants in
  let environment = metadata.metadata_environment in
  let target = view.named_conclusion in
  (match primitive with
   | NRAxiom ->
     NOk { planned_rule = RAxiom; planned_generated_metadata = [];
       planned_environment = environment }
   | NRHypothesis hypothesis ->
     named_bind (hypothesis_index metadata hypothesis) (fun index -> NOk
       { planned_rule = (RHypothesis index); planned_generated_metadata = [];
       planned_environment = environment })
   | NRFalsumElim ->
     NOk { planned_rule = RFalsumElim; planned_generated_metadata =
       ((metadata_with_conclusion metadata [] environment) :: []);
       planned_environment = environment }
   | NRImplIntro hypothesis ->
     named_bind (ensure_hypothesis_fresh metadata hypothesis) (fun _ ->
       match target with
       | NImpl (premise, conclusion0) ->
         NOk { planned_rule = RImplIntro; planned_generated_metadata =
           ((metadata_with_hypothesis metadata hypothesis
              (named_binder_names premise) (named_binder_names conclusion0)
              environment) :: []); planned_environment = environment }
       | NNeg premise ->
         NOk { planned_rule = RImplIntro; planned_generated_metadata =
           ((metadata_with_hypothesis metadata hypothesis
              (named_binder_names premise) [] environment) :: []);
           planned_environment = environment }
       | _ -> NError NWrongNamedShape)
   | NRImplElim premise ->
     let next_environment = extend_environment constants environment premise
     in
     named_bind (elaborate_in_environment constants next_environment premise)
       (fun core_premise -> NOk { planned_rule = (RImplElim core_premise);
       planned_generated_metadata =
       ((metadata_with_conclusion metadata
          (app (named_binder_names premise)
            metadata.metadata_conclusion_binders) next_environment) :: (
       (metadata_with_conclusion metadata (named_binder_names premise)
         next_environment) :: [])); planned_environment = next_environment })
   | NRConjIntro ->
     (match target with
      | NConj (first, second) ->
        NOk { planned_rule = RConjIntro; planned_generated_metadata =
          ((metadata_with_conclusion metadata (named_binder_names first)
             environment) :: ((metadata_with_conclusion metadata
                                (named_binder_names second) environment) :: []));
          planned_environment = environment }
      | NIff (first, second) ->
        NOk { planned_rule = RConjIntro; planned_generated_metadata =
          ((metadata_with_conclusion metadata
             (named_binder_names (NImpl (first, second))) environment) :: (
          (metadata_with_conclusion metadata
            (named_binder_names (NImpl (second, first))) environment) :: []));
          planned_environment = environment }
      | _ -> NError NWrongNamedShape)
   | NRConjElimL extra ->
     let next_environment = extend_environment constants environment extra in
     named_bind (elaborate_in_environment constants next_environment extra)
       (fun core_extra -> NOk { planned_rule = (RConjElimL core_extra);
       planned_generated_metadata =
       ((metadata_with_conclusion metadata
          (app metadata.metadata_conclusion_binders
            (named_binder_names extra)) next_environment) :: []);
       planned_environment = next_environment })
   | NRConjElimR extra ->
     let next_environment = extend_environment constants environment extra in
     named_bind (elaborate_in_environment constants next_environment extra)
       (fun core_extra -> NOk { planned_rule = (RConjElimR core_extra);
       planned_generated_metadata =
       ((metadata_with_conclusion metadata
          (app (named_binder_names extra)
            metadata.metadata_conclusion_binders) next_environment) :: []);
       planned_environment = next_environment })
   | NRDisjIntroL ->
     (match target with
      | NDisj (first, _) ->
        NOk { planned_rule = RDisjIntroL; planned_generated_metadata =
          ((metadata_with_conclusion metadata (named_binder_names first)
             environment) :: []); planned_environment = environment }
      | _ -> NError NWrongNamedShape)
   | NRDisjIntroR ->
     (match target with
      | NDisj (_, second) ->
        NOk { planned_rule = RDisjIntroR; planned_generated_metadata =
          ((metadata_with_conclusion metadata (named_binder_names second)
             environment) :: []); planned_environment = environment }
      | _ -> NError NWrongNamedShape)
   | NRDisjElim (first, second, first_name, second_name) ->
     named_bind (ensure_hypothesis_fresh metadata first_name) (fun _ ->
       named_bind (ensure_hypothesis_fresh metadata second_name) (fun _ ->
         if (=) first_name second_name
         then NError (NHypothesisAlreadyUsed second_name)
         else let next_environment =
                extend_environments constants environment
                  (first :: (second :: []))
              in
              named_bind
                (elaborate_in_environment constants next_environment first)
                (fun core_first ->
                named_bind
                  (elaborate_in_environment constants next_environment second)
                  (fun core_second -> NOk { planned_rule = (RDisjElim
                  (core_first, core_second)); planned_generated_metadata =
                  ((metadata_with_conclusion metadata
                     (named_binder_names (NDisj (first, second)))
                     next_environment) :: ((metadata_with_hypothesis metadata
                                             first_name
                                             (named_binder_names first)
                                             metadata.metadata_conclusion_binders
                                             next_environment) :: ((metadata_with_hypothesis
                                                                    metadata
                                                                    second_name
                                                                    (named_binder_names
                                                                    second)
                                                                    metadata.metadata_conclusion_binders
                                                                    next_environment) :: [])));
                  planned_environment = next_environment }))))
   | NRAllIntro variable ->
     named_bind (ensure_variable_fresh metadata variable) (fun _ ->
       match target with
       | NAll (_, body) ->
         let next_environment = variable :: environment in
         NOk { planned_rule = RAllIntro; planned_generated_metadata =
         ((metadata_with_conclusion metadata (named_binder_names body)
            next_environment) :: []); planned_environment = next_environment }
       | _ -> NError NWrongNamedShape)
   | NRAllElim (term0, universal) ->
     (match universal with
      | NAll (binder, body) ->
        let next_environment =
          add_environment_name constants
            (extend_environment constants environment universal) term0
        in
        named_bind (elaborate constants (binder :: []) next_environment body)
          (fun core_body ->
          named_bind (term_index constants next_environment term0)
            (fun core_term -> NOk { planned_rule = (RAllElim (core_body,
            core_term)); planned_generated_metadata =
            ((metadata_with_conclusion metadata
               (named_binder_names universal) next_environment) :: []);
            planned_environment = next_environment }))
      | _ -> NError NWrongNamedShape)
   | NRExIntro term0 ->
     (match target with
      | NEx (_, body) ->
        let next_environment =
          add_environment_name constants environment term0
        in
        named_bind (term_index constants next_environment term0)
          (fun core_term -> NOk { planned_rule = (RExIntro core_term);
          planned_generated_metadata =
          ((metadata_with_conclusion metadata (named_binder_names body)
             next_environment) :: []); planned_environment =
          next_environment })
      | _ -> NError NWrongNamedShape)
   | NRExElim (witness, hypothesis, existential) ->
     named_bind (ensure_hypothesis_fresh metadata hypothesis) (fun _ ->
       match existential with
       | NEx (binder, body) ->
         let before_environment =
           extend_environment constants environment existential
         in
         if (||) (string_mem witness constants)
              (string_mem witness before_environment)
         then NError (NVariableAlreadyUsed witness)
         else let generated_environment = witness :: before_environment in
              named_bind
                (elaborate constants (binder :: []) before_environment body)
                (fun core_body -> NOk { planned_rule = (RExElim core_body);
                planned_generated_metadata =
                ((metadata_with_conclusion metadata
                   (named_binder_names existential) before_environment) :: (
                (metadata_with_hypothesis metadata hypothesis
                  (named_binder_names body)
                  metadata.metadata_conclusion_binders generated_environment) :: []));
                planned_environment = before_environment })
       | _ -> NError NWrongNamedShape)
   | NREqualRefl ->
     NOk { planned_rule = REqualRefl; planned_generated_metadata = [];
       planned_environment = environment }
   | NREqualElim (first, second, predicate) ->
     (match predicate with
      | NAll (binder, body) ->
        let next_environment =
          add_environment_name constants
            (add_environment_name constants
              (extend_environment constants environment predicate) first)
            second
        in
        named_bind (elaborate constants (binder :: []) next_environment body)
          (fun core_predicate ->
          named_bind (term_index constants next_environment first)
            (fun core_first ->
            named_bind (term_index constants next_environment second)
              (fun core_second -> NOk { planned_rule = (REqualElim
              (core_predicate, core_first, core_second));
              planned_generated_metadata =
              ((metadata_with_conclusion metadata [] next_environment) :: (
              (metadata_with_conclusion metadata (named_binder_names body)
                next_environment) :: [])); planned_environment =
              next_environment })))
      | _ -> NError NWrongNamedShape)
   | NRCut (hypothesis, lemma) ->
     named_bind (ensure_hypothesis_fresh metadata hypothesis) (fun _ ->
       let next_environment = extend_environment constants environment lemma
       in
       named_bind (elaborate_in_environment constants next_environment lemma)
         (fun core_lemma -> NOk { planned_rule = (RCut core_lemma);
         planned_generated_metadata =
         ((metadata_with_conclusion metadata (named_binder_names lemma)
            next_environment) :: ((metadata_with_hypothesis metadata
                                    hypothesis (named_binder_names lemma)
                                    metadata.metadata_conclusion_binders
                                    next_environment) :: []));
         planned_environment = next_environment })))

(** val named_rule_step :
    named_axiom list -> named_rule -> named_state -> named_state named_result **)

let named_rule_step axioms primitive state =
  match state.named_kernel_state with
  | [] ->
    (match state.named_goal_metadata with
     | [] -> NError (NCoreError NoGoals)
     | _ :: _ -> NError NMetadataMismatch)
  | goal0 :: _ ->
    (match state.named_goal_metadata with
     | [] -> NError NMetadataMismatch
     | metadata :: metadata_rest ->
       named_bind (reify_goal metadata goal0) (fun view ->
         named_bind (plan_named_rule metadata view primitive) (fun plan ->
           named_bind
             (compile_axioms metadata.metadata_constants
               plan.planned_environment axioms) (fun core_axioms ->
             match rule_step (fun candidate ->
                     formula_in candidate core_axioms) plan.planned_rule
                     state.named_kernel_state with
             | Success next ->
               NOk { named_kernel_state = next; named_goal_metadata =
                 (app plan.planned_generated_metadata metadata_rest) }
             | Failure error -> NError (NCoreError error)))))

(** val named_rule_run :
    named_axiom list -> named_rule list -> named_state -> named_state
    named_result **)

let rec named_rule_run axioms rules state =
  match rules with
  | [] -> NOk state
  | primitive :: rest ->
    named_bind (named_rule_step axioms primitive state) (fun next ->
      named_rule_run axioms rest next)

type named_tactic =
| NTacRule of named_rule
| NTacIntro of string
| NTacExact of string
| NTacApply of string
| NTacSpecialize of string * string * string
| NTacSplit
| NTacLeft
| NTacRight
| NTacUse of string
| NTacRefl
| NTacContradiction
| NTacCases of string * string * string

type tactic_plan = { planned_tactic : tactic;
                     tactic_generated_metadata : goal_metadata list;
                     tactic_environment : string list }

(** val plan_named_tactic :
    goal_metadata -> named_goal -> named_tactic -> tactic_plan named_result **)

let plan_named_tactic metadata view command =
  let constants = metadata.metadata_constants in
  let environment = metadata.metadata_environment in
  let target = view.named_conclusion in
  (match command with
   | NTacRule _ -> NError NWrongNamedShape
   | NTacIntro name ->
     (match target with
      | NImpl (premise, conclusion0) ->
        named_bind (ensure_hypothesis_fresh metadata name) (fun _ -> NOk
          { planned_tactic = TacIntro; tactic_generated_metadata =
          ((metadata_with_hypothesis metadata name
             (named_binder_names premise) (named_binder_names conclusion0)
             environment) :: []); tactic_environment = environment })
      | NNeg premise ->
        named_bind (ensure_hypothesis_fresh metadata name) (fun _ -> NOk
          { planned_tactic = TacIntro; tactic_generated_metadata =
          ((metadata_with_hypothesis metadata name
             (named_binder_names premise) [] environment) :: []);
          tactic_environment = environment })
      | NAll (_, body) ->
        named_bind (ensure_variable_fresh metadata name) (fun _ ->
          let next_environment = name :: environment in
          NOk { planned_tactic = TacIntro; tactic_generated_metadata =
          ((metadata_with_conclusion metadata (named_binder_names body)
             next_environment) :: []); tactic_environment = next_environment })
      | _ -> NError NWrongNamedShape)
   | NTacExact hypothesis ->
     named_bind (hypothesis_index metadata hypothesis) (fun index -> NOk
       { planned_tactic = (TacExact index); tactic_generated_metadata = [];
       tactic_environment = environment })
   | NTacApply hypothesis ->
     named_bind (hypothesis_index metadata hypothesis) (fun index ->
       match find_named_hypothesis hypothesis view.named_assumptions with
       | Some n ->
         (match n with
          | NImpl (premise, _) ->
            NOk { planned_tactic = (TacApply index);
              tactic_generated_metadata =
              ((metadata_with_conclusion metadata
                 (named_binder_names premise) environment) :: []);
              tactic_environment = environment }
          | NNeg premise ->
            NOk { planned_tactic = (TacApply index);
              tactic_generated_metadata =
              ((metadata_with_conclusion metadata
                 (named_binder_names premise) environment) :: []);
              tactic_environment = environment }
          | _ -> NError NWrongNamedShape)
       | None -> NError (NHypothesisNotFound hypothesis))
   | NTacSpecialize (hypothesis, term0, new_hypothesis) ->
     named_bind (ensure_hypothesis_fresh metadata new_hypothesis) (fun _ ->
       named_bind (hypothesis_index metadata hypothesis) (fun index ->
         match find_named_hypothesis hypothesis view.named_assumptions with
         | Some n ->
           (match n with
            | NAll (_, body) ->
              let next_environment =
                add_environment_name constants environment term0
              in
              named_bind (term_index constants next_environment term0)
                (fun core_term -> NOk { planned_tactic = (TacSpecialize
                (index, core_term)); tactic_generated_metadata =
                ((metadata_with_hypothesis metadata new_hypothesis
                   (named_binder_names body)
                   metadata.metadata_conclusion_binders next_environment) :: []);
                tactic_environment = next_environment })
            | _ -> NError NWrongNamedShape)
         | None -> NError (NHypothesisNotFound hypothesis)))
   | NTacSplit ->
     (match target with
      | NConj (first, second) ->
        NOk { planned_tactic = TacSplit; tactic_generated_metadata =
          ((metadata_with_conclusion metadata (named_binder_names first)
             environment) :: ((metadata_with_conclusion metadata
                                (named_binder_names second) environment) :: []));
          tactic_environment = environment }
      | NIff (first, second) ->
        NOk { planned_tactic = TacSplit; tactic_generated_metadata =
          ((metadata_with_conclusion metadata
             (named_binder_names (NImpl (first, second))) environment) :: (
          (metadata_with_conclusion metadata
            (named_binder_names (NImpl (second, first))) environment) :: []));
          tactic_environment = environment }
      | _ -> NError NWrongNamedShape)
   | NTacLeft ->
     (match target with
      | NDisj (first, _) ->
        NOk { planned_tactic = TacLeft; tactic_generated_metadata =
          ((metadata_with_conclusion metadata (named_binder_names first)
             environment) :: []); tactic_environment = environment }
      | _ -> NError NWrongNamedShape)
   | NTacRight ->
     (match target with
      | NDisj (_, second) ->
        NOk { planned_tactic = TacRight; tactic_generated_metadata =
          ((metadata_with_conclusion metadata (named_binder_names second)
             environment) :: []); tactic_environment = environment }
      | _ -> NError NWrongNamedShape)
   | NTacUse term0 ->
     (match target with
      | NEx (_, body) ->
        let next_environment =
          add_environment_name constants environment term0
        in
        named_bind (term_index constants next_environment term0)
          (fun core_term -> NOk { planned_tactic = (TacUse core_term);
          tactic_generated_metadata =
          ((metadata_with_conclusion metadata (named_binder_names body)
             next_environment) :: []); tactic_environment =
          next_environment })
      | _ -> NError NWrongNamedShape)
   | NTacRefl ->
     NOk { planned_tactic = TacRefl; tactic_generated_metadata = [];
       tactic_environment = environment }
   | NTacContradiction ->
     NOk { planned_tactic = TacContradiction; tactic_generated_metadata = [];
       tactic_environment = environment }
   | NTacCases (hypothesis, first_name, second_name) ->
     named_bind (hypothesis_index metadata hypothesis) (fun index ->
       match find_named_hypothesis hypothesis view.named_assumptions with
       | Some n ->
         (match n with
          | NConj (first, second) ->
            named_bind (ensure_hypothesis_fresh metadata first_name)
              (fun _ ->
              named_bind (ensure_hypothesis_fresh metadata second_name)
                (fun _ ->
                if (=) first_name second_name
                then NError (NHypothesisAlreadyUsed second_name)
                else NOk { planned_tactic = (TacCases index);
                       tactic_generated_metadata =
                       ({ metadata_hypothesis_names =
                       (second_name :: (first_name :: metadata.metadata_hypothesis_names));
                       metadata_assumption_binders =
                       ((named_binder_names second) :: ((named_binder_names
                                                          first) :: metadata.metadata_assumption_binders));
                       metadata_conclusion_binders =
                       metadata.metadata_conclusion_binders;
                       metadata_environment = environment;
                       metadata_constants = constants } :: []);
                       tactic_environment = environment }))
          | NIff (first, second) ->
            named_bind (ensure_hypothesis_fresh metadata first_name)
              (fun _ ->
              named_bind (ensure_hypothesis_fresh metadata second_name)
                (fun _ ->
                if (=) first_name second_name
                then NError (NHypothesisAlreadyUsed second_name)
                else NOk { planned_tactic = (TacCases index);
                       tactic_generated_metadata =
                       ({ metadata_hypothesis_names =
                       (second_name :: (first_name :: metadata.metadata_hypothesis_names));
                       metadata_assumption_binders =
                       ((named_binder_names (NImpl (second, first))) :: (
                       (named_binder_names (NImpl (first, second))) :: metadata.metadata_assumption_binders));
                       metadata_conclusion_binders =
                       metadata.metadata_conclusion_binders;
                       metadata_environment = environment;
                       metadata_constants = constants } :: []);
                       tactic_environment = environment }))
          | NEx (_, body) ->
            named_bind (ensure_hypothesis_fresh metadata second_name)
              (fun _ ->
              named_bind (ensure_variable_fresh metadata first_name)
                (fun _ ->
                let next_environment = first_name :: environment in
                NOk { planned_tactic = (TacCases index);
                tactic_generated_metadata =
                ((metadata_with_hypothesis metadata second_name
                   (named_binder_names body)
                   metadata.metadata_conclusion_binders next_environment) :: []);
                tactic_environment = next_environment }))
          | _ -> NError NWrongNamedShape)
       | None -> NError (NHypothesisNotFound hypothesis)))

(** val named_tactic_step :
    named_tactic -> named_state -> named_state named_result **)

let named_tactic_step command state =
  match state.named_kernel_state with
  | [] ->
    (match state.named_goal_metadata with
     | [] -> NError (NCoreError NoGoals)
     | _ :: _ -> NError NMetadataMismatch)
  | goal0 :: _ ->
    (match state.named_goal_metadata with
     | [] -> NError NMetadataMismatch
     | metadata :: metadata_rest ->
       named_bind (reify_goal metadata goal0) (fun view ->
         named_bind (plan_named_tactic metadata view command) (fun plan ->
           match step (fun _ -> false) plan.planned_tactic
                   state.named_kernel_state with
           | Success next ->
             NOk { named_kernel_state = next; named_goal_metadata =
               (app plan.tactic_generated_metadata metadata_rest) }
           | Failure error -> NError (NCoreError error))))

(** val named_step :
    named_axiom list -> named_tactic -> named_state -> named_state
    named_result **)

let named_step axioms command state =
  match command with
  | NTacRule primitive -> named_rule_step axioms primitive state
  | _ -> named_tactic_step command state

(** val named_run :
    named_axiom list -> named_tactic list -> named_state -> named_state
    named_result **)

let rec named_run axioms commands state =
  match commands with
  | [] -> NOk state
  | command :: rest ->
    named_bind (named_step axioms command state) (fun next ->
      named_run axioms rest next)

(** val named_all_variables : named_formula -> string list **)

let rec named_all_variables = function
| NFalsum -> []
| NEqual (first, second) -> add_name (first :: []) second
| NMember (first, second) -> add_name (first :: []) second
| NConj (first, second) ->
  merge_names (named_all_variables first) (named_all_variables second)
| NDisj (first, second) ->
  merge_names (named_all_variables first) (named_all_variables second)
| NImpl (first, second) ->
  merge_names (named_all_variables first) (named_all_variables second)
| NNeg body -> named_all_variables body
| NIff (first, second) ->
  merge_names (named_all_variables first) (named_all_variables second)
| NAll (binder, body) -> add_name (named_all_variables body) binder
| NEx (binder, body) -> add_name (named_all_variables body) binder

(** val named_substitute_variable :
    string -> string -> named_formula -> named_formula **)

let rec named_substitute_variable variable replacement source =
  let replace = fun name -> if (=) name variable then replacement else name in
  (match source with
   | NFalsum -> NFalsum
   | NEqual (first, second) -> NEqual ((replace first), (replace second))
   | NMember (first, second) -> NMember ((replace first), (replace second))
   | NConj (first, second) ->
     NConj ((named_substitute_variable variable replacement first),
       (named_substitute_variable variable replacement second))
   | NDisj (first, second) ->
     NDisj ((named_substitute_variable variable replacement first),
       (named_substitute_variable variable replacement second))
   | NImpl (first, second) ->
     NImpl ((named_substitute_variable variable replacement first),
       (named_substitute_variable variable replacement second))
   | NNeg body -> NNeg (named_substitute_variable variable replacement body)
   | NIff (first, second) ->
     NIff ((named_substitute_variable variable replacement first),
       (named_substitute_variable variable replacement second))
   | NAll (binder, body) ->
     if (=) binder variable
     then NAll (binder, body)
     else NAll (binder, (named_substitute_variable variable replacement body))
   | NEx (binder, body) ->
     if (=) binder variable
     then NEx (binder, body)
     else NEx (binder, (named_substitute_variable variable replacement body)))

(** val named_separation_instance :
    string -> string -> named_formula -> named_formula **)

let named_separation_instance source element predicate =
  let used =
    add_name (add_name (named_all_variables predicate) source) element
  in
  let subset = fresh_string "b" used in
  NEx (subset, (NAll (element, (NIff ((NMember (element, subset)), (NConj
  ((NMember (element, source)), predicate)))))))

type named_replacement_parts = { named_replacement_functional : named_formula;
                                 named_replacement_image : named_formula;
                                 named_replacement_instance : named_formula }

(** val make_named_replacement_parts :
    string -> string -> string -> named_formula -> named_replacement_parts **)

let make_named_replacement_parts source input output predicate =
  let used =
    add_name
      (add_name (add_name (named_all_variables predicate) source) input)
      output
  in
  let alternate = fresh_string "z" used in
  let image_set = fresh_string "b" (add_name used alternate) in
  let alternate_predicate =
    named_substitute_variable output alternate predicate
  in
  let functional = NAll (input, (NEx (output, (NConj (predicate, (NAll
    (alternate, (NImpl (alternate_predicate, (NEqual (alternate,
    output)))))))))))
  in
  let image = NEx (image_set, (NAll (output, (NIff ((NMember (output,
    image_set)), (NEx (input, (NConj ((NMember (input, source)),
    predicate)))))))))
  in
  { named_replacement_functional = functional; named_replacement_image =
  image; named_replacement_instance = (NImpl (functional, image)) }

(** val named_fixed_axioms : named_axiom list **)

let named_fixed_axioms =
  (NFixedAxiom NEmptySet) :: ((NFixedAxiom NExtensionality) :: ((NFixedAxiom
    NPairing) :: ((NFixedAxiom NUnion) :: ((NFixedAxiom
    NPowerSet) :: ((NFixedAxiom NFoundation) :: ((NFixedAxiom
    NInfinity) :: ((NFixedAxiom NChoice) :: [])))))))

(** val named_default_all_intro_rule_step :
    named_state -> named_state named_result **)

let named_default_all_intro_rule_step state =
  match named_goals state with
  | NOk value ->
    (match value with
     | [] -> NError (NCoreError NoGoals)
     | goal0 :: _ ->
       (match goal0.named_conclusion with
        | NAll (binder, _) -> named_rule_step [] (NRAllIntro binder) state
        | _ -> NError NWrongNamedShape))
  | NError error -> NError error

(** val named_fixed_axiom_rule_step :
    named_state -> named_state named_result **)

let named_fixed_axiom_rule_step state =
  named_rule_run named_fixed_axioms (NRAxiom :: []) state

(** val named_separation_axiom_rule_step :
    string -> string -> named_formula -> named_state -> named_state
    named_result **)

let named_separation_axiom_rule_step source element predicate state =
  let instance = named_separation_instance source element predicate in
  named_rule_run ((NSeparationAxiom (source, element, predicate)) :: [])
    ((NRAllElim (source, (NAll (source, instance)))) :: (NRAxiom :: [])) state

(** val current_hypothesis_names : named_state -> string list **)

let current_hypothesis_names state =
  match state.named_goal_metadata with
  | [] -> []
  | metadata :: _ -> metadata.metadata_hypothesis_names

(** val replacement_internal_hypothesis : named_state -> string **)

let replacement_internal_hypothesis state =
  fresh_string "__replacement_functional" (current_hypothesis_names state)

(** val named_replacement_axiom_rule_step :
    string -> string -> string -> named_formula -> named_state -> named_state
    named_result **)

let named_replacement_axiom_rule_step source input output predicate state =
  let parts = make_named_replacement_parts source input output predicate in
  let functional = parts.named_replacement_functional in
  let image = parts.named_replacement_image in
  let internal = replacement_internal_hypothesis state in
  named_rule_run ((NReplacementAxiom (input, output, predicate)) :: [])
    ((NRImplIntro internal) :: ((NRAllElim (source, (NAll (source,
    image)))) :: ((NRImplElim functional) :: (NRAxiom :: ((NRHypothesis
    internal) :: []))))) state

(** val named_separation_tactic_step :
    string -> string -> string -> named_formula -> named_state -> named_state
    named_result **)

let named_separation_tactic_step fact source element predicate state =
  let instance = named_separation_instance source element predicate in
  named_rule_run ((NSeparationAxiom (source, element, predicate)) :: [])
    ((NRCut (fact, instance)) :: ((NRAllElim (source, (NAll (source,
    instance)))) :: (NRAxiom :: []))) state

(** val named_replacement_tactic_step :
    string -> string -> string -> string -> named_formula -> named_state ->
    named_state named_result **)

let named_replacement_tactic_step fact source input output predicate state =
  let parts = make_named_replacement_parts source input output predicate in
  let functional = parts.named_replacement_functional in
  let image = parts.named_replacement_image in
  let instance = parts.named_replacement_instance in
  let internal = replacement_internal_hypothesis state in
  named_rule_run ((NReplacementAxiom (input, output, predicate)) :: [])
    ((NRCut (fact, instance)) :: ((NRImplIntro internal) :: ((NRAllElim
    (source, (NAll (source, image)))) :: ((NRImplElim
    functional) :: (NRAxiom :: ((NRHypothesis internal) :: [])))))) state

type named_rule_request =
| NPrimitiveRule of named_rule
| NDefaultAllIntroRule
| NFixedAxiomRule
| NSeparationAxiomRule of string * string * named_formula
| NReplacementAxiomRule of string * string * string * named_formula

(** val named_execute_rule :
    named_rule_request -> named_state -> named_state named_result **)

let named_execute_rule request state =
  match request with
  | NPrimitiveRule primitive -> named_rule_step [] primitive state
  | NDefaultAllIntroRule -> named_default_all_intro_rule_step state
  | NFixedAxiomRule -> named_fixed_axiom_rule_step state
  | NSeparationAxiomRule (source, element, predicate) ->
    named_separation_axiom_rule_step source element predicate state
  | NReplacementAxiomRule (source, input, output, predicate) ->
    named_replacement_axiom_rule_step source input output predicate state

type certificate_step = { certificate_axioms : named_axiom list;
                          certificate_rule : named_rule }

type certificate = certificate_step list

(** val run_certificate_step :
    certificate_step -> named_state -> named_state named_result **)

let run_certificate_step step0 state =
  named_rule_step step0.certificate_axioms step0.certificate_rule state

(** val replay_steps :
    certificate -> named_state -> named_state named_result **)

let rec replay_steps steps state =
  match steps with
  | [] -> NOk state
  | step0 :: rest ->
    named_bind (run_certificate_step step0 state) (fun next ->
      replay_steps rest next)

type certified_state = { certified_initial_formula : named_formula;
                         certified_constants : string list;
                         certified_current_state : named_state;
                         certified_reverse_certificate : certificate }

(** val certified_start_with_constants :
    string list -> named_formula -> certified_state named_result **)

let certified_start_with_constants constants source =
  named_bind (named_start_with_constants constants source) (fun state -> NOk
    { certified_initial_formula = source; certified_constants = constants;
    certified_current_state = state; certified_reverse_certificate = [] })

(** val certified_start : named_formula -> certified_state named_result **)

let certified_start source =
  certified_start_with_constants [] source

(** val certified_goals : certified_state -> named_goal list named_result **)

let certified_goals state =
  named_goals state.certified_current_state

(** val certified_solved : certified_state -> bool **)

let certified_solved state =
  named_solved state.certified_current_state

(** val certified_certificate : certified_state -> certificate **)

let certified_certificate state =
  rev state.certified_reverse_certificate

(** val certified_step :
    certificate_step -> certified_state -> certified_state named_result **)

let certified_step step0 state =
  named_bind (run_certificate_step step0 state.certified_current_state)
    (fun next -> NOk { certified_initial_formula =
    state.certified_initial_formula; certified_constants =
    state.certified_constants; certified_current_state = next;
    certified_reverse_certificate =
    (step0 :: state.certified_reverse_certificate) })

(** val certified_run :
    certificate -> certified_state -> certified_state named_result **)

let rec certified_run steps state =
  match steps with
  | [] -> NOk state
  | step0 :: rest ->
    named_bind (certified_step step0 state) (fun next ->
      certified_run rest next)

(** val replay_certificate_with_constants :
    string list -> named_formula -> certificate -> named_state named_result **)

let replay_certificate_with_constants constants source steps =
  named_bind (named_start_with_constants constants source) (fun state ->
    replay_steps steps state)

(** val replay_certificate :
    named_formula -> certificate -> named_state named_result **)

let replay_certificate source steps =
  replay_certificate_with_constants [] source steps

(** val certified_finalize : certified_state -> certificate named_result **)

let certified_finalize state =
  let steps = certified_certificate state in
  named_bind
    (replay_certificate_with_constants state.certified_constants
      state.certified_initial_formula steps) (fun replayed ->
    if named_solved replayed then NOk steps else NError NWrongNamedShape)

(** val one_step : named_axiom list -> named_rule -> certificate_step **)

let one_step axioms primitive =
  { certificate_axioms = axioms; certificate_rule = primitive }

(** val named_rule_request_program :
    named_rule_request -> named_state -> certificate named_result **)

let named_rule_request_program request state =
  match request with
  | NPrimitiveRule primitive -> NOk ((one_step [] primitive) :: [])
  | NDefaultAllIntroRule ->
    (match named_goals state with
     | NOk value ->
       (match value with
        | [] -> NError (NCoreError NoGoals)
        | goal0 :: _ ->
          (match goal0.named_conclusion with
           | NAll (binder, _) -> NOk ((one_step [] (NRAllIntro binder)) :: [])
           | _ -> NError NWrongNamedShape))
     | NError error -> NError error)
  | NFixedAxiomRule -> NOk ((one_step named_fixed_axioms NRAxiom) :: [])
  | NSeparationAxiomRule (source, element, predicate) ->
    let instance = named_separation_instance source element predicate in
    let capability = NSeparationAxiom (source, element, predicate) in
    NOk
    ((one_step [] (NRAllElim (source, (NAll (source, instance))))) :: (
    (one_step (capability :: []) NRAxiom) :: []))
  | NReplacementAxiomRule (source, input, output, predicate) ->
    let parts = make_named_replacement_parts source input output predicate in
    let functional = parts.named_replacement_functional in
    let image = parts.named_replacement_image in
    let internal = replacement_internal_hypothesis state in
    let capability = NReplacementAxiom (input, output, predicate) in
    NOk
    ((one_step [] (NRImplIntro internal)) :: ((one_step [] (NRAllElim
                                                (source, (NAll (source,
                                                image))))) :: ((one_step []
                                                                 (NRImplElim
                                                                 functional)) :: (
    (one_step (capability :: []) NRAxiom) :: ((one_step [] (NRHypothesis
                                                internal)) :: [])))))

(** val certified_execute_rule :
    named_rule_request -> certified_state -> certified_state named_result **)

let certified_execute_rule request state =
  named_bind
    (named_rule_request_program request state.certified_current_state)
    (fun steps -> certified_run steps state)

(** val separation_tactic_program :
    string -> string -> string -> named_formula -> certificate **)

let separation_tactic_program fact source element predicate =
  let instance = named_separation_instance source element predicate in
  let capability = NSeparationAxiom (source, element, predicate) in
  (one_step [] (NRCut (fact, instance))) :: ((one_step [] (NRAllElim (source,
                                               (NAll (source, instance))))) :: (
  (one_step (capability :: []) NRAxiom) :: []))

(** val certified_separation_tactic :
    string -> string -> string -> named_formula -> certified_state ->
    certified_state named_result **)

let certified_separation_tactic fact source element predicate state =
  certified_run (separation_tactic_program fact source element predicate)
    state

(** val replacement_tactic_program :
    string -> string -> string -> string -> named_formula -> named_state ->
    certificate **)

let replacement_tactic_program fact source input output predicate state =
  let parts = make_named_replacement_parts source input output predicate in
  let functional = parts.named_replacement_functional in
  let image = parts.named_replacement_image in
  let instance = parts.named_replacement_instance in
  let internal = replacement_internal_hypothesis state in
  let capability = NReplacementAxiom (input, output, predicate) in
  (one_step [] (NRCut (fact, instance))) :: ((one_step [] (NRImplIntro
                                               internal)) :: ((one_step []
                                                                (NRAllElim
                                                                (source,
                                                                (NAll
                                                                (source,
                                                                image))))) :: (
  (one_step [] (NRImplElim functional)) :: ((one_step (capability :: [])
                                              NRAxiom) :: ((one_step []
                                                             (NRHypothesis
                                                             internal)) :: [])))))

(** val certified_replacement_tactic :
    string -> string -> string -> string -> named_formula -> certified_state
    -> certified_state named_result **)

let certified_replacement_tactic fact source input output predicate state =
  certified_run
    (replacement_tactic_program fact source input output predicate
      state.certified_current_state) state
