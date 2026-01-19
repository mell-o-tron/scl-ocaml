open Ast
open Rewriting
open Rules
open Unification

let is_var (t : term) = match t with Var _ -> true | _ -> false

let is_term_shallow (t : term) = match t with
  | Const _ -> true
  | Var _ -> true
  | Func(_, l) -> List.for_all is_var l

let is_atom_simple (a : atom) = match a with
  | Atom(_, l) -> List.for_all is_term_shallow l

let is_literal_simple (l : literal) = match l with
  | Pos(a) -> is_atom_simple a
  | Neg(a) -> is_atom_simple a

let is_clause_simple (c : clause) = List.for_all is_literal_simple c

let is_term_functional (t) = match t with
| Const _ -> true
| Var _ -> false
| Func(_, _) -> true

let is_atom_functional a = match a with
  | Atom(_, l) -> List.exists is_term_functional l

let is_literal_functional (l : literal) = match l with
  | Pos(a) -> is_atom_functional a
  | Neg(a) -> is_atom_functional a

let is_clause_functional (c) = List.exists is_literal_functional c

let is_literal_positive l = match l with
| Pos(_) -> true
| Neg(_) -> false

let is_literal_negative l = not(is_literal_positive l)

let is_clause_positive c = List.for_all is_literal_positive c

let is_clause_single_vard c = 
  let l = get_all_vars_clause c in
  List.length l = 1

let rec get_functional_subterms t = match t with
  | Const _ -> [t]
  | Var _ -> []
  | Func (_, l) -> t :: (List.map get_functional_subterms l |> List.flatten)

let all_functional_subterms_contain_vars_term t vars = 
  let funsubterms = get_functional_subterms t in
  List.for_all (
    fun t1 -> let varst1 = get_all_vars_term t1 in
    List.for_all (fun x -> List.mem x varst1) vars
  ) funsubterms

let all_functional_subterms_contain_vars_atom a vars = match a with
  | Atom(_, l) -> List.for_all (fun x -> all_functional_subterms_contain_vars_term x vars) l

let all_functional_subterms_contain_vars_literal l vars = match l with
  | Pos(a) | Neg(a) -> all_functional_subterms_contain_vars_atom a vars

let all_functional_subterms_contain_vars_clause c vars = List.for_all
  (fun x -> all_functional_subterms_contain_vars_literal x vars) c

let get_guards c = 
  let vars_c = get_all_vars_clause c in
  List.filter 
  (fun x -> 
    let vars_x = get_all_vars_literal x in  
    List.length vars_x != 0 &&
    List.for_all (fun x -> List.mem x vars_c) vars_x && 
    is_literal_negative x &&
    not(is_literal_functional x)
  ) c

let is_clause_guarded c = 
  let all_vars_c = get_all_vars_clause c in
  is_clause_simple c &&
  ((is_clause_positive (c) && not(is_clause_functional c) && is_clause_single_vard c)
  || 
  (all_functional_subterms_contain_vars_clause c (all_vars_c) && 
  if List.length all_vars_c != 0 then List.length (get_guards c) != 0 else true  
  ))

let get_max_clause c ord = 
  let rec get_max_aux c current = match c with 
    | [] -> current
    | a :: next -> 
      if Option.is_none current then get_max_aux next (Some a) else 
      (if ord a (Option.get current) > 0 then 
      get_max_aux next (Some a) else 
      get_max_aux next current)
      in
      get_max_aux c None

let get_max_clauses c ord = 
  let max = get_max_clause c ord in
  if Option.is_none max then [] else
    let max = Option.get max in
    List.filter (fun x -> ord x max >= 0) c

(** Gets the eligible literals in a clause, i.e. those that are either selected or (in case of no selection) maximal *)
let get_eligible_literals (ord : literal-> literal -> int) (c : clause) = 
  if is_clause_functional c then
    let funneg = List.filter (fun x -> is_literal_functional x && is_literal_negative x) c in
    if List.length funneg != 0 then 
      (Printf.printf "Found negative functional\n";
      funneg)
    else 
      (Printf.printf "No negative functional, going for max\n";
      get_max_clauses c ord)
  else
    (let g = get_guards c in
    if List.is_empty g then 
      (Printf.printf "No guard, going for max\n";
      get_max_clauses c ord)
    else (Printf.printf "Found guard\n"; g))


type eligible_literal = {lit : literal ; from : clause}

let pretty_eligible_literal {lit; from} =
  Printf.sprintf "%s \t (%s)\n" (pretty_lit lit) (pretty_clause from)

let complement l = match l with    
  | Pos(a) -> Neg(a)
  | Neg(a) -> Pos(a)

(** Given a literal l and a list of literals L, returns the literals in L that are resolvable with l.*)
let find_resolvable (elig_list : eligible_literal list)  (l : eligible_literal) = 
  let comp_l = complement l.lit in
  List.filter 
    (fun l1 -> 
      Printf.printf "Trying to match %s and %s\n" (pretty_lit comp_l) (pretty_lit l1.lit);
      let substs = unify_lits_to_pair l1.lit comp_l in
      match substs with
        | None -> Printf.printf "no can do\n"; false
        | _ -> true
      ) elig_list

(** Debug routine for testing guarded SCL strategy -- requires a state, a literal ordering and a constant for grounding.*)
let guarded_debug_scl scl_state ord constant_for_grounding = 
  (* for each clause, get eligible literals -- keep reference to clause*)
  let eligibles = 
    List.map (fun x -> (get_eligible_literals ord x) |> List.map (fun l -> {lit = l; from = x}))
    scl_state.clauses in

  Printf.printf ("Eligible literals:\n");
  List.iter (fun x -> Printf.printf "%s" (pretty_eligible_literal x)) (eligibles |> List.flatten);

  (* find an eligible literal that can be unified with the complement of an eligible literal from another clause *)
  let available_resolutions = List.map (fun eligibles_in_clause -> 
    let rest = List.filter (fun x -> not(x = eligibles_in_clause)) eligibles |> List.flatten in
    Printf.printf "Rest:\n\t%s\n" (List.map pretty_eligible_literal rest |> String.concat "\t");
    List.map (fun x ->  (x, find_resolvable rest x)) eligibles_in_clause
  ) eligibles |> List.flatten |> List.filter (
    fun x -> snd x |> List.is_empty |> not
  ) in
  
  (* corrupt democracy happens (first found is elected) *)
  let elected_1, elected_2 = match available_resolutions with 
  | [] -> failwith "nothing to resolve"
  | (_, []) :: _ -> failwith "should have been filtered out"
  | (l1, l2 :: _) :: _ -> l1, l2 in

  (* check which one of the literals is positive -- this is used for propagation*)
  let positive_elected = match elected_1.lit, elected_2.lit with
  | Pos(_), Neg(_) -> elected_1
  | Neg(_), Pos(_) -> elected_2
  | _ -> failwith "something has gone wrong..." in

  let mgu = 
    try
    unify_literal elected_1.lit (complement elected_2.lit) |> Option.get
    with _ -> failwith "elected literals should have been unifiable..." in

  (* produce list of literals to guide decisions *)
  let clause_1_minus_l1 = List.filter (fun x -> not (x = elected_1.lit)) elected_1.from in
  let clause_2_minus_l2 = List.filter (fun x -> not (x = elected_2.lit)) elected_2.from in
  let negate = List.map complement in
  let decision_guide = negate(clause_1_minus_l1) @ negate(clause_2_minus_l2) in

  (* try to perform all the decisions and at each step check if conflict arises *)
  (* as a grounding substitution, use a grounding of the MGU of L1 and !L2 *)

  let lits_and_subs = List.map (
    fun l -> let l1 = apply_subst_lit mgu l in
    let fv = get_all_vars_literal l1 in
    let groundingsub = List.fold_left (fun (sub : 'a StringMap.t) s -> StringMap.add s constant_for_grounding sub) mgu fv in
    (l, groundingsub)
  ) decision_guide in

  let rec apply_decisions_and_check_conflict (state : scl_state) (lits_and_subs : (literal * subst) list) = match lits_and_subs with
    | [] -> state 
    | (l, sub) :: rest -> 
        Printf.printf "Deciding %s%s\n" (pretty_lit l) (pretty_subst sub);
        let new_state = decide l sub state in 
        let confl = Rules.conflict new_state in
        match confl with
          | R_Continue _ -> apply_decisions_and_check_conflict new_state rest
          | R_State (s) -> Printf.printf "EARLY CONFLICT!!\n%s\n" (pretty_state s) ; failwith "early conflict"
          | _ -> failwith "should not be reachable here" in
        
  
  let state_after_decisions = apply_decisions_and_check_conflict scl_state lits_and_subs in

  (* try to propagate the positive eligible literal and cause a conflict *) 

  let fv = get_all_vars_literal positive_elected.lit in
  let groundingsub = List.fold_left (fun (sub : 'a StringMap.t) s -> StringMap.add s constant_for_grounding sub) mgu fv in

  let state_after_propatagion = guided_propagate state_after_decisions positive_elected.lit (List.filter (fun x -> not (x = positive_elected.lit)) positive_elected.from) groundingsub in

  (* now there should be a conflict *)

  let confl = Rules.conflict state_after_propatagion in
  
  let state_after_conflict = (match confl with
          | R_Continue _ -> failwith "no conflict found..."
          | R_State s -> Printf.printf "CONFLICT DETECTED!\n%s\n" (pretty_state s) ; s
          | _ -> failwith "sat or unsat should not be reachable from here 1") in

  (* now apply skip a bunch of times, until resolution is available *)

  let state_after_resolve = (match resolve state_after_conflict with
  | R_Continue _ -> failwith "resolve did not work..."
  | R_State s -> Printf.printf "RESOLVED!\n%s\n" (pretty_state s) ; s
  | _ -> failwith "sat or unsat should not be reachable from here 4") in

  let rec skip_and_resolve state = 
    (match skip state with
    | R_Continue state -> backtrack state
    | R_State state -> skip_and_resolve state
    | _ -> failwith "sat or unsat should not be reachable from here 2")

  in 
  let _state_after_backtrack = (match skip_and_resolve state_after_resolve with
    | R_Continue _ -> failwith "backtrack did not work..."
    | R_State s -> Printf.printf "BACKTRACKED!\n%s\n" (pretty_state s) ; s
    | _ -> failwith "sat or unsat should not be reachable from here 3") in
  ()