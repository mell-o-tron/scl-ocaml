open Ast
open Unification
open Exceptions

(** Prints the state *)
let print_state (state : scl_state) = Printf.printf "State:\n=========================================================\n%s\n\n" (pretty_state state)

(** These shall be defined before running the prover *)
let signature : (string * int) list ref = ref []
let term_ordering : (term -> term -> int) ref = ref (fun _ _ -> failwith "term ordering not implemented")
let literal_ordering : (literal -> literal -> int) ref = ref (fun _ _ -> failwith "literal ordering not implemented")
let clause_ordering : (clause -> clause -> int) ref = ref (fun _ _ -> failwith "clause ordering not implemented")


(** skeleton of the decide rule*)
let decide (l : literal) (s : subst) (state : scl_state) = 
  {state with trail = (apply_subst_lit s l, Level (state.decision_level + 1)) :: state.trail;
  decision_level = state.decision_level + 1}

(** gets all the literals in the state*)
let get_all_literals (state : scl_state) = 
  List.flatten (state.clauses @ state.learned_clauses)

(** gets all the free variables of a term*)
let rec get_all_vars_term (t : term) = match t with
  | Var v -> [v]
  | Func (_, tl) -> List.map (get_all_vars_term) tl |> List.flatten
  | Const _ -> []

(** gets all the free variables of an atom*)
let get_all_vars_atom (Atom(_, tl)) =  List.map (get_all_vars_term) tl |> List.flatten

(** gets all the free variables of a literal *)
let get_all_vars_literal (l : literal) = match l with
  | Pos a -> get_all_vars_atom a
  | Neg a -> get_all_vars_atom a

(** Deduplicates a list *)
let dedup (l : 'a list) : 'a list =
  List.fold_left
    (fun acc x ->
       if List.mem x acc then
         acc
       else
         acc @ [x]
    )
    []
    l


(** gets all the free variables of a clause*)
let get_all_vars_clause (c : clause) = 
  List.map (fun l -> get_all_vars_literal l) c |> List.flatten |> dedup

(** Combinatorial function, returns the n-choices of a list l *)
let rec choices l n = 
  if n < 0 then
    invalid_arg "choices: n must be non-negative"
  else if n = 0 then
    [ [] ]
  else
    List.concat_map
      (fun x ->
         List.map (fun tail -> x :: tail)
                  (choices l (n - 1))
      )
      l

(** generalization of map2 for n elements *)
let rec mapn (f : 'a list -> 'b) (lists : 'a list list) : 'b list =
  (* if any list is empty, we’re done *)
  if List.exists ((=) []) lists then
    []
  else
    let heads = List.map List.hd lists   (* collect the first element of each list *)
    and tails = List.map List.tl lists   (* collect the remainder of each list *)
    in
    f heads :: mapn f tails

(** generates all closed terms below a certain depth *)
let rec gen_all_closed_terms max_depth = 
  List.map (fun (n, ar) -> 
    if ar = 0 then [Const n] else if max_depth > 0 then
      let terms = gen_all_closed_terms (max_depth - 1) in
      mapn (fun l -> Func (n, l)) (choices terms ar)
    else []
  ) !signature |> List.flatten

(** Generates all the froundings of literal l that are below some literal beta.*)
let gen_all_closed_literals_leq_b (l : literal) (b : literal) = 
  let aux max_depth = 
    let terms = gen_all_closed_terms max_depth in
    let vars = get_all_vars_literal l in
    let c = choices terms (List.length vars) in
    let labeled_c = List.map (fun l -> List.mapi (fun i t -> (List.nth vars i, t)) l) c in
    let substs = List.map (fun l -> StringMap.of_list l) labeled_c in
    let gnd = List.map (fun s -> (apply_subst_lit s l, s)) substs in
    List.filter (fun (l1, _) -> (!literal_ordering l1 b) <= 0) gnd
  in 
    let res = ref (aux 0) in
    let old_res = ref !res in
    let i = ref 0 in
    let diff = ref (-1) in

    while List.length !res != 0 && !diff != 0 do
      i := !i+1;
      old_res := !res;
      res := aux !i;
      diff := List.length !res - List.length !old_res
    done;
    !old_res

(** Checks whether a literal is in a trail *)
let is_in_trail (trail : (literal * annot) list) (l : literal) = 
  let trail = List.map (fun (l, _) -> l) trail in
  List.mem l trail || List.mem (lit_neg (l)) trail


(** Auxiliary function for the decision rule. Returns an undecided literal that is < beta *)
let next_decision_literal (state : scl_state) : (literal * subst) = 
  let all_literals = get_all_literals state in
  let gnd = List.map (fun l -> gen_all_closed_literals_leq_b l state.limiting_literal) all_literals |> List.flatten in
  let all_new_literals = List.filter (fun (l, _) -> not (is_in_trail state.trail l)) gnd in
  try List.hd all_new_literals with _ ->  raise (GoToNextRule "all decision literals leq beta are in trail")


(** Auxiliary function for the propagate rule. Returns all the lists that can by obtained
    by removing one element from a list. *)
let remove_one (l : 'a list) : ('a list * 'a) list =
  let rec aux prefix = function
    | [] -> [] 
    | x :: xs ->
      let without_x = (List.rev prefix) @ xs in
      (without_x, x) :: aux (x :: prefix) xs
  in
  aux [] l


(** Checks whether a clause is true in a trail*)
let is_true_in_trail (c : clause) (trail : (literal * annot) list) =
  let trail = List.map (fun (l, _) -> l) trail in
  List.for_all (fun l -> List.mem l trail || not (List.mem (lit_neg l) trail)) c

(** Auxiliary function for the propagate rule. Attempts to split a given ground clause. *)
let try_split_ground_clause (c: clause) (trail : (literal * annot) list) = 
  (* removes duplicated literals *)
  let c = dedup c in
  let splits = remove_one c in
  (* finds a split such that c0 is false in the trail, and l is undefined in the trail*)
  try (Some (List.find (fun (c0, l) -> not(is_true_in_trail c0 trail) && not(is_in_trail trail l)) splits)) with Not_found -> None

let fst3 t = match t with a, _, _ -> a
let snd3 t = match t with _, b, _ -> b
let thrd3 t = match t with _, _, c -> c


(** Auxiliary function for the propagate rule. Attempts to split a given non-ground clause. *)
let try_split_clause (c: clause) (trail : (literal * annot) list) (b : literal)= 
  let aux (max_depth) = 
    let terms = gen_all_closed_terms max_depth in
    let vars = get_all_vars_clause c in
    let ch = choices terms (List.length vars) in
    let labeled_c = List.map (fun l -> List.mapi (fun i t -> (List.nth vars i, t)) l) ch in
    let substs = List.map (fun l -> StringMap.of_list l) labeled_c in
    let gnd = List.map (fun s -> (apply_subst_clause s c, s)) substs in
    let gndleqb = List.filter (fun (l1, _) -> (!clause_ordering l1 [b]) <= 0) gnd in
    try 
      let result = ref None in
      let sub = ref StringMap.empty in
      let _ = List.find (fun (cl, s) -> result := try_split_ground_clause cl trail; sub := s; Option.is_some !result) gndleqb in
      !result, gndleqb, sub
    with Not_found -> None, gndleqb, ref StringMap.empty
  in

    let res = ref (aux 0) in
    let gndleqb = ref (snd3 !res) in
    let old_gndleqb = ref !gndleqb in
    let i = ref 0 in
    let diff = ref (-1) in

    (* is gndleqb nonempty and has it not reached a fixpoint? *)
    while Option.is_none (fst3 !res) && List.length !gndleqb != 0 && !diff != 0 do
      i := !i+1;
      old_gndleqb := !gndleqb;
      res := (aux !i);
      gndleqb := snd3 !res;
      diff := List.length !gndleqb - List.length !old_gndleqb
    done;
    fst3 !res, !(thrd3 !res)


(** The propagate rule. Tries to find a grounding substitution to split a clause into a 
    part that is false in the trail and one literal, to be added to the trail -- TODO this is not quite right*)
let propagate (state : scl_state) =
  try
    let all_clauses = state.clauses @ state.learned_clauses in
    let result = ref (None, StringMap.empty) in
    let _ = List.find (fun cl -> 
      let split, s = try_split_clause cl state.trail state.limiting_literal in
      result := (split, s); Option.is_some split) all_clauses in 
    let (c0, l), s = (Option.get (fst !result)), snd !result in
    {state with trail = (l, Pred (Closure(l :: c0, s))) :: state.trail}


  with Not_found -> raise (GoToNextRule "nothing to propagate")

(** Conflict rule: looks for a clause that is false in the trail for some grounding substitution*)
let conflict (state : scl_state) = 
  let aux (state : scl_state) (max_depth) =
    let terms = gen_all_closed_terms max_depth in
    let vars = List.map (fun c -> get_all_vars_clause c) (state.clauses @ state.learned_clauses) |> List.flatten in
    let ch = choices terms (List.length vars) in
    let labeled_c = List.map (fun l -> List.mapi (fun i t -> (List.nth vars i, t)) l) ch in
    let substs = List.map (fun l -> StringMap.of_list l) labeled_c in

    (* Does one of these substitutions bring to a conflict? *)
    try
      let d = ref [] in
      let s = List.find (fun s -> List.exists (fun c -> d := c; not(is_true_in_trail (apply_subst_clause s c) state.trail)) (state.clauses @ state.learned_clauses)) substs in
      Some {state with conflict_closure = Closure(!d, s)}
    with Not_found -> None
  in

  (* TODO How to limit the depth? Also use beta? *)
  try Option.get (aux state 10) with _ -> raise (GoToNextRule "could not create conflict")

(** Skip rule: if a literal in the trail is not present in the conflict clause, skip it*)
let skip (state : scl_state) = 

  let d = match state.conflict_closure with
    | Closure (c, s) -> apply_subst_clause s c
    | Bot -> failwith "cannot recover"
    | Top -> failwith "not in conflict state" in
  match state.trail with
  | (l, Level (_)) :: rest -> 
    if not(List.mem (lit_neg l) d) then 
      let _ = Printf.printf "%s is not a member of %s.\n" (pretty_lit (lit_neg l)) (pretty_clause d) in
      {state with trail = rest; decision_level = state.decision_level - 1} else raise (GoToNextRule "nothing to skip")
  | (l, Pred _) :: rest -> 
      if not(List.mem l d) then 
        let _ = Printf.printf "%s is not a member of %s.\n" (pretty_lit l) (pretty_clause d) in
        {state with trail = rest} else raise (GoToNextRule "nothing to skip")
  | _ -> raise (GoToNextRule "nothing to skip")

(** auxiliary function for factorize, removes first occurrence of x in list l *)
let remove_first (x : 'a) (l : 'a list) : 'a list =
  let rec aux acc = function
    | [] -> List.rev acc
    | y :: ys ->
      if x = y then List.rev_append acc ys
      else aux (y :: acc) ys
  in
  aux [] l

(** factorize rule*)
let factorize (state : scl_state) = 
  let s, c = match state.conflict_closure with
    | Closure (c, s) -> s, c
    | Bot -> failwith "cannot recover"
    | Top -> failwith "not in conflict state" in
  let c = c |> dedup in
  (* for each pair of literals, check if they can be unified and unify them *)
  let mgu = ref None in
  let l1 = try (List.find (fun l1 -> List.exists (fun l2 -> l2 != l1 && (
  let mgu_found = (unify_literal (StringMap.empty) l1 l2) in  
    mgu := mgu_found ; Option.is_some mgu_found) ) c) c) with Not_found -> raise (GoToNextRule "could not factorize") in

  let d = remove_first l1 c in 
  {state with conflict_closure = Closure (apply_subst_clause (Option.get !mgu) d, s)}

(** "de-applicates" a substitution, substituting the subterms with the original variable *)
let de_apply_subst_lit (s : subst) (l:literal) = 
  let lis = StringMap.to_list s in
  let h : (term, string) Hashtbl.t = Hashtbl.create 10 in
  List.iter (fun (s, t) -> Hashtbl.add h t s) lis;

  let rec aux (t : term) = 
    if Hashtbl.mem h t then (Var (Hashtbl.find h t)) else 
    match t with 
      | Func (n, l) -> Func (n, List.map (aux) l)
      | _ -> t
  in
  match l with 
    | Pos (Atom (n, lis)) -> Pos(Atom(n, List.map aux lis))
    | Neg (Atom (n, lis)) -> Neg (Atom(n, List.map aux lis))

(** resolve rule: applies a resolution step to the conflict clause *)
let resolve (state : scl_state) = match state.trail with
  | (ldelta, Pred (Closure(c, delta))) :: _ -> 
    let l = de_apply_subst_lit delta ldelta in
    let sigma, d = match state.conflict_closure with
      | Closure (c, s) -> s, c
      | Bot -> failwith "cannot recover"
      | Top -> failwith "not in conflict state" in
    let mgu = ref None in
    let l' = try
      List.find (fun l' -> (ldelta = lit_neg(apply_subst_lit sigma l')) && let mgu_found = unify_literal StringMap.empty l l' in mgu := mgu_found; Option.is_some mgu_found) d
    with Not_found -> raise (GoToNextRule "no resolution step can be applied")
    in let d = remove_first l' d 
    in let c = remove_first l c
    in {state with conflict_closure = Closure (apply_subst_clause (Option.get !mgu) (d @ c), compose sigma delta)}

  | _ -> raise (GoToNextRule "cannot apply resolve")

let max_in_list (l : 'a list) : 'a =
  match l with
  | [] -> invalid_arg "max_in_list: empty list"
  | x :: xs ->
      List.fold_left max x xs

(** finds level of a literal -- TODO check more closely that this never loops*)
let rec level_of_lit (l : literal) (trail : (literal * annot) list) = 
  try
    let _, a = List.find (fun (l1, _) -> l1 = l) trail in
    match a with
      | Level k -> k
      | Pred(Closure(c, sigma)) -> level_of_clause (apply_subst_clause sigma c) (trail)
      | _ -> failwith "should never happen"
  with Not_found -> failwith "cannot find literal"


(** finds level of a clause*)
and level_of_clause (c : clause) (trail : (literal * annot) list) : int = 
  max_in_list (List.map (fun l -> level_of_lit l trail) c)
  
(** finds level of a trail *)
let level_of_trail (trail : (literal * annot) list) = match trail with
  | (l, _) :: _ -> level_of_lit l trail
  | _ -> 0

let rec prefix n l =
    match (n, l) with
  | (0, _) | (_, []) -> []
  | (n, x :: xs) -> x :: prefix (n - 1) xs

(** finds smallest maximal trail subsequence such that exists substitution that makes c true *)
let min_subtrail (trail : (literal * annot) list) (c : clause) =  
let aux (trail : (literal * annot) list) (max_depth) =
  let terms = gen_all_closed_terms max_depth in
  let vars = get_all_vars_clause c in
  let ch = choices terms (List.length vars) in
  let labeled_c = List.map (fun l -> List.mapi (fun i t -> (List.nth vars i, t)) l) ch in
  let substs = List.map (fun l -> StringMap.of_list l) labeled_c in
  List.exists (fun s -> is_true_in_trail (apply_subst_clause s c) trail) substs
in 
let result = ref None in
  for i = 1 to List.length trail - 1 do
    Printf.printf "%s\n" (if aux (prefix i trail) 10 then "true" else "false");
    (* TODO figure out how to limit depth properly *)
    if aux (prefix i trail) 10 && not(aux (prefix (i+1) trail) 10) && Option.is_none !result then
      result := Some (prefix i trail)
  done;
  (* if no subtrail is found, the subtrail defaults to empty *)
  if Option.is_none !result then [] else Option.get !result

(** backtrack rule *)
let backtrack (state : scl_state) =
  let lsigma, _ = List.hd state.trail in 
  let dvl, sigma =  match state.conflict_closure with
    | Closure (c, s) -> c, s
    | Bot -> failwith "cannot recover"
    | Top -> failwith "not in conflict state" in
  let _l = de_apply_subst_lit sigma lsigma in
  let subtrail = min_subtrail state.trail dvl in
  let k = level_of_trail subtrail  in
  {state with trail = subtrail ; learned_clauses = dvl :: state.learned_clauses; decision_level = k; conflict_closure = Top}

