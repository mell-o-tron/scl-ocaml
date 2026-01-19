open Scl.Ast
open Scl.Rules
open Scl.Exceptions
open Scl.Kbo
open Scl.Rewriting
open Scl.Guarded

(** List of rules for seeking conflicts. *)
let seek_conflict_rules : ((scl_state -> rule_result) list) = [
  (fun state -> (Printf.printf("applying rule conflict\n"); conflict state)) ;
  (fun state -> (Printf.printf("applying rule propagate\n"); propagate state));
  (fun state -> (Printf.printf("applying rule decide\n"); 
    try let decision_literal, s = next_decision_literal (state) in
    Printf.printf "decided literal: %s\n" (pretty_lit decision_literal);
    R_State (decide decision_literal s state) with GoToNextRule _ -> R_Continue state))
]

(** List of rules for solving conflicts. *)
let solve_conflict_rules : ((scl_state -> rule_result) list) = [
  (fun state ->  Printf.printf("applying rule skip\n"); skip state) ;
  (fun state ->  Printf.printf("applying rule factorize\n"); factorize state);
  (fun state -> Printf.printf("applying rule resolve\n"); resolve state);
  (fun state -> Printf.printf("applying rule backtrack\n"); backtrack state)
]

(** Applies a rule to the state; if one rule cannot be applied, fall back to the next one. *)
let apply_rule (state : scl_state) = match state with
  | {conflict_closure = Top; _ } -> 
    let rec aux n state =

      match (if n < List.length seek_conflict_rules then
        List.nth (seek_conflict_rules) n state
      else 
        failwith "was unable to apply any conflict seek rule.") with
        | R_State s -> R_State s
        | R_Continue _ -> aux (n+1) state
        | R_Sat t -> R_Sat t
        | R_Unsat -> R_Unsat

    in 
    aux 0 state

  | {conflict_closure = Closure ([], _) ; _} | {conflict_closure = Bot; _ } -> R_Unsat

  | _ -> let rec aux n state =
    match
      if n < List.length solve_conflict_rules then
        List.nth (solve_conflict_rules) n state
      else 
        failwith "was unable to apply any conflict solving rule." with
      | R_State s -> R_State s
      | R_Continue _ -> aux (n+1) state
      | R_Sat t -> R_Sat t
      | R_Unsat -> R_Unsat
  in 
  aux 0 state
    
let check_sat state = 
  let s = get_subst_from_trail state.trail in
  let vars = get_all_vars_state state in
  let vars_in_s = List.map (fun (s, _) -> s) (s |> StringMap.to_list) in
  if(List.for_all (fun x -> List.mem x vars_in_s) vars) then
    let s = get_subst_from_trail state.trail in
    Printf.printf "subst from trail: %s\n" (pretty_subst s);
    List.for_all (fun c -> 
      let c1 = (apply_subst_clause s c) in
      Printf.printf "checking if clause %s is true in trail %s\n" (pretty_clause c1) (pretty_trail state.trail);
      is_true_in_trail (apply_subst_clause s c1) state.trail) state.clauses
  else false

let rec _keep_applying_rules state = 
    let res = apply_rule state in
    match res with 
    | R_State s ->
      print_state s;
      flush stdout;
      (* let _ = read_line () in *)
      if check_sat s then 
        print_endline "Found satisfying interpretation"
      else 
      _keep_applying_rules s

    | R_Unsat -> print_endline "Refutation Found"
    | R_Sat _ -> print_endline "Found satisfying interpretation"
    | R_Continue _ -> failwith "should not happen"

let _main () = 
  signature := [("a", 0); ("b", 0)];
  let precedence = ["R"; "Q"; "P"; "b"; "a"] in
  term_ordering := kbo_cmp (StringMap.of_list ["a", 1 ; "b", 1]) (!signature) precedence;
  literal_ordering := kbo_lits_cmp (StringMap.of_list ["a", 1 ; "b", 1; "P", 1; "Q", 1; "R", 1]) (!signature) precedence;
  clause_ordering := kbo_clauses_cmp (StringMap.of_list ["a", 1 ; "b", 1; "P", 1; "Q", 1; "R", 1]) (!signature) precedence;

  let _n =  [[Pos (Atom("P", [Var "x"])); Pos (Atom("Q", [Const "b"]))];
            [Pos (Atom("P", [Var "x"])); Neg (Atom("Q", [Var "y"]))];
            [Neg (Atom("P", [Const "a"])); Pos (Atom("Q", [Var "x"]))];
            [Neg (Atom("P", [Var "x"])); Neg (Atom("Q", [Const "b"]))]] in

  let _n1 = [[Pos (Atom("P", [Var "x"]))] ; 
             [Neg (Atom("P", [Var "x"])) ; Pos(Atom("Q", [Var "x"]))];
             [Pos(Atom("Q", [Const("b")]))]
            ] in

  let _n3 = [[Pos (Atom("P", [Var "x"])) ; Pos (Atom("Q", [Var "x"]))] ; 
             [Neg (Atom("P", [Var "x"])) ; Neg (Atom("Q", [Var "x"]))]] in

  let _n4 = [[Pos (Atom("P", [Var "x"])) ; Neg (Atom("R", [Var "x"]))] ; 
             [Pos (Atom("Q", [Var "x"])) ; Pos (Atom("R", [Var "x"]))] ;
             [Pos (Atom ("Q", [Var "x"]))]] in

  let _initial_state = {trail = [] ; clauses = _n4; learned_clauses = []; limiting_literal = Pos(Atom("R", [Const ("b")]));
                       decision_level = 0 ; conflict_closure = Top} in

  (* keep_applying_rules _initial_state *)

  guarded_debug_scl _initial_state !literal_ordering (Const "a")
;;

let _test () = 
  signature := [("a", 0); ("b", 0)];
  (* R > Q > P > b > a *)
  let precedence = ["R"; "Q"; "P"; "b"; "a"] in
  let beta = Pos(Atom("R", [Const ("b")])) in
  let w = StringMap.of_list ["a", 1 ; "b", 1; "P", 1; "Q", 1; "R", 1] in
  (* let res = kbo_cmp w (!signature) precedence (Const "a") (Const "b") in *)
  let res = kbo_lits_cmp w (!signature) precedence beta (Pos(Atom("Q", [Const("a")]))) in 
  Printf.printf "%d\n" res

;;

_main()