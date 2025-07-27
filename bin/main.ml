open Scl.Ast
open Scl.Rules
open Scl.Exceptions
open Scl.Kbo

(** List of rules for seeking conflicts. *)
let seek_conflict_rules : ((scl_state -> scl_state) list) = [
  (fun state -> (Printf.printf("applying rule conflict\n"); conflict state)) ;
  (fun state -> (Printf.printf("applying rule propagate\n"); propagate state));
  (fun state -> (Printf.printf("applying rule decide\n"); 
    let decision_literal, s = next_decision_literal (state) in
    Printf.printf "decided literal: %s\n" (pretty_lit decision_literal);
    decide decision_literal s state))
]

(** List of rules for solving conflicts. *)
let solve_conflict_rules : ((scl_state -> scl_state) list) = [
  (fun state ->  Printf.printf("applying rule skip\n"); skip state) ;
  (fun state ->  Printf.printf("applying rule factorize\n"); factorize state);
  (fun state -> Printf.printf("applying rule resolve\n"); resolve state);
  (fun state -> Printf.printf("applying rule backtrack\n"); backtrack state)
]

(** Applies a rule to the state; if one rule cannot be applied, fall back to the next one. *)
let apply_rule (state : scl_state) = match state with
  | {conflict_closure = Top; _ } -> 
    let rec aux n state =
      try (
        if n < List.length seek_conflict_rules then
          List.nth (seek_conflict_rules) n state
        else 
          state
      ) with GoToNextRule s -> Printf.printf "   -> %s\n\n" s; aux (n+1) state
    in 
    aux 0 state

  | {conflict_closure = Closure ([], _) ; _} | {conflict_closure = Bot; _ } -> raise (FoundRefutation)

  | _ -> let rec aux n state =
    try (
      if n < List.length solve_conflict_rules then
        List.nth (solve_conflict_rules) n state
      else 
        state
    ) with GoToNextRule s -> Printf.printf "   -> %s\n\n" s; aux (n+1) state
  in 
  aux 0 state
    
let rec keep_applying_rules state = 
  try
    let res = apply_rule state in
    print_state res;
    flush stdout;
    (* let _ = read_line () in *)
    keep_applying_rules res
  with FoundRefutation -> print_endline "Refutation Found"
let _main () = 
  signature := [("a", 0); ("b", 0)];
  let precedence = ["R"; "Q"; "P"; "b"; "a"] in
  term_ordering := kbo_cmp (StringMap.of_list ["a", 1 ; "b", 1]) (!signature) precedence;
  literal_ordering := kbo_lits_cmp (StringMap.of_list ["a", 1 ; "b", 1; "P", 1; "Q", 1; "R", 1]) (!signature) precedence;
  clause_ordering := kbo_clauses_cmp (StringMap.of_list ["a", 1 ; "b", 1; "P", 1; "Q", 1; "R", 1]) (!signature) precedence;


  let n =  [[Pos (Atom("P", [Var "x"])); Pos (Atom("Q", [Const "b"]))];
            [Pos (Atom("P", [Var "x"])); Neg (Atom("Q", [Var "y"]))];
            [Neg (Atom("P", [Const "a"])); Pos (Atom("Q", [Var "x"]))];
            [Neg (Atom("P", [Var "x"])); Neg (Atom("Q", [Const "b"]))]] in

  let _initial_state = {trail = [] ; clauses = n; learned_clauses = []; limiting_literal = Pos(Atom("R", [Const ("b")]));
                       decision_level = 0 ; conflict_closure = Top} in

  keep_applying_rules _initial_state
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