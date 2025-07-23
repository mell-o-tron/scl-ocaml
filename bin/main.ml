open Scl.Ast
open Scl.Rules
open Scl.Exceptions

let seek_conflict_rules : ((scl_state -> scl_state) list) = [
  (fun state -> (Printf.printf("applying rule conflict\n"); conflict state)) ;
  (fun state -> (Printf.printf("applying rule propagate\n"); propagate state));
  (fun state -> (Printf.printf("applying rule decide\n"); 
    let decision_literal, s = next_decision_literal (state) in
    Printf.printf "decided literal: %s\n" (pretty_lit decision_literal);
    decide decision_literal s state))
]

let solve_conflict_rules : ((scl_state -> scl_state) list) = [
  (fun state ->  Printf.printf("applying rule skip\n"); skip state) ;
  (fun state ->  Printf.printf("applying rule factorize\n"); factorize state);
  (fun state -> Printf.printf("applying rule resolve\n"); resolve state);
  (fun state -> Printf.printf("applying rule backtrack\n"); backtrack state)
]

let _apply_rules (state : scl_state) = match state with
  | {conflict_closure = Top; _ } -> 
    let rec aux n state =
      try (
        if n < List.length seek_conflict_rules then
          List.nth (seek_conflict_rules) n state
        else 
          state
      ) with GoToNextRule _ -> aux (n+1) state
    in 
    aux 0 state

  | {conflict_closure = Bot; _ } -> raise (FoundRefutation)

  | _ -> let rec aux n state =
    try (
      if n < List.length solve_conflict_rules then
        List.nth (solve_conflict_rules) n state
      else 
        state
    ) with GoToNextRule _ -> aux (n+1) state
  in 
  aux 0 state
    
let rec keep_applying_rules state = 
  let res = _apply_rules state in
  print_state res;
  flush stdout;
  let _ = read_line () in
  keep_applying_rules res

let main () = 
  signature := [("a", 0); ("b", 0)];
  (* Placeholder: this should be something like unit-weight KBO in complete implementation *)
  literal_ordering := (fun _ l2 -> ( 
    if l2 = Pos(Atom("R", [Const ("b")])) then -1
    else failwith "illegal comparison, second argument is not beta."
  ));
  (* Placeholder: this should be something like unit-weight KBO in complete implementation *)
  clause_ordering := (fun _ c2 -> ( 
    if c2 = [Pos(Atom("R", [Const ("b")]))] then -1
    else failwith "illegal comparison, second argument is not [beta]."
  ));


  let n =  [[Pos (Atom("P", [Var "x"])); Pos (Atom("Q", [Const "b"]))];
            [Pos (Atom("P", [Var "x"])); Neg (Atom("Q", [Var "y"]))];
            [Neg (Atom("P", [Const "a"])); Pos (Atom("Q", [Var "x"]))];
            [Neg (Atom("P", [Var "x"])); Neg (Atom("Q", [Const "b"]))]] in

  let _initial_state = {trail = [] ; clauses = n; learned_clauses = []; limiting_literal = Pos(Atom("R", [Const ("b")]));
                       decision_level = 0 ; conflict_closure = Top} in

  keep_applying_rules _initial_state
;;

main()