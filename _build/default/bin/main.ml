open Scl.Ast
open Scl.Rules
open Scl.Exceptions

let _apply_rules (state : scl_state) = match state with
  | {conflict_closure = Top; _ } -> (
    try
      Printf.printf("applying rule conflict\n");
      conflict state
    with 
      GoToNextRule _ -> (
        try 
        Printf.printf("applying rule propagate\n");
        propagate state
        with GoToNextRule _ -> (
          Printf.printf("applying rule decision\n");
          let decision_literal, s = next_decision_literal (state) in

          Printf.printf "decided literal: %s\n" (show_literal decision_literal);
          decide decision_literal s state
        )
      ))

  | _ ->
    try 
    Printf.printf("applying rule skip\n");
      skip state
    with GoToNextRule _ -> (
      try 
        Printf.printf("applying rule factorize\n");
        factorize state
      with GoToNextRule _ -> (
        try Printf.printf("applying rule resolve\n"); resolve state with
        GoToNextRule _ -> (
          Printf.printf("applying rule backtrack\n");
          backtrack state
        )
      ) 
    )

let rec keep_applying_rules state = 
  let res = _apply_rules state in
  print_state res;
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