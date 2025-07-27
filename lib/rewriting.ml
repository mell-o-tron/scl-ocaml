open Ast

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


(** gets all the free variables of a clause*)
let get_all_vars_clause (c : clause) = 
  List.map (fun l -> get_all_vars_literal l) c |> List.flatten |> dedup

