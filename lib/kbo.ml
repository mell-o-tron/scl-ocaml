open Ast
open Rewriting

let rec all_occurrences (sym : string) (t : term) = match t with
  | Var _ -> []
  | Const a -> [a]
  | Func (n, l) -> n :: (List.map (all_occurrences sym) l |> List.flatten)

let rec sum_list lst =
  match lst with
  | [] -> 0
  | x :: xs -> x + sum_list xs  

let term_weight (w : int StringMap.t) (signature : (string * int) list) (t : term) =
  let v = get_all_vars_term t in
  let weighted_occs = List.map (fun (s, _) -> 
    (all_occurrences s t |> List.length) * (StringMap.find s w)) signature in
  sum_list weighted_occs + (dedup v |> List.length)

let variable_inclusion_req (t1 : term) (t2 : term) =
  List.for_all (fun x -> List.length (all_occurrences x t1) >= List.length (all_occurrences x t2)) (get_all_vars_term t1 @ get_all_vars_term t2 |> dedup)

let has_precedence (precedence : string list) n1 n2 = 
  List.find_index (fun s -> s = n1) precedence > List.find_index (fun s -> s = n2) precedence

let rec lex_compare (w : int StringMap.t) (signature : (string * int) list) (precedence : string list) l1 l2 = match l1, l2 with
| t1 :: l1, t2 :: l2 -> if t1 == t2 then lex_compare w signature precedence l1 l2 else
  kbo_gt w signature precedence t1 t2 
| [], _ :: _ -> true
| _ :: _, [] -> false
| _ -> false

and kbo_gt (w : int StringMap.t) (signature : (string * int) list) (precedence : string list) (t1 : term) (t2 : term) = 
  (* weigth requirement *)
  if term_weight w signature t1 > term_weight w signature t2 
  (* variable occurrence requirement *)
  &&  variable_inclusion_req t1 t2
  then true
  else match t1, t2 with
  | Func (_) , Var x -> List.mem x (get_all_vars_term t1)
  | Func (n1, _), Func (n2, _)
  | Const n1, Const n2 when not(n1 = n2) -> 
     (* The literal ordering is defined by which comes first in the precedence list *)
      has_precedence precedence n1 n2
  | Func (_, l1), Func (_, l2) -> 
    lex_compare w signature precedence l1 l2
  | _ -> false

let kbo_cmp (w : int StringMap.t) (signature : (string * int) list) (precedence : string list) (t1 : term) (t2 : term) = 
  if t1 = t2 then 0
  else if kbo_gt w signature precedence t1 t2 then 1 else -1

let atom_weight (w : int StringMap.t) (signature : (string * int) list) (Atom (n, tl)) = 
  StringMap.find n w + sum_list (List.map (term_weight w signature) tl)

let kbo_atoms (w : int StringMap.t) (signature : (string * int) list) (precedence : string list) (Atom(n1, l1) as a1 : atom) (Atom(n2, l2) as a2 : atom) =
  if atom_weight w signature a1 > atom_weight w signature a2
    (* variable occurrence requirement *)
    &&  List.for_all2 (fun t1 t2 -> variable_inclusion_req t1 t2) l1 l2
    then true
    else if n1 != n2 && has_precedence precedence n1 n2 then true
    else if n1 == n2 then lex_compare w signature precedence l1 l2
    else false

let kbo_atoms_cmp (w : int StringMap.t) (signature : (string * int) list) (precedence : string list) (a1 : atom) (a2 : atom) =
  if a1 = a2 then 0
  else if kbo_atoms w signature precedence a1 a2 then 1 else -1

let multiplicity mset elem = List.filter (fun x -> x = elem) mset |> List.length

let kbo_atom_multisets (w : int StringMap.t) (signature : (string * int) list) (precedence : string list) (al1 : atom list) (al2 : atom list) =
  let elems = (al1 @ al2 |> dedup) in
  not(al1 = al2) && List.for_all (
    fun m -> (not (multiplicity al2 m > multiplicity al1 m) || 
    List.exists (fun m' -> kbo_atoms w signature precedence m' m && multiplicity al1 m' > multiplicity al2 m') elems)
  ) elems

let kbo_lits (w : int StringMap.t) (signature : (string * int) list) (precedence : string list) (l1 : literal) (l2 : literal) = 
  let mset1 = match l1 with
  | Pos (Atom _ as a) -> [a]
  | Neg (Atom _ as a) -> [a ; a]
  in 
  let mset2 = match l2 with
  | Pos (Atom _ as a) -> [a]
  | Neg (Atom _ as a) -> [a ; a] in
  kbo_atom_multisets w signature precedence mset1 mset2

let kbo_lits_cmp (w : int StringMap.t) (signature : (string * int) list) (precedence : string list) (l1 : literal) (l2 : literal) =
  if l1 = l2 then 0
  else if kbo_lits w signature precedence l1 l2 then 1 else -1

let kbo_literal_multisets (w : int StringMap.t) (signature : (string * int) list) (precedence : string list) (ll1 : literal list) (ll2 : literal list) =
  let elems = (ll1 @ ll2 |> dedup) in
  not(ll1 = ll2) && List.for_all (
    fun m -> (not (multiplicity ll2 m > multiplicity ll1 m) || 
    List.exists (fun m' -> kbo_lits w signature precedence m' m && multiplicity ll1 m' > multiplicity ll2 m') elems)
  ) elems

let kbo_clauses (w : int StringMap.t) (signature : (string * int) list) (precedence : string list) (c1 : clause) (c2 : clause) =
  kbo_literal_multisets w signature precedence c1 c2

let kbo_clauses_cmp (w : int StringMap.t) (signature : (string * int) list) (precedence : string list) (c1 : clause) (c2 : clause) =
  if c1 = c2 then 0
  else if kbo_clauses w signature precedence c1 c2 then 1 else -1