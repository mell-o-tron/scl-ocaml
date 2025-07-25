open Ast
open Exceptions

(** Apply a substitution to a term *)
let rec apply_subst_term (s : subst) (t : term) = match t with
  | Var v -> (try StringMap.find v s with _ -> Var v)
  | Func (n, tl) -> Func (n, List.map (apply_subst_term s) tl)
  | Const _ -> t

(** sigma1 AND THEN sigma2 *)
let compose (sigma1 : subst) (sigma2 : subst) : subst =
  let sigma1' = StringMap.map (apply_subst_term sigma2) sigma1 in
  StringMap.union (fun _ t1 _ -> Some t1) sigma1' sigma2

(** deletes all equalities between equal terms *)
let delete (eqs : (term * term) list) = 
  List.filter (fun (t1, t2) -> not(t1 = t2)) eqs

(** generates new equalities from function eqs *)
let decompose (eqs : (term * term) list) = 
  let aux (t1, t2) = match t1, t2 with
  Func (n1, l1) , Func (n2, l2) when n1 = n2 && List.length l1 = List.length l2 ->  
    List.map2 (fun t1 t2 -> (t1, t2)) l1 l2
  | _ -> [(t1, t2)]
  in
  List.map aux eqs |> List.flatten

(** Brings variables to the left *)
let swap (eqs : (term * term) list) = 
  let aux ((t1, t2) : term * term) = match (t1, t2) with
    | (Const _ | Func _), Var _ -> (t2, t1)
    | _ -> (t1, t2)
in List.map aux eqs

(** substitutes variable x with term t in set eqs *)
let subst_in_eqset (x : string) (t : term) (eqs : (term * term) list) = 
  let rec aux (t1 :  term) = match (t1) with
    | Var y -> if x = y then t else t1
    | Const _ -> t1
    | Func (n, l) -> Func (n, List.map aux l)
  in
  List.map (fun (t1, t2) -> (aux t1, aux t2)) eqs 

let rec term_vars (t : term) = match t with
  | Var y -> [y]
  | Const _ -> []
  | Func (_, l) -> List.map (term_vars) l |> List.flatten

let eqs_vars (eqs : (term * term) list) = 
  List.map (fun (t1, t2) -> term_vars t1 @ term_vars t2) eqs |> List.flatten

let is_var t = match t with
  | Var _ -> true
  | _ -> false

let is_in_varlist (t : term) (vl : string list) = match t with
| Var x -> List.mem x vl 
| _ -> failwith "term is not a variable"

let get_var_name (t : term) = match t with
| Var x -> x
| _ -> failwith "term is not a variable"

(** Subsitutes variables found in equalities *)
let eliminate (eqs : (term * term) list) = 
  try
    let pair = List.find (fun (t1, t2) -> is_var t1 && is_in_varlist t1 (eqs_vars eqs) && not(is_in_varlist t1 (term_vars t2))) eqs in
    let rest = List.filter (fun p -> not (p = pair)) eqs in
    pair :: subst_in_eqset (get_var_name (fst pair)) (snd pair) rest
  with Not_found -> eqs

let term_conflict t1 t2 = match t1, t2 with
  | Func (n1, l1), Func (n2, l2) -> 
    if n1 = n2 && List.length l1 = List.length l2 then false else true
  | Const a, Const b -> if a = b then false else true
  | _ -> false

let conflict (eqs : (term * term) list) = 
  if (List.exists (fun (t1, t2) -> term_conflict t1 t2) eqs) then raise CannotUnify else eqs

let occur_check (eqs : (term * term) list) = 
  if List.exists (fun (t1, t2) -> is_var t1 && is_in_varlist t1 (term_vars t2)) eqs then 
  raise CannotUnify else eqs

  
let rec unify_equalities (eqs : (term * term) list) =  
  let aux (eqs : (term * term) list) = 
    let eqs = delete eqs in
    let eqs = decompose eqs in
    let eqs = swap eqs in
    let eqs = eliminate eqs in
    let eqs = conflict eqs in
    occur_check eqs
  in 
  try 
  let res = aux eqs in
  if res = eqs then (Some res) else unify_equalities res
  with CannotUnify -> None

let unify_lits_to_pair l1 l2 = match l1, l2 with
| Pos (Atom (n1, tl1)), Pos (Atom (n2, tl2)) when 
  n1 = n2 && List.length tl1 = List.length tl2 -> unify_equalities (List.map2 (fun t1 t2 -> (t1, t2)) tl1 tl2)
| Neg (Atom (n1, tl1)), Neg (Atom (n2, tl2)) when 
  n1 = n2 && List.length tl1 = List.length tl2 -> unify_equalities (List.map2 (fun t1 t2 -> (t1, t2)) tl1 tl2)
| _ -> None

let unify_literal l1 l2 = 
  (* Printf.printf "trying to unify literals: %s, %s\n" (pretty_lit l1) (pretty_lit l2); *)
let pairlistopt = unify_lits_to_pair l1 l2

in if Option.is_some pairlistopt then 
  let listopt = Option.get pairlistopt in
  let listopt = List.map (fun (t1, t2) -> (get_var_name t1, t2)) listopt in
  Some (listopt |> StringMap.of_list)
else None

let unify_literal_with_lits (l1 : literal) (c : clause) = 
  let lis = List.map (fun l -> unify_lits_to_pair l1 l) c in
  let pairlistopt = if List.for_all Option.is_some lis then Some(List.map Option.get lis |> List.flatten) else None in
  if Option.is_some pairlistopt then 
    let listopt = Option.get pairlistopt in
    let listopt = List.map (fun (t1, t2) -> (get_var_name t1, t2)) listopt in
    Some (listopt |> StringMap.of_list)
else None
