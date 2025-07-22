open Ast

(** Apply a substitution to a term *)
let rec apply_term (sigma : subst) (t : term) : term =
  match t with
  | Const _ -> t
  | Var x ->
    (match StringMap.find_opt x sigma with
     | None   -> t
     | Some t' -> apply_term sigma t')
  | Func(f, args) ->
    Func(f, List.map (apply_term sigma) args)

(** Compose two substitutions: sigma₂ ∘ sigma₁, meaning apply sigma₁ then sigma₂ *)
let compose (sigma2 : subst) (sigma1 : subst) : subst =
  let sigma1' = StringMap.map (apply_term sigma2) sigma1 in
  StringMap.union (fun _ t1 _ -> Some t1) sigma1' sigma2

(** Occurs-check: does variable x occur inside term t? *)
let rec occurs (x : string) (t : term) : bool =
  match t with
  | Const _      -> false
  | Var y        -> x = y
  | Func(_, args) ->
    List.exists (occurs x) args

(** Unify two terms under current substitution sigma, returning an updated sigma or failure *)
let rec unify_term (sigma : subst) (s : term) (t : term) : subst option =
  let s = apply_term sigma s in
  let t = apply_term sigma t in
  match (s, t) with
  | Const a, Const b when a = b ->
    Some sigma
  | Var x, t
  | t, Var x ->
    if t = Var x then Some sigma
    else if occurs x t then
      None  (* would create infinite term *)
    else
      Some (StringMap.add x t sigma)
  | Func(f, ss), Func(g, ts)
    when f = g && List.length ss = List.length ts ->
    unify_terms sigma ss ts
  | _ ->
    None

(** Unify two lists of terms pairwise *)
and unify_terms (sigma : subst) (ss : term list) (ts : term list) : subst option =
  match (ss, ts) with
  | [], [] -> Some sigma
  | s::ss', t::ts' ->
    (match unify_term sigma s t with
     | None    -> None
     | Some sigma' -> unify_terms sigma' ss' ts')
  | _ -> None  (* arity mismatch *)

(** Unify two atoms: same predicate name and arity *)
let unify_atom (sigma : subst) (Atom(p, ss)) (Atom(q, ts)) : subst option =
  if p = q && List.length ss = List.length ts then
    unify_terms sigma ss ts
  else
    None

(** Unify two literals. *)
let unify_literal (sigma : subst) (l1 : literal) (l2 : literal) : subst option =
  match (l1, l2) with
  | Pos a1, Pos a2
  | Neg a1, Neg a2 ->
    unify_atom sigma a1 a2
  | _ ->
    None