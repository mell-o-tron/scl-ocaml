module StringMap = Map.Make(String);;


type term = Const of string | Var of string | Func of string * term list [@@deriving show]
type atom = Atom of string * term list [@@deriving show]
type literal = Pos of atom | Neg of atom [@@deriving show]
type clause = literal list [@@deriving show]
type subst = term StringMap.t

let pp_subst fmt subst =
  let pp_binding fmt (k, v) =
    Format.fprintf fmt "%s ↦ %a" k pp_term v
  in
  Format.fprintf fmt "@[<v 1>{@ ";
  StringMap.iter (fun k v -> Format.fprintf fmt "%a;@ " pp_binding (k, v)) subst;
  Format.fprintf fmt "@]}@]"


type closure = Top | Bot | Closure of clause * subst [@@deriving show]
type annot = Level of int | Pred of closure [@@deriving show]


type scl_state = {
  trail : (literal * annot) list;
  clauses : clause list;
  learned_clauses : clause list;
  limiting_literal : literal;
  decision_level : int;
  conflict_closure : closure
} [@@deriving show]

(** applies a substitution to a term*)
let rec apply_subst_term (s : subst) (t : term) = match t with
  | Var v -> (try StringMap.find v s with _ -> Var v)
  | Func (n, tl) -> Func (n, List.map (apply_subst_term s) tl)
  | Const _ -> t

(** applies a substitution to an atom *)
let apply_subst_atom (s : subst) (Atom(pname, tl)) = Atom (pname, List.map (apply_subst_term s) tl)

(** applies a substitution to a literal*)
let apply_subst_lit (s : subst) (l : literal) = match l with 
  | Pos (a) -> Pos(apply_subst_atom s a)
  | Neg (a) -> Neg(apply_subst_atom s a)

(** Negates a literal *)
let lit_neg (l : literal) = match l with 
| Pos (a) -> Neg a
| Neg (a) -> Pos a

(** applies a substitution to a clause *)
let apply_subst_clause (s : subst) (c : clause) = List.map (apply_subst_lit s) c 

let rec pretty_term (t) = match t with
  | Const s -> s
  | Var s -> s
  | Func (s, l) -> Printf.sprintf "%s(%s)" s ((List.map (pretty_term) l) |> String.concat ", ")

let pretty_subst (subst : term StringMap.t) =
  let pp_binding (k, t) =
    Printf.sprintf "%s ↦ %s" k (pretty_term t)
  in
  "{" ^ (List.map (fun (k, t) -> pp_binding (k, t)) (StringMap.to_list subst) |> String.concat ", ") ^ "}"


let pretty_lit (l : literal) = match l with
  | Pos(Atom (name, l)) -> Printf.sprintf "%s(%s)" name ((List.map (pretty_term) l) |> String.concat ", ")
  | Neg(Atom (name, l)) -> Printf.sprintf "¬%s(%s)" name ((List.map (pretty_term) l) |> String.concat ", ")

let pretty_clause (c : clause) = ((List.map (pretty_lit) c) |> String.concat " ∨ ")
let pretty_closure c = match c with
  | Top -> "⊤"
  | Bot -> "⊥"
  | Closure (c, s) -> Printf.sprintf "%s * %s" (pretty_clause c) (pretty_subst s)
let pretty_annot a = match a with
  | Level(k) -> string_of_int k
  | Pred (c) -> pretty_closure c

let pretty_trail (l : (literal * annot) list) =
  List.map (fun (l, a) -> Printf.sprintf "(%s, %s)" (pretty_lit l) (pretty_annot a)) l |> String.concat ", "

let pretty_state (state : scl_state) = 
  Printf.sprintf "Γ:\t\t%s\nclauses:\t%s\nlearned:\t%s\nβ:\t\t%s\nlevel:\t\t%d\nconflict:\t%s\n" 
    (pretty_trail state.trail) 
    (List.map (pretty_clause) state.clauses |> String.concat ", ")
    (List.map (pretty_clause) state.learned_clauses |> String.concat ", ")
    (pretty_lit state.limiting_literal)
    (state.decision_level)
    (pretty_closure state.conflict_closure)