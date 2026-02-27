open Formula

let rec print_term = function
  | Var str -> print_string str
  | Nat num -> print_int (to_int num)
  | Func t -> print_string "f("; print_term t; print_string ")"

let print_atom = function
  | Leq (t, t') -> print_term t; print_string " ≤ "; print_term t'
  | Le  (t, t') -> print_term t; print_string " < "; print_term t'
  | Eq  (t, t') -> print_term t; print_string " = "; print_term t'
  | Neq (t, t') -> print_term t; print_string " ≠ "; print_term t'

let rec print_formula = function
  | Atom a -> print_atom a
  | Conj (frm, frm') -> print_string "("; print_formula frm; print_string " ∧ "; print_formula frm'; print_string ")"
  | Disj (frm, frm') -> print_string "("; print_formula frm; print_string " ∨ "; print_formula frm'; print_string ")"
  | Forall (str, frm) -> print_string ("∀ " ^ str ^ " ∈ ℕ. "); print_formula frm
  | Exists (str, frm) -> print_string ("∃ " ^ str ^ " ∈ ℕ. "); print_formula frm
