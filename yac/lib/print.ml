open Formula

let print_term = function
  | Var str -> print_string str
  | Nat num -> print_int num

let print_atom = function
  | Leq (t, t') -> print_term t; print_string " ≤ "; print_term t'
  | Le (t, t')  -> print_term t; print_string " < "; print_term t'
  | Eq (t, t')  -> print_term t; print_string " = "; print_term t'

let rec print_formula = function
  | Atom a -> print_atom a
  | NegAtom a -> print_string "¬ "; print_atom a
  | Conj _ -> failwith "not done yet"
  | Disj _ -> failwith "not done yet"
  | Forall (str, frm) -> print_string ("∀ " ^ str ^ " ∈ ℕ. "); print_formula frm
  | Exists (str, frm) -> print_string ("∃ " ^ str ^ " ∈ ℕ. "); print_formula frm

let rec print_context = function
  | [] -> ()
  | x :: xs -> print_formula x; print_string ", "; print_context xs
