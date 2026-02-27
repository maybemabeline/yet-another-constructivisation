type tm =
  | Var of var
  | Num of nat
  | Apply of tm * tm

and nat = Zero | Succ of nat

and var = tm Bindlib.var

and atom =
  | Leq of tm * tm
  | Le  of tm * tm
  | Eq  of tm * tm

and frm =
  | Atom of atom
  | NegAtom of atom
  | Conj of frm * frm
  | Disj of frm * frm
  | Forall of frm binder
  | Exists of frm binder

and prf =
  | Focus of frm
  | True
  | Conj of prf * prf
  | Disj of prf
  | Forall of (nat -> prf)
  | Exists of tm * prf
  | Cut of frm * prf * prf

and 'a binder = (tm, 'a) Bindlib.binder
