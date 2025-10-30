type nat = Zero | Succ of nat

let rec to_int = function
  | Zero -> 0
  | Succ n -> (to_int n) + 1

let rec of_int n =
  if n = 0 then
    Zero
  else if n > 0 then
    Succ (of_int (n - 1))
  else
    failwith "Negative integer"

type term = Var of string | Nat of nat | Func of term

type atom = Leq of term*term | Le of term*term | Eq of term*term

type formula = Atom of atom
             | NegAtom of atom
             | Conj of formula*formula
             | Disj of formula*formula
             | Forall of string * formula
             | Exists of string * formula

let rec neg = function
  | Atom a -> NegAtom a
  | NegAtom a -> Atom a
  | Conj (f, g) -> Disj (neg f, neg g)
  | Disj (f, g) -> Conj (neg f, neg g)
  | Forall (x, f) -> Exists (x, neg f)
  | Exists (x, f) -> Forall (x, neg f)

let rec subst_term trm str = function
  | Var str' when str = str' -> trm
  | Func t -> Func (subst_term trm str t)
  | y -> y

let eval fn = function
  | Func (Nat n) -> Nat (fn n)
  | y -> y

let subst_atom fn trm str = function
  | Leq (t1, t2) -> Leq (t1 |> subst_term trm str |> eval fn, t2 |> subst_term trm str |> eval fn)
  | Le  (t1, t2) -> Le  (t1 |> subst_term trm str |> eval fn, t2 |> subst_term trm str |> eval fn)
  | Eq  (t1, t2) -> Eq  (t1 |> subst_term trm str |> eval fn, t2 |> subst_term trm str |> eval fn)

let rec subst_formula fn trm str = function
  | Atom a -> Atom (subst_atom fn trm str a)
  | NegAtom a -> NegAtom (subst_atom fn trm str a)
  | Conj (f, g) -> Conj (subst_formula fn trm str f, subst_formula fn trm str g)
  | Disj (f, g) -> Disj (subst_formula fn trm str f, subst_formula fn trm str g)
  | Forall (str', frm) ->
     if str = str' then
       Forall (str, frm)
     else
       Forall (str', subst_formula fn trm str frm)
  | Exists (str', frm) ->
     if str = str' then
       Exists (str, frm)
     else
       Exists (str', subst_formula fn trm str frm)
