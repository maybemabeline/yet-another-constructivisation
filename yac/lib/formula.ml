type term = Var of string | Nat of int

type atom = Leq of term*term | Le of term*term | Eq of term*term

type formula = Atom of atom
             | NegAtom of atom
             | Conj of formula list
             | Disj of formula list
             | Forall of string * formula
             | Exists of string * formula

let subst_term trm str = function
  | Var str' when str = str' -> trm
  | y -> y

let subst_atom trm str = function
  | Leq (t1, t2) -> Leq (subst_term trm str t1, subst_term trm str t2)
  | Le (t1, t2) -> Le (subst_term trm str t1, subst_term trm str t2)
  | Eq (t1, t2) -> Eq (subst_term trm str t1, subst_term trm str t2)

let rec subst_formula trm str = function
  | Atom a -> Atom (subst_atom trm str a)
  | NegAtom a -> NegAtom (subst_atom trm str a)
  | Conj l -> Conj (List.map (subst_formula trm str) l)
  | Disj l -> Disj (List.map (subst_formula trm str) l)
  | Forall (str', frm) ->
     if str = str' then
       Forall (str, frm)
     else
       Forall (str', subst_formula trm str frm)
  | Exists (str', frm) ->
     if str = str' then
       Exists (str, frm)
     else
       Exists (str', subst_formula trm str frm)


module Context = Set.Make(struct type t = formula let compare = compare end)

let rec neg = function
  | Atom a -> NegAtom a
  | NegAtom a -> Atom a
  | Conj l -> Disj (List.map neg l)
  | Disj l -> Conj (List.map neg l)
  | Forall (x, f) -> Exists (x, neg f)
  | Exists (x, f) -> Forall (x, neg f)
