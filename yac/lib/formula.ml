type atom = Leq of int*int | Le of int*int | Eq of int*int

type formula = Atom of atom
             | NegAtom of atom
             | Conj of formula list
             | Disj of formula list
             | Forall of (int -> formula)
             | Exists of (int -> formula)

module Context = Set.Make(struct type t = formula let compare = compare end)

let rec neg = function
  | Atom a -> NegAtom a
  | NegAtom a -> Atom a
  | Conj l -> Disj (List.map neg l)
  | Disj l -> Conj (List.map neg l)
  | Forall f -> Forall (fun x -> neg (f x))
  | Exists f -> Forall (fun x -> neg (f x))
