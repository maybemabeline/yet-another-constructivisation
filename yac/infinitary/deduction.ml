open Formula

type proof = True of atom
           | False of atom
           | ConjI of formula * formula * proof * proof
           | DisjI of formula * formula * proof
           | ForallI of string * formula * (nat -> proof)
           | ExistsI of string * formula * nat * proof
           | Cut of formula * proof * proof

module Dict = struct
  type ('k, 'v) t = 'k -> 'v option

  let empty = []

  let insert k v d = (k, v) :: d

  let lookup k d = List.assoc_opt k d
end

let derives = function
  | True a -> Atom a
  | False a -> NegAtom a
  | ConjI (frm1, frm2, _, _) -> Conj (frm1, frm2)
  | DisjI (frm1, frm2, _) -> Disj (frm1, frm2)
  | ForallI (var, frm, _) -> Forall (var, frm)
  | ExistsI (var, frm, _, _) -> Exists (var, frm)
  | Cut _ -> failwith "The cut rule does not derive a formula"
