open Formula
open Deduction

let extract fn prf =
  let rec aux acc = function
    | True atm ->
       let func acc (frm, value) = if frm = Atom atm then value :: acc else acc in
       List.fold_left func Dict.empty acc

    | False atm ->
       let func acc (frm, value) = if frm = NegAtom atm then value :: acc else acc in
       List.fold_left func Dict.empty acc

    | ConjI (frm, frm', prf, prf') ->
       let func ins acc (frm'', value) =
         if frm'' = Conj (frm, frm') then
           acc |> Dict.insert ins value
         else
           acc
       in
       let res  = aux (List.fold_left (func frm ) acc acc) prf  in
       let res' = aux (List.fold_left (func frm') acc acc) prf' in
       let func acc (frm, num) =
         match List.assoc_opt frm acc with
         | Some num' when num = num' -> acc
         | Some _ -> List.remove_assoc frm acc
         | None -> acc |> Dict.insert frm num
       in
       List.fold_left func res res'

    | DisjI (frm, frm', prf) ->
       let func acc (frm'', value) =
         if frm'' = Disj (frm, frm') then
           acc |> Dict.insert frm value |> Dict.insert frm' value
         else
           acc
       in
       aux (List.fold_left func acc acc) prf

    | ExistsI (var, frm, num, prf) ->
       let frm' = subst_formula fn (Nat num) var frm in
       let func acc (frm'', value) =
         if frm'' = Exists (var, frm) then
           Dict.insert frm' value acc
         else
           acc
       in
       aux (List.fold_left func (Dict.insert frm' (Exists (var, frm), num) acc) acc) prf

    | ForallI _ -> failwith "Formula not simply existential"
    | Cut _ -> failwith "Formula not cut-free"
  in aux Dict.empty prf

let rec cut_elim fn = function
  | True a -> True a
  | False a -> False a
  | ConjI (frm1, frm2, prf1, prf2) -> ConjI (frm1, frm2, cut_elim fn prf1, cut_elim fn prf2)
  | DisjI (frm1, frm2, prf) -> DisjI (frm1, frm2, cut_elim fn prf)
  | ForallI (var, frm, prfs) -> ForallI (var, frm, fun n -> cut_elim fn (prfs n))
  | ExistsI (var, frm, num, prf) -> ExistsI (var, frm, num, cut_elim fn prf)
  | Cut (frm, prf, prf') ->
     let rec aux frm prf prf' =
       if not (frm = derives prf) then
         match prf with
         | True a -> True a
         | False a -> False a
         | ConjI (frm1, frm2, prf1, prf2) -> ConjI (frm1, frm2, aux frm prf1 prf', aux frm prf2 prf')
         | DisjI (frm1, frm2, prf'') -> DisjI (frm1, frm2, aux frm prf'' prf')
         | ForallI (var, frm', prfs) -> ForallI (var, frm', fun n -> aux frm (prfs n) prf')
         | ExistsI (var, frm', num, prf'') -> ExistsI (var, frm', num, aux frm prf'' prf')
         | Cut _ -> failwith "Derivation is cut-free by assumption"
       else if not (neg frm = derives prf') then
         match prf' with
         | True a -> True a
         | False a -> False a
         | ConjI (frm1, frm2, prf1, prf2) -> ConjI (frm1, frm2, aux frm prf prf1, aux frm prf prf2)
         | DisjI (frm1, frm2, prf'') -> DisjI (frm1, frm2, aux frm prf prf'')
         | ForallI (var, frm', prfs) -> ForallI (var, frm', fun n -> aux frm prf (prfs n))
         | ExistsI (var, frm', num, prf'') -> ExistsI (var, frm', num, aux frm prf prf'')
         | Cut _ -> failwith "Derivation is cut-free by assumption"
       else
         match (prf, prf') with
         | (ConjI (frm1, frm2, prf1, prf2), DisjI(_, _, prf)) -> aux frm2 prf2 (aux frm1 prf1 prf)
         | (DisjI (frm1, frm2, prf), ConjI (_, _, prf1, prf2)) -> aux frm2 (aux frm1 prf prf1) prf2
         | (ForallI (var, frm, prfs), ExistsI (_, _, num, prf)) ->
            aux
              (Forall (var, frm))
              (ForallI (var, frm, prfs))
              (aux (subst_formula fn (Nat num) var frm) (prfs num) prf)
         | (ExistsI (var, frm, num, prf), ForallI(_, _, prfs)) ->
            aux
              (Exists (var, frm))
              (aux (subst_formula fn (Nat num) var frm) prf (prfs num))
              (ForallI (var, neg frm, prfs))
         | _ -> failwith "Unreachable case"
     in
     aux frm (cut_elim fn prf) (cut_elim fn prf')
