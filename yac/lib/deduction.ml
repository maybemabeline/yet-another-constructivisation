open Formula

type context = Context.t

type proof = Lem of atom * context
           | ConjI of (formula * proof) list
           | DisjI of (formula list) * proof
           | ForallI of string * formula * proof
           | ExistsI of term * formula * proof
           | Cut of formula * proof * proof

(* Check if list consists of a unique element and returns it if it does.*)
(* Returns None on empty list *)
let unique_el =
  let rec aux first = function
    | [] -> first
    | x :: xs ->
       match first with
       | None -> aux (Some x) xs
       | Some y -> if x = y then aux first xs else None
  in
  aux None

let some_if cond value = if cond then Some value else None

let rec check g = function
  | Lem (atm, ctx) ->
     (* Check if the atom is contained in the context *)
     some_if (Context.mem (Atom atm) ctx) (Context.add (NegAtom atm) ctx)
  | ConjI lst ->
     (* Recursively check all the proofs of the conjuncts and *)
     (* return list of the conjuncts and list of contexts in which they are derived *)
     let rec aux acc1 acc2 = function
       | [] -> Some (acc1, acc2)
       | (frm, prf) :: rest ->
          Option.bind (check g prf) (fun ctx ->
              (* Check if conjunct is actually contained in the derived context *)
              if Context.mem frm ctx then
                aux (frm :: acc1) ((Context.remove frm ctx) :: acc2) rest
              else
                None
            )
     in
     Option.bind (aux [] [] lst) (fun (frms, ctxs) ->
         (* Check if all the derived contexts without the conjucts are the same *)
         Option.bind (unique_el ctxs) (fun ctx ->
             Some (Context.add (Conj frms) ctx)
           )
       )
  | DisjI (frms, prf) ->
     (* Recursively check the proof *)
     Option.bind (check g prf) (fun ctx ->
         (* Check if all the disjuncts are contained in the derived context. *)
         (* If so, return the context without all the conjuncts *)
         let rec aux acc = function
           | [] -> Some acc
           | frm :: rest ->
              if Context.mem frm acc then
                aux (Context.remove frm acc) rest
              else
                None
         in
         Option.bind (aux ctx frms) (fun ctx' ->
             Some (Context.add (Disj frms) ctx')
           )
       )
  | ForallI (str, frm, prf) ->
     Option.bind (check (str :: g) prf) (fun ctx ->
         some_if (Context.mem frm ctx) (Context.add (Forall (str, frm)) (Context.remove frm ctx))
       )
  | ExistsI (trm, frm, prf) ->
     Option.bind (check g prf) (fun ctx ->
         let func frm' = function
           | Some x -> Some x
           | None ->
              match frm' with
              | Exists (str, frm'') when frm = frm'' -> Some str
              | _ -> None
         in
         Option.bind (Context.fold func ctx None) (fun str ->
             let check = match trm with
               | Var str -> List.mem str g
               | Nat _ -> true
             in
             let frm' = subst_formula trm str frm in
             some_if ((Context.mem frm' ctx) && check) (Context.remove frm' ctx)
           )
       )
  | Cut (frm, prf, prf') ->
     Option.bind (check g prf) (fun ctx ->
         Option.bind (check g prf') (fun ctx' ->
             some_if ((Context.mem frm ctx) && (Context.mem (neg frm) ctx') && (Context.remove frm ctx' = Context.remove (neg frm) ctx')) @@
               Context.remove frm ctx
           )
       )
