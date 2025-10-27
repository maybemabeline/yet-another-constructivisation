open Formula

type context = Context.t

type proof = Lem of atom * context
           | Conj of (formula * proof) list
           | Disj of proof
           | Forall of (int -> formula * proof)
           | Exists of int * proof


let unique_el =
  let rec aux first ok = function
    | [] -> if ok then first else None
    | x :: xs ->
       match first with
       | None -> aux (Some x) true xs
       | Some y -> aux first (ok && x = y) xs
  in
  aux None true

let rec check : proof -> context option = function
  | Conj l ->
     let rec aux acc1 acc2 = function
       | [] -> Some (acc1, acc2)
       | (frm, prf) :: rest ->
          Option.bind (check prf) (fun ctx ->
              aux (frm :: acc1) ((Context.remove frm ctx) :: acc2) rest
            )
     in
     Option.bind (aux [] [] l) (fun (frms, ctxs) ->
         Option.bind (unique_el ctxs) (fun ctx ->
             Some (Context.add (Conj frms) ctx)
           )
       )
  | Forall f ->
