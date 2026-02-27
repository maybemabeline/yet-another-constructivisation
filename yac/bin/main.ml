open Yac.Formula
open Yac.Print
open Yac.Dickson
open Yac.Properties


(* let test = ExistsI (of_int 2, "m", Exists ("n", Atom (Leq (Var "m", Var "n"))), *)
(*                     ExistsI (of_int 3, "n", Atom (Leq (Nat (of_int 2), Var "n")), *)
(*                              True (Leq (Nat (of_int 2), Nat (of_int 3)), []))) *)

(* let test2 = ExistsI ("i", Exists ("j", Exists ("k", Conj (Atom (Leq (Var "i", Var "j")), Atom (Leq (Var "j", Var "k"))))), of_int 2, *)
(*                      ExistsI ("j", Exists ("k", Conj (Atom (Leq (Nat (of_int 2), Var "j")), Atom (Leq (Var "j", Var "k")))), of_int 3, *)
(*                               ExistsI ("k", Conj (Atom (Leq (Nat (of_int 2), Nat (of_int 3))), Atom (Leq (Nat (of_int 3), Var "k"))), of_int 4, *)
(*                                        ConjI ( *)
(*                                            Atom (Leq (Nat (of_int 2), Nat (of_int 3))), *)
(*                                            Atom (Leq (Nat (of_int 3), Nat (of_int 4))), *)
(*                                            True (Leq (Nat (of_int 2), Nat (of_int 3))), *)
(*                                            True (Leq (Nat (of_int 3), Nat (of_int 4))) *)
(*                                          ) *)
(*                                 ) *)
(*                        ) *)
(*               ) *)

let fn = function
  | Zero -> of_int 5
  | Succ Zero -> of_int 4
  | Succ (Succ Zero) -> of_int 3
  | Succ (Succ (Succ Zero)) -> of_int 2
  | Succ _ -> of_int 3

let () = dickson fn
         |> cut_elim fn
         |> extract fn
         |> List.iter (fun (src, num) ->
                print_string "Formula ";
                print_formula src;
                print_string " is witnessed by ";
                print_int (to_int num);
                print_newline()
              )
