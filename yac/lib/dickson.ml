open Formula
open Deduction

let rec go fn n =
  ExistsI ("x",
           Forall ("y", Atom (Leq (Func (Var "x"), Func (Var "y")))),
           n,
           ForallI ("y",
                    Atom (Leq (Nat (fn n), Func (Var "y"))),
                    fun m -> if fn n <= fn m
                             then True (Leq (Nat (fn n), Nat (fn m)))
                             else go fn m
             )
    )

let minimum fn = go fn Zero

let dickson_from_min fn =
  ForallI ("x",
           Exists ("y", Atom (Le (Func (Var "y"), Func (Var "x")))),
           fun n -> ExistsI ("y",
                             Atom (Le (Func (Var "y"), (Nat (fn n)))),
                             Succ n,
                             ExistsI ("i",
                                      Exists ("j", Conj (Atom (Le (Var "i", Var "j")), Atom (Leq (Func (Var "i"), Func (Var "j"))))),
                                      n,
                                      ExistsI ("j",
                                               Conj (Atom (Le (Nat n, Var "j")), Atom (Leq (Nat (fn n), Func (Var "j")))),
                                               Succ n,
                                               ConjI (Atom (Le (Nat n, Nat (Succ n))),
                                                      Atom (Leq (Nat (fn n), Nat (fn (Succ n)))),
                                                      True (Le (Nat n, Nat (Succ n))),
                                                      (if fn n <= fn (Succ n)
                                                       then True (Leq (Nat (fn n), Nat (fn (Succ n))))
                                                       else True (Le (Nat (fn (Succ n)), Nat (fn n))))
                                                 )
                                        )
                               )
                      )
    )

let dickson fn =
  Cut ((Exists ("x", Forall ("y", Atom (Leq (Func (Var "x"), Func (Var "y")))))),
       (minimum fn),
       (dickson_from_min fn)
    )
