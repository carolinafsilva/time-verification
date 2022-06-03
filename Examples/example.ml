open Ast
open VC

let invariant = AEq (Var "X", Sum (Var "R", Mul (Var "Y", Var "Q")))

let cw =
  Seq (Assign ("R", Sub (Var "R", Var "Y")), Assign ("Q", Sum (Var "Q", Cons 1)))

let precondition = AAnd (AEq (Var "R", Var "X"), AEq (Var "Q", Cons 0))

let poscondition =
  AAnd
    ( AEq (Var "X", Sum (Var "R", Mul (Var "Y", Var "Q"))),
      AAnd (ALe (Var "R", Var "Y"), ANeg (AEq (Var "R", Var "Y"))) )

let time = Var "X"

let prog = While (Le (Var "Y", Var "R"), cw)

let result = vcg precondition prog (Cons 1) poscondition
