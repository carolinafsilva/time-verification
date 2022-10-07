type ident = string

type count = int

type aexp =
  | Cons of int
  | Var of ident
  | Sum of aexp * aexp
  | Sub of aexp * aexp
  | Mul of aexp * aexp
  | Div of aexp * aexp
  | Exp of aexp * aexp
  | Arr of ident * aexp
  | Sigma of ident * int * aexp * aexp

type bexp =
  | Bool of bool
  | Eq of aexp * aexp
  | Ne of aexp * aexp
  | Lt of aexp * aexp
  | Gt of aexp * aexp
  | Le of aexp * aexp
  | Ge of aexp * aexp
  | Neg of bexp
  | And of bexp * bexp
  | Or of bexp * bexp

type stmt =
  | Skip
  | Assign of ident * aexp
  | ArrDef of ident * int
  | ArrAssign of ident * aexp * aexp
  | If of bexp * stmt * stmt
  | While of count * bexp * stmt
  | Seq of stmt * stmt

type annot =
  | ABool of bool
  | AEq of aexp * aexp
  | ANe of aexp * aexp
  | ALt of aexp * aexp
  | AGt of aexp * aexp
  | ALe of aexp * aexp
  | AGe of aexp * aexp
  | ANeg of annot
  | AAnd of annot * annot
  | AOr of annot * annot
  | AImpl of annot * annot
  | AExists of ident * annot
  | AForall of ident * annot

type lambda = ident * aexp

(* invariant * variant * number of iterations *)
type oracle = annot * aexp * aexp

(* preconditon, program, postcondition, resource bound *)
type hoare = annot * stmt * annot * aexp
