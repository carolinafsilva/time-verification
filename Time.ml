open Ast

type time = int

let time_dict =
  [ ("Assign", 1)
  ; ("ArrDef", 1)
  ; ("Skip", 1)
  ; ("Cons", 1)
  ; ("Var", 1)
  ; ("Arr", 1)
  ; ("Sum", 1)
  ; ("Sub", 1)
  ; ("Mul", 1)
  ; ("Div", 1)
  ; ("Exp", 1)
  ; ("Bool", 1)
  ; ("Eq", 1)
  ; ("Ne", 1)
  ; ("Lt", 1)
  ; ("Gt", 1)
  ; ("Le", 1)
  ; ("Ge", 1)
  ; ("Neg", 1)
  ; ("And", 1)
  ; ("Or", 1) ]

let def_time op time = (op, time) :: time_dict

let check_time =
  let tbl = Hashtbl.create 32 in
  List.iter (fun (s, i) -> Hashtbl.add tbl s i) time_dict ;
  fun s -> try Hashtbl.find tbl s with Not_found -> 0

let rec time_aexp (e : aexp) =
  match e with
  | Cons _ ->
      Var "Cons"
  | Var v when check_time v != 0 ->
      Var v
  | Var _ ->
      Var "Var"
  | Arr (_, _) ->
      Var "Arr"
  | Sum (e1, e2) ->
      Sum (Var "Sum", Sum (time_aexp e1, time_aexp e2))
  | Sub (e1, e2) ->
      Sum (Var "Sub", Sum (time_aexp e1, time_aexp e2))
  | Mul (e1, e2) ->
      Sum (Var "Mul", Sum (time_aexp e1, time_aexp e2))
  | Div (e1, e2) ->
      Sum (Var "Div", Sum (time_aexp e1, time_aexp e2))
  | Exp (e1, e2) ->
      Sum (Var "Exp", Sum (time_aexp e1, time_aexp e2))
  | Sigma (ident, lower, upper, body) ->
      Sigma (ident, lower, upper, time_aexp body)

let get_op (a : aexp) =
  match a with
  | Cons _ ->
      "Cons"
  | Var _ ->
      "Var"
  | Arr _ ->
      "Arr"
  | Sum _ ->
      "Sum"
  | Sub _ ->
      "Sub"
  | Mul _ ->
      "Mul"
  | Div _ ->
      "Div"
  | Exp _ ->
      "Exp"
  | Sigma _ ->
      "Sigma"

let rec eval_time_aexp (e : aexp) =
  match e with
  | Cons _ ->
      Cons (check_time "Cons")
  | Var v ->
      let i = check_time v in
      if i = 0 then e else Cons i
  | Arr (_, e) -> (
      let e = eval_time_aexp e in
      let arr = check_time "Arr" in
      match e with Cons c -> Cons (c + arr) | _ -> Sum (e, Cons arr) )
  | Sum (e1, e2) | Sub (e1, e2) | Mul (e1, e2) | Div (e1, e2) | Exp (e1, e2)
    -> (
      let op = get_op e in
      let op = check_time op in
      let e1 = eval_time_aexp e1 in
      let e2 = eval_time_aexp e2 in
      match (e1, e2) with
      | Cons c1, Cons c2 ->
          Cons (c1 + c2 + op)
      | Cons c1, _ ->
          Sum (Cons (c1 + op), e2)
      | _, Cons c2 ->
          Sum (Cons (c2 + op), e1)
      | _ ->
          Sum (Cons op, Sum (e1, e2)) )
  | Sigma (_, lower, upper, body) ->
      e
(* let upper = eval_time_aexp upper in
   let body = eval_time_aexp body in
   match upper with
   | Cons c -> (
       let range = c - lower in
       match body with
       | Cons c' ->
           Cons (range * c')
       | _ ->
           Mul (Cons range, body) )
   | _ ->
       Mul (Sub (upper, Cons lower), body) ) *)

let rec time_bexp b =
  match b with
  | Bool _ ->
      Var "Bool"
  | Eq (e1, e2) ->
      Sum (Var "Eq", Sum (time_aexp e1, time_aexp e2))
  | Ne (e1, e2) ->
      Sum (Var "Ne", Sum (time_aexp e1, time_aexp e2))
  | Lt (e1, e2) ->
      Sum (Var "Lt", Sum (time_aexp e1, time_aexp e2))
  | Gt (e1, e2) ->
      Sum (Var "Gt", Sum (time_aexp e1, time_aexp e2))
  | Le (e1, e2) ->
      Sum (Var "Le", Sum (time_aexp e1, time_aexp e2))
  | Ge (e1, e2) ->
      Sum (Var "Ge", Sum (time_aexp e1, time_aexp e2))
  | Neg b1 ->
      Sum (Var "Neg", time_bexp b1)
  | And (b1, b2) ->
      Sum (Var "And", Sum (time_bexp b1, time_bexp b2))
  | Or (b1, b2) ->
      Sum (Var "Or", Sum (time_bexp b1, time_bexp b2))

let get_bop b =
  match b with
  | Bool _ ->
      "Bool"
  | Neg _ ->
      "Neg"
  | Eq _ ->
      "Eq"
  | Ne _ ->
      "Ne"
  | Le _ ->
      "Le"
  | Ge _ ->
      "Ge"
  | Lt _ ->
      "Lt"
  | Gt _ ->
      "Gt"
  | And _ ->
      "And"
  | Or _ ->
      "Or"

let rec eval_time_bexp b =
  match b with
  | Bool _ ->
      Cons (check_time "Bool")
  | Neg b -> (
      let neg = check_time "Neg" in
      let b = eval_time_bexp b in
      match b with Cons c -> Cons (c + neg) | _ -> Sum (Cons neg, b) )
  | Eq (e1, e2)
  | Ne (e1, e2)
  | Lt (e1, e2)
  | Gt (e1, e2)
  | Le (e1, e2)
  | Ge (e1, e2) -> (
      let op = get_bop b in
      let op = check_time op in
      let e1 = eval_time_aexp e1 in
      let e2 = eval_time_aexp e2 in
      match (e1, e2) with
      | Cons c1, Cons c2 ->
          Cons (c1 + c2 + op)
      | Cons c1, _ ->
          Sum (Cons (c1 + op), e2)
      | _, Cons c2 ->
          Sum (Cons (c2 + op), e1)
      | _ ->
          Sum (Cons op, Sum (e1, e2)) )
  | And (b1, b2) | Or (b1, b2) -> (
      let op = get_bop b in
      let op = check_time op in
      let e1 = eval_time_bexp b1 in
      let e2 = eval_time_bexp b2 in
      match (e1, e2) with
      | Cons c1, Cons c2 ->
          Cons (c1 + c2 + op)
      | Cons c1, _ ->
          Sum (Cons (c1 + op), e2)
      | _, Cons c2 ->
          Sum (Cons (c2 + op), e1)
      | _ ->
          Sum (Cons op, Sum (e1, e2)) )
