open Ast
open Time

type loc = Id of string | ArrId of string * int

type value = int

type state = (loc, value) Hashtbl.t

let (env:state) = Hashtbl.create 997

let int_exp x y = float_of_int x ** float_of_int y |> int_of_float

let rec a' env exp =
  let a' = a' env in
  match exp with
  | Cons i ->
      i
  | Var x ->
      Hashtbl.find env (Id x)
  | Arr (x, i) ->
      Hashtbl.find env (ArrId (x, a' i))
  | Sum (a1, a2) ->
      a' a1 + a' a2
  | Sub (a1, a2) ->
      a' a1 - a' a2
  | Mul (a1, a2) ->
      a' a1 * a' a2
  | Div (a1, a2) ->
      a' a1 / a' a2
  | Exp (a1, a2) ->
      int_exp (a' a1) (a' a2)
  | Sigma (ident, lower, upper, body) ->
      let rec sigma ident i upper body =
        if i > upper then 0
        else (
          Hashtbl.replace env ident i ;
          a' body + sigma ident (i + 1) upper body )
      in
      sigma (Id ident) lower (a' upper) body

let rec b' env exp =
  let a' = a' env in
  let b' = b' env in
  match exp with
  | Bool b ->
      b
  | Eq (a1, a2) ->
      a' a1 = a' a2
  | Ne (a1, a2) ->
      a' a1 != a' a2
  | Lt (a1, a2) ->
      a' a1 < a' a2
  | Gt (a1, a2) ->
      a' a1 > a' a2
  | Le (a1, a2) ->
      a' a1 <= a' a2
  | Ge (a1, a2) ->
      a' a1 >= a' a2
  | Neg b ->
      not (b' b)
  | And (b1, b2) ->
      b' b1 && b' b2
  | Or (b1, b2) ->
      b' b1 || b' b2

let rec interpret env s =
  match s with
  | Skip ->
      (env, check_time "Skip")
  | Assign (x, a) ->
      let v = a' env a in
      let t = eval_time_aexp a in
      Hashtbl.replace env (Id x) v ;
      (env, t + check_time "Assign")
      (* TODO: Replace +1*)
  | ArrDef (_, _) ->
      (env, 1) (*FIXME*)
  | ArrAssign (x, a1, a2) ->
      let v1 = a' env a1 in
      let v2 = a' env a2 in
      let t1 = eval_time_aexp a1 in
      let t2 = eval_time_aexp a2 in
      Hashtbl.replace env (ArrId (x, v1)) v2 ;
      (env, t1 + t2 + 1)
      (* TODO: Replace +1*)
  | If (b, s1, s2) ->
      let t_b = eval_time_bexp b in
      let v = b' env b in
      let env, t = if v then interpret env s1 else interpret env s2 in
      (env, t_b + t)
  | For (c, i, a, b, s) ->
      let x =(Lt (Cons a, b)) in
      let t_b = x |> time_bexp |> eval_time_aexp in
      Hashtbl.replace env (Id i) a;
      let v = b' env x in
      if v then
        let env, t' = interpret env s in
        let env, t = interpret env (For (c, i, a+1, b, s)) in
        (env, t_b + t' + t)
      else (env, t_b)
  | Seq (s1, s2) ->
      let env, t1 = interpret env s1 in
      let env, t2 = interpret env s2 in
      (env, t1 + t2)
