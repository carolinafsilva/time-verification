open Ast
open Time
open Printer

let oracle_hashtbl = Hashtbl.create 43

let oracle () =
  try
    Printf.printf "Invariant: " ;
    let input = read_line () in
    let inv = Lexing.from_string input |> Parser.annot_start Lexer.token in
    Printf.printf "Variant: " ;
    let input = read_line () in
    let f = Lexing.from_string input |> Parser.aexp_start Lexer.token in
    Printf.printf "Number of Iterations: " ;
    let input = read_line () in
    let n = Lexing.from_string input |> Parser.aexp_start Lexer.token in
    Printf.printf "Amortized cost of while body: " ;
    let input = read_line () in
    let a = Lexing.from_string input |> Parser.aexp_start Lexer.token in
    Printf.printf "Potential Function: " ;
    let input = read_line () in
    let p = Lexing.from_string input |> Parser.aexp_start Lexer.token in
    (inv, f, n, a, p)
  with _ ->
    Printf.printf "Oracle Error\n" ;
    (ABool true, Cons 1, Cons 1, Cons 1, Cons 1)

let get_oracle id =
  if Hashtbl.mem oracle_hashtbl id then Hashtbl.find oracle_hashtbl id
  else
    let inv, f, n, a, p = oracle () in
    Hashtbl.add oracle_hashtbl id (inv, f, n, a, p) ;
    (inv, f, n, a, p)

let log msg =
  let oc = open_out_gen [Open_append; Open_creat] 0o644 "cost.log" in
  Printf.fprintf oc "%s\n" msg ;
  close_out oc

let rec asubst exp x arg =
  match exp with
  | Cons a ->
      Cons a
  | Var y ->
      if y = x then arg else Var y
  | Arr (x, i) ->
      Arr (x, i)
  | Sum (e1, e2) ->
      Sum (asubst e1 x arg, asubst e2 x arg)
  | Sub (e1, e2) ->
      Sub (asubst e1 x arg, asubst e2 x arg)
  | Mul (e1, e2) ->
      Mul (asubst e1 x arg, asubst e2 x arg)
  | Div (e1, e2) ->
      Div (asubst e1 x arg, asubst e2 x arg)
  | Exp (e1, e2) ->
      Exp (asubst e1 x arg, asubst e2 x arg)
  | Sigma (ident, lower, upper, body) ->
      Sigma (ident, lower, upper, asubst body x arg)

let rec subst phi x e =
  match phi with
  | ABool b ->
      ABool b
  | AEq (e1, e2) ->
      AEq (asubst e1 x e, asubst e2 x e)
  | ANe (e1, e2) ->
      ANe (asubst e1 x e, asubst e2 x e)
  | ALt (e1, e2) ->
      ALt (asubst e1 x e, asubst e2 x e)
  | AGt (e1, e2) ->
      AGt (asubst e1 x e, asubst e2 x e)
  | ALe (e1, e2) ->
      ALe (asubst e1 x e, asubst e2 x e)
  | AGe (e1, e2) ->
      AGe (asubst e1 x e, asubst e2 x e)
  | ANeg phi1 ->
      ANeg (subst phi1 x e)
  | AAnd (phi1, phi2) ->
      AAnd (subst phi1 x e, subst phi2 x e)
  | AOr (phi1, phi2) ->
      AOr (subst phi1 x e, subst phi2 x e)
  | AImpl (phi1, phi2) ->
      AImpl (subst phi1 x e, subst phi2 x e)
  | AExists (y, phi') ->
      if x = y then phi else AExists (y, subst phi' x e)
  | AForall (y, phi') ->
      if x = y then phi else AForall (y, subst phi' x e)

let rec asubst_arr exp x i arg =
  match exp with
  | Cons a ->
      Cons a
  | Var x ->
      Var x
  | Arr (y, j) ->
      if y = x && j = i then arg else Arr (y, j)
  | Sum (e1, e2) ->
      Sum (asubst_arr e1 x i arg, asubst_arr e2 x i arg)
  | Sub (e1, e2) ->
      Sub (asubst_arr e1 x i arg, asubst_arr e2 x i arg)
  | Mul (e1, e2) ->
      Mul (asubst_arr e1 x i arg, asubst_arr e2 x i arg)
  | Div (e1, e2) ->
      Div (asubst_arr e1 x i arg, asubst_arr e2 x i arg)
  | Exp (e1, e2) ->
      Exp (asubst_arr e1 x i arg, asubst_arr e2 x i arg)
  | Sigma (ident, lower, upper, body) ->
      Sigma (ident, lower, upper, asubst_arr body x i arg)

let rec subst_arr phi x i e =
  match phi with
  | ABool b ->
      ABool b
  | AEq (e1, e2) ->
      AEq (asubst_arr e1 x i e, asubst_arr e2 x i e)
  | ANe (e1, e2) ->
      ANe (asubst_arr e1 x i e, asubst_arr e2 x i e)
  | ALt (e1, e2) ->
      ALt (asubst_arr e1 x i e, asubst_arr e2 x i e)
  | AGt (e1, e2) ->
      AGt (asubst_arr e1 x i e, asubst_arr e2 x i e)
  | ALe (e1, e2) ->
      ALe (asubst_arr e1 x i e, asubst_arr e2 x i e)
  | AGe (e1, e2) ->
      AGe (asubst_arr e1 x i e, asubst_arr e2 x i e)
  | ANeg phi1 ->
      ANeg (subst_arr phi1 x i e)
  | AAnd (phi1, phi2) ->
      AAnd (subst_arr phi1 x i e, subst_arr phi2 x i e)
  | AOr (phi1, phi2) ->
      AOr (subst_arr phi1 x i e, subst_arr phi2 x i e)
  | AImpl (phi1, phi2) ->
      AImpl (subst_arr phi1 x i e, subst_arr phi2 x i e)
  | AExists (y, phi') ->
      if x = y then phi else AExists (y, subst_arr phi' x i e)
  | AForall (y, phi') ->
      if x = y then phi else AForall (y, subst_arr phi' x i e)

let rec annot_of_bexp bexp =
  match bexp with
  | Bool b ->
      ABool b
  | Eq (e1, e2) ->
      AEq (e1, e2)
  | Ne (e1, e2) ->
      ANe (e1, e2)
  | Lt (e1, e2) ->
      ALt (e1, e2)
  | Gt (e1, e2) ->
      AGt (e1, e2)
  | Le (e1, e2) ->
      ALe (e1, e2)
  | Ge (e1, e2) ->
      AGe (e1, e2)
  | Neg e ->
      ANeg (annot_of_bexp e)
  | And (e1, e2) ->
      AAnd (annot_of_bexp e1, annot_of_bexp e2)
  | Or (e1, e2) ->
      AOr (annot_of_bexp e1, annot_of_bexp e2)

let rec wpc s phi verbose =
  match s with
  | Skip ->
      (phi, Var "Skip")
  | Assign (x, a) ->
      let t' = time_aexp a in
      (subst phi x a, Sum (Var "Assign", t'))
  | ArrDef (_, _) ->
      (phi, Var "ArrDef")
  | ArrAssign (x, a1, a2) ->
      let t' = Sum (time_aexp a1, time_aexp a2) in
      (subst_arr phi x a1 a2, Sum (Var "Assign", t'))
  | Seq (s1, s2) ->
      let phi', t2 = wpc s2 phi verbose in
      let phi, t1 = wpc s1 phi' verbose in
      (phi, Sum (t1, t2))
  | If (b, s1, s2) ->
      let wp1, t1 = wpc s1 phi verbose in
      let wp2, t2 = wpc s2 phi verbose in
      let v_b = annot_of_bexp b in
      let tb = time_bexp b in
      (AAnd (AImpl (v_b, wp1), AImpl (ANeg v_b, wp2)), Sum (Sum (t1, t2), tb))
  | While (id, b, _) ->
      let inv, f, n, a, p = get_oracle id in
      let time_body = Mul (n, a) in
      ( AAnd (AAnd (inv, AGe (f, Cons 0)), AEq (p, Cons 0))
      , Sum (Mul (Sum (n, Cons 1), time_bexp b), time_body) )

let wp s phi : annot =
  let phi, _ = wpc s phi false in
  phi

let lambda_app (f : lambda) x =
  let ident, body = f in
  asubst body ident x

let rec vc s phi : annot list =
  match s with
  | Skip | Assign (_, _) | ArrDef (_, _) | ArrAssign (_, _, _) ->
      []
  | Seq (s1, s2) ->
      vc s1 (wp s2 phi) @ vc s2 phi
  | If (_, s1, s2) ->
      vc s1 phi @ vc s2 phi
  | While (id, b, s') ->
      let inv, f, n, a, p = get_oracle id in
      let b = annot_of_bexp b in
      let wp, t = wpc s' (AAnd(inv, AAnd (AGt (f, Var "k"), AEq (p, Var "pk")))) false in
      AImpl (AAnd (inv, b), ALe (f, n))
      :: AImpl (inv, AGe(p, Cons 0))
      :: AForall ( "k", AImpl ( AAnd (inv, AAnd (b, AEq (f, Var "k"))), wp) )
      :: AGe (Sub (Sum(a, p), Var "pk"), t)
      :: AImpl (AAnd (inv, ANeg b), phi)
      :: vc s' inv

let vcg pre s t pos =
  let wp, ts = wpc s pos true in
  (* let ts = eval_time_aexp ts in
  let t = eval_time_aexp t in *)
  ALe (ts, t) :: AImpl (pre, wp) :: vc s pos
