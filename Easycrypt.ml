open Ast

let import = "require import AllCore.\n\n"

let pragma = "pragma Goals:printall.\n\n"

let simple_proof = "proof.\nsmt.\nqed.\n\n"

let rec aexp_to_easycrypt a =
  match a with
  | Cons c ->
      string_of_int c
  | Var i ->
      i
  | Sum (a1, a2) ->
      aexp_to_easycrypt a1 ^ "+" ^ aexp_to_easycrypt a2
  | Sub (a1, a2) ->
      aexp_to_easycrypt a1 ^ "-" ^ aexp_to_easycrypt a2
  | Mul (a1, a2) ->
      aexp_to_easycrypt a1 ^ "*" ^ aexp_to_easycrypt a2
  | Div (a1, a2) ->
      aexp_to_easycrypt a1 ^ "/" ^ aexp_to_easycrypt a2
  | Exp (a1, a2) ->
      aexp_to_easycrypt a1 ^ "^" ^ aexp_to_easycrypt a2
  | Arr (i, a') ->
      i ^ "[" ^ aexp_to_easycrypt a' ^ "]"
  | Sigma (_, _, _, _) ->
      (*FIXME*)
      ""

let rec bexp_to_easycrypt b =
  match b with
  | Bool b ->
      string_of_bool b
  | Eq (a1, a2) ->
      aexp_to_easycrypt a1 ^ "=" ^ aexp_to_easycrypt a2
  | Ne (a1, a2) ->
      aexp_to_easycrypt a1 ^ "!=" ^ aexp_to_easycrypt a2
  | Lt (a1, a2) ->
      aexp_to_easycrypt a1 ^ "<" ^ aexp_to_easycrypt a2
  | Gt (a1, a2) ->
      aexp_to_easycrypt a1 ^ ">" ^ aexp_to_easycrypt a2
  | Le (a1, a2) ->
      aexp_to_easycrypt a1 ^ "<=" ^ aexp_to_easycrypt a2
  | Ge (a1, a2) ->
      aexp_to_easycrypt a1 ^ ">=" ^ aexp_to_easycrypt a2
  | Neg b ->
      "!" ^ bexp_to_easycrypt b
  | And (b1, b2) ->
      bexp_to_easycrypt b1 ^ "/\\" ^ bexp_to_easycrypt b2
  | Or (b1, b2) ->
      bexp_to_easycrypt b1 ^ "\\/" ^ bexp_to_easycrypt b2

let rec annot_to_easycrypt a =
  match a with
  | ABool b ->
      string_of_bool b
  | AEq (a1, a2) ->
      aexp_to_easycrypt a1 ^ "=" ^ aexp_to_easycrypt a2
  | ANe (a1, a2) ->
      aexp_to_easycrypt a1 ^ "!=" ^ aexp_to_easycrypt a2
  | ALt (a1, a2) ->
      aexp_to_easycrypt a1 ^ "<" ^ aexp_to_easycrypt a2
  | AGt (a1, a2) ->
      aexp_to_easycrypt a1 ^ ">" ^ aexp_to_easycrypt a2
  | ALe (a1, a2) ->
      aexp_to_easycrypt a1 ^ "<=" ^ aexp_to_easycrypt a2
  | AGe (a1, a2) ->
      aexp_to_easycrypt a1 ^ ">=" ^ aexp_to_easycrypt a2
  | ANeg a ->
      "!" ^ annot_to_easycrypt a
  | AAnd (a1, a2) ->
      annot_to_easycrypt a1 ^ "/\\" ^ annot_to_easycrypt a2
  | AOr (a1, a2) ->
      annot_to_easycrypt a1 ^ "\\/" ^ annot_to_easycrypt a2
  | AImpl (a1, a2) ->
      annot_to_easycrypt a1 ^ "=>" ^ annot_to_easycrypt a2
  | AExists (i, a) ->
      "exists " ^ i ^ "," ^ annot_to_easycrypt a
  | AForall (i, a) ->
      "forall " ^ i ^ "," ^ annot_to_easycrypt a

let rec stmt_to_easycrypt s =
  match s with
  | Skip ->
      "();\n"
  | Assign (i, a) ->
      "var" ^ i ^ "=" ^ aexp_to_easycrypt a ^ ";\n"
  | ArrDef (_, _) ->
      "" (*FIXME*)
  | ArrAssign (i, a1, a2) ->
      i ^ "[" ^ aexp_to_easycrypt a1 ^ "] = " ^ aexp_to_easycrypt a2 ^ ";\n"
  | If (b, s1, s2) ->
      "if (" ^ bexp_to_easycrypt b ^ ") {\n" ^ stmt_to_easycrypt s1 ^ ";\n"
      ^ stmt_to_easycrypt s2 ^ "}"
  | While (_, b, s') ->
      "while (" ^ bexp_to_easycrypt b ^ ") {\n" ^ stmt_to_easycrypt s' ^ "}\n"
  | Seq (s1, s2) ->
      stmt_to_easycrypt s1 ^ stmt_to_easycrypt s2

let rc hoare_to_easycrypt (pre, c, pos, cost) =
  let out = import ^ pragma in
  let out = out ^ "module Main = {\n" ^ stmt_to_easycrypt c ^ "}." in
  let out =
    out ^ "lemma main:\n hoare[ M.main: " ^ annot_to_easycrypt pre ^ "==>"
    ^ annot_to_easycrypt pos ^ "].\n proof.\nqed."
  in
  out

let vcs_to_easycrypt (l : annot list) =
  let rec vcs_to_easycrypt_rec l =
    match l with
    | [] ->
        ""
    | h :: tl ->
        "lemma l" ^ ": " ^ annot_to_easycrypt h ^ ".\n" ^ simple_proof
        ^ vcs_to_easycrypt_rec tl
  in
  import ^ pragma ^ vcs_to_easycrypt_rec l
