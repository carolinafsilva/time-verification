open Ast

let rec string_of_aexp a =
  match a with
  | Cons i ->
      string_of_int i
  | Var x ->
      x
  | Arr (x, i) ->
      x ^ "[" ^ string_of_aexp i ^ "]"
  | Sum (e1, e2) ->
      "(" ^ string_of_aexp e1 ^ " + " ^ string_of_aexp e2 ^ ")"
  | Sub (e1, e2) ->
      "(" ^ string_of_aexp e1 ^ " - " ^ string_of_aexp e2 ^ ")"
  | Mul (e1, e2) ->
      "(" ^ string_of_aexp e1 ^ " × " ^ string_of_aexp e2 ^ ")"
  | Div (e1, e2) ->
      "(" ^ string_of_aexp e1 ^ " / " ^ string_of_aexp e2 ^ ")"
  | Exp (e1, e2) ->
      "(" ^ string_of_aexp e1 ^ " ^ " ^ string_of_aexp e2 ^ ")"
  | Sigma (ident, i, upper, body) ->
      "(" ^ ident ^ "=" ^ string_of_int i ^ " ∑ " ^ string_of_aexp upper ^ "("
      ^ string_of_aexp body ^ ")" ^ ")"

let rec print_aexp a =
  match a with
  | Cons i ->
      Printf.printf "%d" i
  | Var x ->
      Printf.printf "%s" x
  | Arr (x, i) ->
      Printf.printf "%s[" x ; print_aexp i ; Printf.printf "]"
  | Sum (e1, e2) ->
      Printf.printf "(" ;
      print_aexp e1 ;
      Printf.printf " + " ;
      print_aexp e2 ;
      Printf.printf ")"
  | Sub (e1, e2) ->
      Printf.printf "(" ;
      print_aexp e1 ;
      Printf.printf " - " ;
      print_aexp e2 ;
      Printf.printf ")"
  | Mul (e1, e2) ->
      Printf.printf "(" ;
      print_aexp e1 ;
      Printf.printf " × " ;
      print_aexp e2 ;
      Printf.printf ")"
  | Div (e1, e2) ->
      Printf.printf "(" ;
      print_aexp e1 ;
      Printf.printf " / " ;
      print_aexp e2 ;
      Printf.printf ")"
  | Exp (e1, e2) ->
      Printf.printf "(" ;
      print_aexp e1 ;
      Printf.printf " ^ " ;
      print_aexp e2 ;
      Printf.printf ")"
  | Sigma (_, _, _, _) ->
      Printf.printf "%s" (string_of_aexp a)

let rec string_of_annot a =
  match a with
  | ABool b ->
      if b then "True" else "False"
  | AEq (e1, e2) ->
      string_of_aexp e1 ^ " == " ^ string_of_aexp e2
  | ANe (e1, e2) ->
      string_of_aexp e1 ^ " != " ^ string_of_aexp e2
  | ALt (e1, e2) ->
      string_of_aexp e1 ^ " < " ^ string_of_aexp e2
  | AGt (e1, e2) ->
      string_of_aexp e1 ^ " > " ^ string_of_aexp e2
  | ALe (e1, e2) ->
      string_of_aexp e1 ^ " ≤ " ^ string_of_aexp e2
  | AGe (e1, e2) ->
      string_of_aexp e1 ^ " ≥ " ^ string_of_aexp e2
  | ANeg phi ->
      "¬ " ^ string_of_annot phi
  | AAnd (phi1, phi2) ->
      "(" ^ string_of_annot phi1 ^ " ∧ " ^ string_of_annot phi2 ^ ")"
  | AOr (phi1, phi2) ->
      "(" ^ string_of_annot phi1 ^ " ∨ " ^ string_of_annot phi2 ^ ")"
  | AImpl (phi1, phi2) ->
      "(" ^ string_of_annot phi1 ^ " → " ^ string_of_annot phi2 ^ ")"
  | AExists (x, phi) ->
      "∃%s." ^ x ^ string_of_annot phi
  | AForall (x, phi) ->
      "∀%s." ^ x ^ string_of_annot phi

let rec print_annot a =
  match a with
  | ABool b ->
      if b then Printf.printf "True" else Printf.printf "False"
  | AEq (e1, e2) ->
      print_aexp e1 ; Printf.printf " == " ; print_aexp e2
  | ANe (e1, e2) ->
      print_aexp e1 ; Printf.printf " != " ; print_aexp e2
  | ALt (e1, e2) ->
      print_aexp e1 ; Printf.printf " < " ; print_aexp e2
  | AGt (e1, e2) ->
      print_aexp e1 ; Printf.printf " > " ; print_aexp e2
  | ALe (e1, e2) ->
      print_aexp e1 ; Printf.printf " ≤ " ; print_aexp e2
  | AGe (e1, e2) ->
      print_aexp e1 ; Printf.printf " ≥ " ; print_aexp e2
  | ANeg phi ->
      Printf.printf "¬(" ; print_annot phi ; Printf.printf ")"
  | AAnd (phi1, phi2) ->
      Printf.printf "(" ;
      print_annot phi1 ;
      Printf.printf " ∧ " ;
      print_annot phi2 ;
      Printf.printf ")"
  | AOr (phi1, phi2) ->
      Printf.printf "(" ;
      print_annot phi1 ;
      Printf.printf " ∨ " ;
      print_annot phi2 ;
      Printf.printf ")"
  | AImpl (phi1, phi2) ->
      Printf.printf "(" ;
      print_annot phi1 ;
      Printf.printf " → " ;
      print_annot phi2 ;
      Printf.printf ")"
  | AExists (x, phi) ->
      Printf.printf "∃%s." x ; print_annot phi
  | AForall (x, phi) ->
      Printf.printf "∀%s." x ; print_annot phi

let print vcs =
  let f x = Printf.printf "\n" ; print_annot x ; Printf.printf "\n" in
  List.iter f vcs

let print_loc (l : Semantics.loc) =
    match l with
    | Semantics.Id s -> Printf.printf "%s" s
    | Semantics.ArrId (s,i) -> Printf.printf "%s[%d]" s i

let print_state (s : Semantics.state) =
    Printf.printf "{\n";
    Hashtbl.iter (fun i v -> Printf.printf "    ";print_loc i; Printf.printf " = %d\n" v) s;
    Printf.printf "}\n"
