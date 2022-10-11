%{
  open Ast

  let count = ref 0
%}

%token<string> VAR
%token<int> INT
%token IF THEN ELSE FOR TO DO END SKIP SEMI ATRIB LSB RSB LCB RCB BAR LP RP
%token TRUE FALSE EXISTS FORALL NOT AND OR EQ NE LT GT LE GE IMPL DOT
%token ADD SUB MUL EXP DIV SUM COMMA
%token EOF

%token NON

%left OR
%left AND
%left IMPL
%left ADD SUB
%left MUL
%left SEMI

%nonassoc NOT NON

%start<hoare> parse
%start<annot> annot_start
%start<aexp> aexp_start

%%

parse:
  EOF { (ABool true, Skip, ABool true, Cons 1) }
| s = stmt SEMI? EOF { (ABool true, s, ABool true, Cons 1) }
| LCB pre = annot RCB s = stmt SEMI? LCB pos = annot BAR time = aexp RCB EOF { (pre, s, pos, time) }

annot_start:
 a = annot EOF {a}

aexp_start:
 a = aexp EOF {a}

annot:
  LP a = annot RP { a }
| TRUE { ABool true }
| FALSE { ABool false }
| NOT b = annot { ANeg b }
| b1 = annot AND b2 = annot { AAnd (b1, b2) }
| b1 = annot OR b2 = annot { AOr (b1, b2) }
| b1 = annot IMPL b2 = annot { AImpl (b1, b2) }
| a1 = aexp EQ a2 = aexp { AEq (a1, a2) }
| a1 = aexp NE a2 = aexp { ANe (a1, a2) }
| a1 = aexp LT a2 = aexp { ALt (a1, a2) }
| a1 = aexp GT a2 = aexp { AGt (a1, a2) }
| a1 = aexp LE a2 = aexp { ALe (a1, a2) }
| a1 = aexp GE a2 = aexp { AGe (a1, a2) }
| EXISTS s = VAR DOT a = annot %prec NON { AExists(s, a) }
| FORALL s = VAR DOT a = annot %prec NON { AForall(s, a) }

stmt:
  SKIP { Skip }
| s1 = stmt SEMI s2 = stmt { Seq (s1, s2) }
| s = VAR LSB i = INT RSB { ArrDef (s,i) }
| s = VAR ATRIB a = aexp { Assign (s, a) }
| s = VAR LSB a1 = aexp RSB ATRIB a2 = aexp { ArrAssign (s, a1, a2) }
| IF b = bexp THEN s1 = stmt ELSE s2 = stmt END { If (b, s1, s2) }
| FOR i = VAR ATRIB a = INT TO b = aexp DO s = stmt END { incr count; For (!count, i, a, b, s) }

aexp:
  LP a = aexp RP { a }
| i = INT { Cons i }
| s = VAR { Var s }
| s = VAR LSB a = aexp RSB { Arr (s, a) }
| a1 = aexp ADD a2 = aexp { Sum (a1, a2) }
| a1 = aexp SUB a2 = aexp { Sub (a1, a2) }
| a1 = aexp MUL a2 = aexp { Mul (a1, a2) }
| a1 = aexp DIV a2 = aexp { Div (a1, a2) }
| a1 = aexp EXP a2 = aexp { Exp (a1, a2) }
| SUM LP s = VAR COMMA i1 = INT COMMA a1 = aexp COMMA a2 = aexp RP { Sigma (s,i1,a1,a2) }

bexp:
  LP b = bexp RP { b }
| TRUE { Bool true }
| FALSE { Bool false }
| NOT b = bexp { Neg b }
| b1 = bexp AND b2 = bexp { And (b1, b2) }
| b1 = bexp OR b2 = bexp { Or (b1, b2) }
| a1 = aexp EQ a2 = aexp { Eq (a1, a2) }
| a1 = aexp NE a2 = aexp { Ne (a1, a2) }
| a1 = aexp LT a2 = aexp { Lt (a1, a2) }
| a1 = aexp GT a2 = aexp { Gt (a1, a2) }
| a1 = aexp LE a2 = aexp { Le (a1, a2) }
| a1 = aexp GE a2 = aexp { Ge (a1, a2) }

%%
