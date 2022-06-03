{
  open Parser

  let check_keyword =
    let tbl = Hashtbl.create 32 in
    List.iter (fun (s, token) -> Hashtbl.add tbl s token) [
      "true", TRUE;
      "false", FALSE;
      "exists", EXISTS;
      "forall", FORALL;
      "not", NOT;
      "and", AND;
      "or", OR;
      "if", IF;
      "then", THEN;
      "else", ELSE;
      "while", WHILE;
      "do", DO;
      "end", END;
      "fun", FUN;
      "skip", SKIP;
      "sum", SUM
    ];
    fun s -> try Hashtbl.find tbl s with Not_found -> VAR s
}

let space = [' ' '\t']

let newline = '\n' | '\r' | "\r\n"

let positive = ['0'-'9']+
let number = ['0'-'9']+
let character = ['a'-'z' 'A'-'Z' '_']

let word = character (character | number | '\'')*

rule token = parse
  | space
  | newline         { token lexbuf }
  | "(*"            { comment lexbuf; token lexbuf }
  | "="             { ATRIB }
  | ","             { COMMA }
  | ";"             { SEMI }
  | "{"             { LCB }
  | "}"             { RCB }
  | "("             { LP }
  | ")"             { RP }
  | "["             { LSB }
  | "]"             { RSB }
  | "|"             { BAR }
  | "+"             { ADD }
  | "-"             { SUB }
  | "*"             { MUL }
  | "/"             { DIV }
  | "^"             { EXP }
  | "=="            { EQ }
  | "!="            { NE }
  | "<"             { LT }
  | ">"             { GT }
  | "<="            { LE }
  | ">="            { GE }
  | "."             { DOT }
  | "=>"            { IMPL }
  | "->"            { RARROW }
  | number as i     { INT (int_of_string i) }
  | word as w       { check_keyword w }
  | eof             { EOF }
  | _ as c          { failwith (Format.sprintf "Invalid character: %c" c)}

and comment = parse
  | "(*"            { comment lexbuf; comment lexbuf }
  | "*)"            { () }
  | _               { comment lexbuf }
  | eof             { failwith "Unterminated commet" }
