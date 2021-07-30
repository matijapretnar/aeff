{
  open Parser
  open Utils

  let reserved = Desugarer.StringMap.of_seq @@ List.to_seq [
    ("and", AND);
    ("await", AWAIT);
    ("as", AS);
    ("asr", ASR);
    ("begin", BEGIN);
    ("else", ELSE);
    ("end", END);
    ("false", BOOL false);
    ("fun", FUN);
    ("function", FUNCTION);
    ("if", IF);
    ("in", IN);
    ("land", LAND);
    ("let", LET);
    ("lor", LOR);
    ("lsl", LSL);
    ("lsr", LSR);
    ("lxor", LXOR);
    ("match", MATCH);
    ("mod", MOD);
    ("of", OF);
    ("or", OR);
    ("operation", OPERATION);
    ("promise", PROMISE);
    ("rec", REC);
    ("run", RUN);
    ("send", SEND);
    ("then", THEN);
    ("true", BOOL true);
    ("type", TYPE);
    ("unbox", UNBOX);
    ("until", UNTIL);
    ("with", WITH);
    ("when", WHEN)
  ]

  let escaped_characters = [
    ("\"", "\"");
    ("\\", "\\");
    ("\'", "'");
    ("n", "\n");
    ("t", "\t");
    ("b", "\b");
    ("r", "\r");
    (" ", " ");
  ]

}

let lname = ( ['a'-'z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9' '\'']*
            | ['_' 'a'-'z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9' '\'']+)

let uname = ['A'-'Z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9' '\'']*

let hexdig = ['0'-'9' 'a'-'f' 'A'-'F']

let int = ['0'-'9'] ['0'-'9' '_']*

let xxxint =
    ( ("0x" | "0X") hexdig (hexdig | '_')*
    | ("0o" | "0O") ['0'-'7'] ['0'-'7' '_']*
    | ("0b" | "0B") ['0' '1'] ['0' '1' '_']*)

let float =
  '-'? ['0'-'9'] ['0'-'9' '_']*
  (('.' ['0'-'9' '_']*) (['e' 'E'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']*)? |
   ('.' ['0'-'9' '_']*)? (['e' 'E'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']*))

let operatorchar = ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '.' '<' '=' '>' '?' '@' '^' '|' '~']

let prefixop = ['~' '?' '!']             operatorchar*
let infixop0 = ['=' '<' '>' '|' '&' '$'] operatorchar*
let infixop1 = ['@' '^']                 operatorchar*
let infixop2 = ['+' '-']                 operatorchar*
let infixop3 = ['*' '/' '%']             operatorchar*
let infixop4 = "**"                      operatorchar*

rule token = parse
  | '\n'                { Lexing.new_line lexbuf; token lexbuf }
  | [' ' '\r' '\t']     { token lexbuf }
  | "(*"                { comment 0 lexbuf }
  | int                 { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | xxxint              { try
                            INT (int_of_string (Lexing.lexeme lexbuf))
                          with Failure _ -> Error.syntax ~loc:(Location.of_lexeme (Lexing.lexeme_start_p lexbuf)) "Invalid integer constant"
                        }
  | float               { FLOAT (float_of_string(Lexing.lexeme lexbuf)) }
  | '"'                 { STRING (string "" lexbuf) }
  | lname               { let s = Lexing.lexeme lexbuf in
                            match Desugarer.StringMap.find_opt s reserved with
                              | Some t -> t
                              | None -> LNAME s
                        }
  | uname               { UNAME (Lexing.lexeme lexbuf) }
  | '\'' lname          { let str = Lexing.lexeme lexbuf in
                          PARAM (String.sub str 1 (String.length str - 1)) }
  | '_'                 { UNDERSCORE }
  | '('                 { LPAREN }
  | ')'                 { RPAREN }
  | '['                 { LBRACK }
  | ']'                 { RBRACK }
  | "[|"                { LBOXED }
  | "|]"                { RBOXED }
  | "<<"                { LPROMISE }
  | ">>"                { RPROMISE }
  | "::"                { CONS }
  | ':'                 { COLON }
  | ','                 { COMMA }
  | '|'                 { BAR }
  | "||"                { BARBAR }
  | ';'                 { SEMI }
  | "->"                { ARROW }
  | '='                 { EQUAL }
  | '*'                 { STAR }
  | '+'                 { PLUS }
  | '-'                 { MINUS }
  | "-."                { MINUSDOT }
  | '&'                 { AMPER }
  | "&&"                { AMPERAMPER }
  | prefixop            { PREFIXOP(Lexing.lexeme lexbuf) }
  | ":="                { INFIXOP0(":=") }
  | infixop0            { INFIXOP0(Lexing.lexeme lexbuf) }
  | infixop1            { INFIXOP1(Lexing.lexeme lexbuf) }
  | infixop2            { INFIXOP2(Lexing.lexeme lexbuf) }
  (* infixop4 comes before infixop3 because ** would otherwise match infixop3 *)
  | infixop4            { INFIXOP4(Lexing.lexeme lexbuf) }
  | infixop3            { INFIXOP3(Lexing.lexeme lexbuf) }
  | eof                 { EOF }

and comment n = parse
  | "*)"                { if n = 0 then token lexbuf else comment (n - 1) lexbuf }
  | "(*"                { comment (n + 1) lexbuf }
  | '\n'                { Lexing.new_line lexbuf; comment n lexbuf }
  | _                   { comment n lexbuf }
  | eof                 { Error.syntax ~loc:(Location.of_lexeme (Lexing.lexeme_start_p lexbuf)) "Unterminated comment" }

and string acc = parse
  | '"'                 { acc }
  | '\\'                { let esc = escaped lexbuf in string (acc ^ esc) lexbuf }
  | [^'"' '\\']*        { string (acc ^ (Lexing.lexeme lexbuf)) lexbuf }
  | eof                 { Error.syntax ~loc:(Location.of_lexeme (Lexing.lexeme_start_p lexbuf)) "Unterminated string %s" acc}

and escaped = parse
  | _                   { let str = Lexing.lexeme lexbuf in
                          try List.assoc str escaped_characters
                          with Not_found -> Error.syntax ~loc:(Location.of_lexeme (Lexing.lexeme_start_p lexbuf)) "Unknown escaped character %s" str
                        }

{
  let read_file parser fn =
  try
    let fh = open_in fn in
    let lex = Lexing.from_channel fh in
    lex.Lexing.lex_curr_p <- {lex.Lexing.lex_curr_p with Lexing.pos_fname = fn};
    try
      let terms = parser lex in
      close_in fh;
      terms
    with
      (* Close the file in case of any parsing errors. *)
      Error.Error err -> close_in fh; raise (Error.Error err)
  with
    (* Any errors when opening or closing a file are fatal. *)
    Sys_error msg -> Error.fatal "%s" msg
}
