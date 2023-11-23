{
  (* OCaml declaration *)

  open Parser
  open Printf

  exception Lexing_error of Location.lexeme_pos * string   

  (* Checks if an identifier exceeds the length limit of 64 characters *)
  let check_id_length id lexbuf = 
    if String.length id > 64 then raise (Lexing_error (Location.to_lexeme_position lexbuf, "Error: IDs cannot contain more than 64 characters"))
    else id
  
  (* Checks if an integer is representable with 32 bits *)
  let check_int32 n lexbuf =
    let n32 = try Int32.of_string n 
              with Failure(_) -> raise (Lexing_error (Location.to_lexeme_position lexbuf, "Error: Only 32-bit integers are supported"))
    in n32

  (* Hash table to handle language-reserved keywords *)
  let create_hashtable size init =
    let tbl = Hashtbl.create size in
      List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
      tbl
  
  (* A mapping from language-reserved keywords to tokens *)
  let keyword_table = 
    create_hashtable(16)[
      ("var", VAR);
      ("if", IF);
      ("return", RETURN);
      ("else", ELSE);
      ("while", WHILE);
      ("int", INT);
      ("char", CHAR);
      ("void", VOID);
      ("bool", BOOL);
      ("interface", INTERFACE);
      ("uses", USES);
      ("provides", PROVIDES);
      ("component", COMPONENT);
      ("connect", CONNECT);
      ("def", DEF);
      ("for", FOR);
      ("do", DO);
      ("extends", EXTENDS)
    ]
}


(* Declaration of regular expressions *)
let letter = ['a'-'z' 'A'-'Z']
let digit = ['0' - '9']
let hex = [ '0'-'9' 'A'-'F']
let special_char = ['~' '!' '#' '$' '%' '^' '&' '*' '(' ')' '_' '+' '|' '-' '=' '{' '}' '[' ']' ':' '"' ';' '<' '>' '?' ',' '.' '/' '@']


(* Declaration of scanner functions *)
rule next_token = parse
  | '\n'                                              { Lexing.new_line lexbuf; next_token lexbuf }
  | [' ' '\t']                                        { next_token lexbuf }
  | "/*"                                              { comment lexbuf }
  | "//"                                              { line_comment lexbuf }
  | "true"                                            { LBOOL(true) }
  | "false"                                           { LBOOL(false) }
  | (letter | '_') (letter | digit | '_')* as word    { try Hashtbl.find keyword_table word with Not_found -> ID(check_id_length word lexbuf) }
  | "0x" (hex)+ as num                                { LINT(check_int32 num lexbuf) } 
  | digit+ as num                                     { LINT(check_int32 num lexbuf) }
  | "'"                                               { character lexbuf }
  | "+"                                               { PLUS }
  | "-"                                               { MINUS }
  | "++"                                              { INCREMENT }
  | "--"                                              { DECREMENT }
  | "*"                                               { MULT }
  | "/"                                               { DIV }
  | "%"                                               { MOD }
  | "="                                               { ASSIGN }
  | "+="                                              { PLUSASSIGN }
  | "-="                                              { MINUSASSIGN }
  | "*="                                              { TIMESASSIGN }
  | "/="                                              { DIVASSIGN }
  | "%="                                              { MODASSIGN }
  | "=="                                              { EQ }
  | "!="                                              { NEQ }
  | "<"                                               { LT }
  | "<="                                              { LEQ }
  | ">"                                               { GT }
  | ">="                                              { GEQ }
  | "&"                                               { AMPERSAND }
  | "&&"                                              { AND }
  | "||"                                              { OR }
  | "!"                                               { NOT }
  | "("                                               { LPAREN }
  | ")"                                               { RPAREN }
  | "{"                                               { LBRACE }
  | "}"                                               { RBRACE }
  | "["                                               { LBRACKET }
  | "]"                                               { RBRACKET }
  | "."                                               { DOT }
  | "<-"                                              { LARROW }
  | ":"                                               { COLON }
  | ","                                               { COMMA }
  | ";"                                               { SEMICOLON }
  | eof                                               { EOF }
  | _                                                 { raise (Lexing_error (Location.to_lexeme_position lexbuf, "Unexpected character: " ^ (Lexing.lexeme lexbuf))) }

and comment = parse
  | '\n'    { Lexing.new_line lexbuf; comment lexbuf }
  | "*/"    { next_token lexbuf }
  | _       { comment lexbuf }
and line_comment = parse
  | '\n'    { Lexing.new_line lexbuf; next_token lexbuf }
  | _       { line_comment lexbuf }

and character = parse 
  | '\\' '\'' "'"                          { LCHAR ('\'') }
  | '\\' 'b' "'"                           { LCHAR ('\b') }
  | '\\' 'f' "'"                           { LCHAR ('\x0C') }
  | '\\' 't' "'"                           { LCHAR ('\t') }
  | '\\' '\\' "'"                          { LCHAR ('\\') } 
  | '\\' 'r' "'"                           { LCHAR ('\r') }
  | '\\' 'n' "'"                           { LCHAR ('\n') }
  | (letter | digit | special_char) "'"    { LCHAR (Lexing.lexeme_char lexbuf 0) }   (* for literal chars: it takes the first char in the matched string 'c' *)
