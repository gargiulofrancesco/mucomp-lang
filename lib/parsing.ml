exception Syntax_error of Location.lexeme_pos * string

let parse lexbuf = Parser.compilation_unit lexbuf