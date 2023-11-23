/**
 mComp parser specification 
 */
%{

    open Ast
    open Printf

    (* a mutable record used to maintain the program's interfaces, components and connections found during parsing *)
    type compilation_unit_m = {
        mutable interfaces_m : Location.code_pos interface_decl list;
        mutable components_m : Location.code_pos component_decl list;
        mutable connections_m : connection list ;
    }
    let cu = ref {interfaces_m=[]; components_m=[]; connections_m=[]}

    (* creation of an annotated node *)
    let make_annotated_node (pos : Lexing.position * Lexing.position) (n:'a) = 
      {node=n; annot=(Location.to_code_position pos)}

    (* Util function to represent the FOR construct as a WHILE *)
    let convert_for_to_while pos e1 e2 e3 b = 
      let append_expr pos e3 = 
        match e3 with
          | None -> []
          | Some e -> [make_annotated_node pos (Stmt(make_annotated_node pos (Expr(e))))] 
      in 
      let make_while pos e2 e3 b = 
        let tempblock = [make_annotated_node pos (Stmt(b))] @ (append_expr pos e3) in
        let b = (make_annotated_node pos(Block(tempblock))) in
          match e2 with 
            | None -> [make_annotated_node pos (Stmt(make_annotated_node pos (While((make_annotated_node pos (BLiteral(true))),b))))]
            | Some e -> [make_annotated_node pos (Stmt(make_annotated_node pos (While(e,b))))]
      in 
      let make_initialization pos e1 = match e1 with
        | None -> []
        | Some e -> [make_annotated_node pos (Stmt(make_annotated_node pos (Expr(e))))]
      in 
      (make_initialization pos e1) @ (make_while pos e2 e3 b)

      (* util function to represent a DO-WHILE as a statement followed by a loop *)
      let make_do_while pos s e = 
        let stmtnode = make_annotated_node pos (Stmt(s)) in
        let whilenode = make_annotated_node pos (Stmt(make_annotated_node pos (While(e,s)))) in
        [stmtnode] @ [whilenode]

%} 


/* Token declarations */
%token <string> ID
%token <int32> LINT
%token <bool> LBOOL
%token <char> LCHAR
%token INT CHAR BOOL VOID
%token IF RETURN ELSE WHILE FOR DO
%token PLUS MINUS MULT DIV MOD AMPERSAND
%token AND OR NOT 
%token ASSIGN LT GT EQ NEQ LEQ GEQ
%token PLUSASSIGN MINUSASSIGN TIMESASSIGN DIVASSIGN MODASSIGN
%token INCREMENT DECREMENT
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token COMMA DOT COLON SEMICOLON
%token INTERFACE USES PROVIDES EXTENDS COMPONENT CONNECT VAR DEF LARROW
%token EOF

/* Precedence and associativity specification */

/* lowest precedence */
%nonassoc NOELSE
%nonassoc ELSE
%right TIMESASSIGN DIVASSIGN MODASSIGN
%right PLUSASSIGN MINUSASSIGN
%right ASSIGN
%left OR
%left AND
%left EQ NEQ
%nonassoc GT LT GEQ LEQ
%left PLUS MINUS
%left MULT DIV MOD
%nonassoc NOT
/* highest precedence */

/* Start symbol */
%start compilation_unit
%type <Ast.located_compilation_unit> compilation_unit 

%% 


/* Grammar Specification */
compilation_unit:
  | EOF                 { CompilationUnit{interfaces=[]; components=[]; connections=[]} }
  | topdecl_list EOF    { CompilationUnit{interfaces = !cu.interfaces_m; components = !cu.components_m; connections = !cu.connections_m} }                      
;

topdecl_list:
  | topdecl_list topdecl  {()} (* empty because of side effects *)
  | topdecl               {()} (* empty because of side effects *)
;

topdecl:
  | INTERFACE ID LBRACE imemberdecl_list RBRACE                                   {!cu.interfaces_m <- !cu.interfaces_m @ [(make_annotated_node ($loc) (InterfaceDecl{iname = $2; declarations = (List.rev $4); extends = []}))] }
  | INTERFACE ID EXTENDS interfaces_list LBRACE imemberdecl_list RBRACE           {!cu.interfaces_m <- !cu.interfaces_m @ [(make_annotated_node ($loc) (InterfaceDecl{iname = $2; declarations = (List.rev $6); extends = $4}))] }
  | COMPONENT ID provideclause_opt useclause_opt LBRACE cmemberdecl_list RBRACE   {!cu.components_m <- !cu.components_m @ [(make_annotated_node ($loc) (ComponentDecl{cname=$2; uses=$4; provides=$3; definitions=(List.rev $6)}))] }
  | CONNECT singlelink                                                            {!cu.connections_m <- !cu.connections_m @ [$2]}
  | CONNECT LBRACE link_list_opt RBRACE                                           {!cu.connections_m <- !cu.connections_m @ ($3)}
;

link_list_opt:
  | /*empty*/ {[]}
  | link_list {List.rev $1}
;

link_list:
  | link_list link  {$2 :: $1}
  | link   {[$1]}
;

link:
  | ID DOT ID LARROW ID DOT ID SEMICOLON { Link($1, $3, $5, $7) }
;

singlelink:
  | ID DOT ID LARROW ID DOT ID { Link($1, $3, $5, $7) }
;

interfaces_list:
  | ID                        {[$1]}
  | interfaces_list COMMA ID        {$3 :: $1}
;

imemberdecl_list:
  | imemberdecl_list imemberdecl  {$2 :: $1}
  | imemberdecl                   {[$1]}
;

imemberdecl:
  | VAR varsign SEMICOLON   {make_annotated_node ($loc) (VarDecl($2,None))}
  | funproto SEMICOLON      {make_annotated_node ($loc) ($1)}
;

varsign:
  | ID COLON typ   {($1,$3)}
;

typ:
  | basictype                   {$1}
  | typ LBRACKET RBRACKET       {TArray($1, None)}
  | typ LBRACKET LINT RBRACKET  {TArray($1, Some($3))}
  | AMPERSAND basictype         {TRef($2)}
;

funproto:
  | DEF ID LPAREN parameters_list_opt RPAREN basictype_opt  {FunDecl{rtype = $6; fname = $2; formals = $4; body = None}} (* make_annotated_node ($loc) (FunDecl{rtype = $6; fname = $2; formals = $4; body = None}) *)
;

parameters_list_opt:
  | /*empty*/       {[]}
  | parameters_list {List.rev $1}
;

parameters_list:
  | parameters_list COMMA varsign {$3 :: $1}
  | varsign                       {[$1]}
;

basictype_opt:
  | /*empty*/         {TVoid}
  | COLON basictype   {$2}
;

basictype:
  | INT   {TInt}
  | CHAR  {TChar}
  | VOID  {TVoid}
  | BOOL  {TBool}
;

provideclause_opt:
  | /*empty*/         {[]}
  | PROVIDES id_list  {$2}
; 

id_list:
  | id_list COMMA ID {$3 :: $1}
  | ID               {[$1]}
;

useclause_opt:
  | /*empty*/      {[]}
  | USES id_list   {$2}
; 

cmemberdecl_list:
  | cmemberdecl_list cmemberdecl  {$2 :: $1}
  | cmemberdecl                   {[$1]}
;

cmemberdecl:
  | VAR varsign SEMICOLON                            {make_annotated_node ($loc) (VarDecl($2,None))}
  | VAR ID ASSIGN expr COLON typ SEMICOLON            {make_annotated_node ($loc) (VarDecl(($2,$6),Some($4)))}
  | fundecl                                          {make_annotated_node ($loc) (FunDecl($1))}
;

fundecl:
  | DEF ID LPAREN parameters_list_opt RPAREN basictype_opt block  {{rtype = $6; fname = $2; formals = $4; body = Some($7)}}    (* make_annotated_node ($loc) ({rtype = $6; fname = $2; formals = $4; body = Some($7)}) *)
;

block:
  | LBRACE stmordec_list_opt RBRACE   {make_annotated_node ($loc) (Block($2))}
;

stmordec_list_opt:
  | /*empty*/       {[]}
  | stmordec_list   {List.rev $1}
;

stmordec_list:
  | stmordec_list stmordec  {$2 :: $1}
  | stmordec                {[$1]}
;

stmordec:
  | stmt                                             {make_annotated_node ($loc) (Stmt($1))}
  | VAR varsign SEMICOLON                            {make_annotated_node ($loc) (LocalDecl($2,None))}
  | VAR ID ASSIGN expr COLON typ SEMICOLON            {make_annotated_node ($loc) (LocalDecl(($2,$6),Some($4)))}
;

stmt:
  | RETURN expr_opt SEMICOLON                                                   {make_annotated_node ($loc) (Return($2))}
  | SEMICOLON                                                                   {make_annotated_node ($loc) (Skip)}
  | expr SEMICOLON                                                              {make_annotated_node ($loc) (Expr($1))}
  | block                                                                       {$1} 
  | WHILE LPAREN expr RPAREN stmt                                               {make_annotated_node ($loc) (While($3, $5))}
  | DO stmt WHILE LPAREN expr RPAREN SEMICOLON                                  {make_annotated_node ($loc) (Block(make_do_while $loc $2 $5))}
  | IF LPAREN expr RPAREN stmt ELSE stmt                                        {make_annotated_node ($loc) (If($3, $5, $7))}
  | IF LPAREN expr RPAREN stmt %prec NOELSE                                     {make_annotated_node ($loc) (If($3, $5, make_annotated_node ($loc) (Block([]))  ))}
  | FOR LPAREN expr_opt SEMICOLON expr_opt SEMICOLON expr_opt RPAREN stmt       {make_annotated_node ($loc) (Block(convert_for_to_while $loc $3 $5 $7 $9))}
;

expr_opt:
    |/* empty */ {None}
    | expr       {Some $1}
;

expr:
  | LINT                                {make_annotated_node ($loc) (ILiteral($1))}  
  | LCHAR                               {make_annotated_node ($loc) (CLiteral($1))}
  | LBOOL                               {make_annotated_node ($loc) (BLiteral($1))}
  | LPAREN expr RPAREN                  {$2}
  | AMPERSAND lvalue                    {make_annotated_node ($loc) (Address($2))}
  | lvalue ASSIGN expr                  {make_annotated_node ($loc) (Assign(Eq, $1, $3))}
  | lvalue PLUSASSIGN expr              {make_annotated_node ($loc) (Assign(Plus, $1, $3))}
  | lvalue MINUSASSIGN expr             {make_annotated_node ($loc) (Assign(Minus, $1, $3))}
  | lvalue TIMESASSIGN expr             {make_annotated_node ($loc) (Assign(Times, $1, $3))}
  | lvalue DIVASSIGN expr               {make_annotated_node ($loc) (Assign(Div, $1, $3))}
  | lvalue MODASSIGN expr               {make_annotated_node ($loc) (Assign(Mod, $1, $3))}

  | NOT expr                            {make_annotated_node ($loc) (UnaryOp(Not, $2))}
  | ID LPAREN expr_list_opt RPAREN      {make_annotated_node ($loc) (Call(None, $1, $3)) }
  | lvalue                              {make_annotated_node ($loc) (LV($1))}
  | MINUS expr                          {make_annotated_node ($loc) (UnaryOp(Neg, $2))}
  | lvalue INCREMENT                    {make_annotated_node ($loc) (Increment(Post, $1,1l))}
  | lvalue DECREMENT                    {make_annotated_node ($loc) (Increment(Post, $1,-1l))}
  | INCREMENT lvalue                    {make_annotated_node ($loc) (Increment(Pre, $2,1l))}
  | DECREMENT lvalue                    {make_annotated_node ($loc) (Increment(Pre, $2,-1l))}
  | expr PLUS expr                      {make_annotated_node ($loc) (BinaryOp(Add, $1, $3))}
  | expr MINUS expr                     {make_annotated_node ($loc) (BinaryOp(Sub, $1, $3))}
  | expr MULT expr                      {make_annotated_node ($loc) (BinaryOp(Mult, $1, $3))}
  | expr MOD  expr                      {make_annotated_node ($loc) (BinaryOp(Mod, $1, $3))}
  | expr DIV  expr                      {make_annotated_node ($loc) (BinaryOp(Div, $1, $3))}
  | expr AND  expr                      {make_annotated_node ($loc) (BinaryOp(And, $1, $3))}
  | expr OR   expr                      {make_annotated_node ($loc) (BinaryOp(Or, $1, $3))}
  | expr LT   expr                      {make_annotated_node ($loc) (BinaryOp(Less, $1, $3))}
  | expr GT   expr                      {make_annotated_node ($loc) (BinaryOp(Greater, $1, $3))}
  | expr LEQ  expr                      {make_annotated_node ($loc) (BinaryOp(Leq, $1, $3))}
  | expr GEQ  expr                      {make_annotated_node ($loc) (BinaryOp(Geq, $1, $3))}
  | expr EQ   expr                      {make_annotated_node ($loc) (BinaryOp(Equal, $1, $3))}
  | expr NEQ  expr                      {make_annotated_node ($loc) (BinaryOp(Neq, $1, $3))}
;


expr_list_opt:
  | /* empty */ {[]}
  | expr_list   {List.rev $1}
;

expr_list:
  | expr_list COMMA expr  {$3 :: $1}
  | expr                  {[$1]}
;

lvalue:
  | ID                          {make_annotated_node ($loc) (AccVar(None, $1))}
  | ID LBRACKET expr RBRACKET   {make_annotated_node ($loc) (AccIndex( make_annotated_node ($loc) (AccVar(None, $1)), $3))}
;
