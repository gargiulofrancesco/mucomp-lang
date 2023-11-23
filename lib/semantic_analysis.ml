exception Semantic_error of Location.code_pos * string

open Ast
open Symbol_table
open Printf


(* 
  An environment is composed by four distinct symbol tables to differentiate betweem interfaces, components, 
  functions, and variables. In particular, the "interfaces" symbol table consists of the position of an interface
  and of a list (interface_id, memberdecl_id, memberdecl_typ, memberdecl_pos) of its members. This info is used 
  to retrieve at any moment the members of some interfaces and to combine them in order to setup scopes.
*)
type env = {
  interfaces : ((identifier * identifier * typ * Location.code_pos) list * Location.code_pos) Symbol_table.t; 
  (* used interfaces, provided interfaces, position *)
  components : (identifier list * identifier list * Location.code_pos) Symbol_table.t; 
  functions : (identifier option * typ * Location.code_pos) Symbol_table.t; 
  variables : (identifier option * typ * Location.code_pos) Symbol_table.t; 
}


let empty_env = 
  {
    interfaces = begin_block empty_table; 
    components = begin_block empty_table; 
    functions = begin_block empty_table; 
    variables = begin_block empty_table
  }


(* initializes the env with the stdlib interfaces *)
let init_env = 
  let pos = Location.dummy_code_pos in
  (* adding Prelude and Main interfaces names *)
  let prelude_b = [("Prelude", "print", TFun([TInt],TVoid), pos)] @ [("Prelude", "getint", TFun([], TInt), pos)] in
  let app_b = [("App", "main", TFun([],TInt), pos)] in
  let envp = {empty_env with interfaces=add_entry "Prelude" (prelude_b, pos) (begin_block empty_table)} in
  {envp with interfaces = add_entry "App" (app_b, pos) envp.interfaces}  


(* A global mutable environment is maintained during the sematic analysis *)
type mutable_env = {mutable env: env}
let globalenv = ref {env=init_env}




(* checks if a list has duplicates *)
let rec has_duplicates list = match list with
  | [] -> false 
  | h :: l -> if List.mem h l then true else has_duplicates l


(* given a list of tuples (a,b), generate a list consisting of each second element b *)
let list_of_second list = List.map (fun tuple -> match tuple with (_,elem) -> elem) list


(* checks if a string corresponds to an interface identifier *)
let is_interface env loc str =
  if lookup str env.interfaces = None then raise (Semantic_error (loc, "Error: " ^ str ^  " is not a declared interface in this scope"))
  else ()




(* checks that t is a legal typ *)
let rec check_typ loc t = match t with
  | TArray(TArray(_,_),_) -> raise (Semantic_error (loc, "Error: multidimensional arrays are not allowed"))
  | TArray(TVoid, _) -> raise (Semantic_error (loc, "Error: cannot have an array of void elements"))
  | TArray(TRef(TVoid),_) -> raise (Semantic_error (loc, "Error: cannot have an array of references of void"))
  | TArray(_, Some size) -> if size < Int32.one then raise (Semantic_error (loc, "Error: arrays must have a positive size")) else ()
  | TRef(TVoid) -> raise (Semantic_error (loc, "Error: cannot have a reference to void"))
  | _ -> ()


(* semantic check for variable declarations in components *)
let check_vardecl loc t = match t with 
  | TVoid -> raise (Semantic_error (loc, "Error: cannot have a void variable"))
  | TArray(atyp,size) -> 
      if size = None then raise (Semantic_error (loc, "Error: array variables must have a size"))
      else check_typ loc t
  | _ -> check_typ loc t


(* semantic check for variables declared in interfaces and for function parameters *)
let check_parameter loc t= match t with 
  | TVoid -> raise (Semantic_error (loc, "Error: cannot have a void variable"))
  | TArray(atyp,size) -> 
      if size <> None then raise (Semantic_error (loc, "Error: array parameter cannot have a size"))
      else check_typ loc t  
  | _ -> check_typ loc t


(* semantic check for a binop, returns the binop type *)
let check_binop loc binop t1 t2 =
  if t1 <> t2 then raise (Semantic_error (loc, "Error: non-matching expressions"))
  else match binop with 
    | Add | Sub | Mult | Div | Mod  -> 
        if t1 <> TInt then raise (Semantic_error (loc, "Error: integer expressions expected")) else TInt
    | Less | Leq | Greater | Geq -> 
        if t1 <> TInt then raise (Semantic_error (loc, "Error: integer expressions expected")) else TBool
    | Equal | Neq -> 
      (
        match t1 with 
          | TInt | TBool | TChar -> TBool
          | _ -> raise (Semantic_error (loc, "Error: wrong expressions type for this operator")) 
      )
    | And | Or -> 
        if t1 <> TBool then raise (Semantic_error (loc, "Error: bool expressions expected")) else TBool


let type_of_assignment loc tl te = 
  match (tl, te) with 
    | TArray(t1, None), TArray(t2, _) -> if t1 <> t2 then raise(Semantic_error (loc, "Error: different array reference types")) else TArray(t1,None)
    | TArray(_, _), TArray (_, _) -> raise(Semantic_error (loc, "Error: cannot assign an array"))
    | TRef(t1), TRef(TRef(_)) -> raise(Semantic_error (loc, "Error: a reference cannot be assigned a reference to reference "))
    | TRef(t1), TRef(t2) -> if t1 <> t2 then raise(Semantic_error (loc, "Error: references have different types")) else TRef(t1)
    | TRef(t1), t2 -> if t1 <> t2 then raise(Semantic_error (loc, "Error: types do not match")) else t2
    | t1, TRef(t2) -> if t1 <> t2 then raise(Semantic_error (loc, "Error: types do not match")) else t2
    | t1, t2 -> if t1 <> t2 then raise(Semantic_error (loc, "Error: types do not match")) else t1


(* returns the type of a well-formed expression *)
let rec type_of_expr expr = 
  let env = !globalenv.env in 
  match expr.node with
    | LV(lval) -> type_of_lval lval
    | Assign(atype, lval, expra) -> 
        let result = type_of_assignment expr.annot (type_of_lval lval) (type_of_expr expra) in
        (
          match (atype, result) with
          | (Eq, _) 
          | (_, TInt) -> result
          | _ -> raise(Semantic_error (expr.annot, "Error: compound assignment expects an integer type "))
        )
    | Increment(_, lval, _) ->
        let lval_type = type_of_lval lval in
        (
          match lval_type with
            | TInt 
            | TRef(TInt)
            | TArray(TInt,_) -> lval_type
            | _ -> raise (Semantic_error (expr.annot, "Error: this operand in not applicable on the given variable"))
        )
    | ILiteral(_) -> TInt
    | CLiteral(_) -> TChar
    | BLiteral(_) -> TBool
    | UnaryOp(uop, expru) -> 
      (
        match uop with
          | Not -> if rvalue_of_ref expru = TBool then TBool else raise (Semantic_error (expr.annot, "Error: Not operator applied to non-boolean expression"))
          | Neg -> if rvalue_of_ref expru = TInt then TInt else raise (Semantic_error (expr.annot, "Error: Neg operator applied to non-integer expression"))
      )
    | Address(lvalue) -> TRef(type_of_lval lvalue)
    | BinaryOp(binop, expr1, expr2) -> check_binop expr.annot binop (rvalue_of_ref expr1) (rvalue_of_ref expr2)
    | Call(interf_opt, id, expr_l) -> 
      let ptypes = List.map type_of_expr expr_l in
      let f = lookup id env.functions in 
      match f with
        | None -> raise (Semantic_error (expr.annot, "Error: function " ^ id ^ " is not defined in this scope"))
        | Some(_,t,_) -> match t with
        | TFun(formals, rtype) -> 
            if List.length expr_l <> List.length formals then raise (Semantic_error (expr.annot, "Error: incorrect number of parameters for function call"))
            else List.iter2 (fun ft pt -> type_of_assignment expr.annot ft pt |> ignore) formals ptypes; rtype
        | _ -> raise (Semantic_error (expr.annot, "Error: function " ^ id ^ " is not defined in this scope"))

and type_of_lval lval = 
  let env = !globalenv.env in 
  match lval.node with
    | AccVar(interf_opt, id) -> 
      (
        match lookup id env.variables with
          | None -> raise (Semantic_error (lval.annot, "Error: variable " ^ id ^ " is not defined in this scope"))
          | Some(_, t, _) -> t
      )
    | AccIndex(lvala, expr) -> 
      (
        if type_of_expr expr <> TInt then raise (Semantic_error (lval.annot, "Error: index expression is not an integer"))
        else match type_of_lval lvala with
          | TArray(t,_) -> t
          | _ -> raise (Semantic_error (lval.annot, "Error: cannot access a non-array with an index"))
      )

(* automatically dereferences a rvalue reference *)
and rvalue_of_ref expr = 
  let t = type_of_expr expr in 
  match t with
    | TRef(tr)-> tr
    | _ -> t


(* converts a located expression node to a typed expression node *)
 let rec make_typed_expr (e: Location.code_pos expr) = 
  let env = !globalenv.env in 
  match e.node with
  | LV(lv) -> make_typed_lvalue lv
  | Assign(atype, lv, expr) ->
    (
      let lvtemp = make_typed_lvalue lv in 
      let texpr = make_typed_expr expr in 
        match lvtemp.node with
          | LV(lvtyped) -> {node=Assign(atype, lvtyped, texpr); annot=lvtyped.annot}
          | _ -> raise (Semantic_error (e.annot, "Error: this should not happen"))
    )
  | Increment(inct, lv, k) -> 
      let lvtemp = make_typed_lvalue lv in
      let lvtyped = 
        match lvtemp.node with 
          | LV(lvtp) -> lvtp
          | _ -> raise (Semantic_error (e.annot, "Error: this should not happen"))
      in 
      {node=Increment(inct, lvtyped, k); annot=lvtyped.annot}
  | ILiteral(n) -> {node=ILiteral(n); annot=TInt}
  | CLiteral(c) -> {node=CLiteral(c); annot=TChar}
  | BLiteral(b) -> {node=BLiteral(b); annot=TBool}
  | UnaryOp(uop, expru) -> let tempexpr = make_typed_expr expru in {node=UnaryOp(uop, tempexpr); annot=tempexpr.annot}
  | Address(lv) -> 
    (
      let tlv = make_typed_lvalue lv in 
        match tlv.node with 
          | LV(lvl) -> {node=Address(lvl); annot=lvl.annot}
          | _ -> raise (Semantic_error (e.annot, "Error: this should not happen"))
    )
  | BinaryOp(binop, expr1, expr2) -> 
    (
      let te1 = make_typed_expr expr1 in 
      let te2 = make_typed_expr expr2 in 
      let botype = type_of_expr e in 
      {node=BinaryOp(binop, te1, te2); annot=botype}
    )
  | Call(interf_opt, id, expr_l) -> 
    (
      let texprl = List.map make_typed_expr expr_l in 
      let f = lookup id env.functions in match f with
        | None -> raise (Semantic_error (e.annot, "Error: function " ^ id ^ " is not defined in this scope"))
        | Some(iopt, t, _) -> 
            match t with 
              | TFun(formals, rtype) -> {node=Call(iopt, id, texprl); annot=rtype}
              | _ -> raise (Semantic_error (e.annot, "Error: function " ^ id ^ " is not defined in this scope"))
    )
and make_typed_lvalue (lval: Location.code_pos lvalue) = match lval.node with
| AccVar(interf_opt, id) -> 
  (
    let env = !globalenv.env in 
      match lookup id env.variables with
        | None -> raise (Semantic_error (lval.annot, "Error: variable " ^ id ^ " is not defined in this scope"))
        | Some (interface_opt, t, _) -> 
            let tnode = {node=AccVar(interface_opt, id); annot=type_of_lval lval} in {node=LV(tnode); annot=tnode.annot} 
  ) 
| AccIndex(lvalacc, expr) -> 
    let tlvalacc = make_typed_lvalue lvalacc in 
    let texpr = make_typed_expr expr in 
      match tlvalacc.node with 
        | LV(lvl) -> let tnode = {node=AccIndex(lvl, texpr); annot=lvl.annot} in {node=LV(tnode); annot=tnode.annot}
        | _ -> raise (Semantic_error (lval.annot, "Error: this should not happen"))


(* Semantically checks a statement or declaration and generates its corresponding typed node *)
let rec check_stmtordec rtype stmtordec = 
  let env = !globalenv.env in 
  match stmtordec.node with 
    | LocalDecl((id,t), eopt)-> 
      (
          let enode = 
            match eopt with 
              | None -> None 
              | Some(e) -> 
                  type_of_assignment stmtordec.annot t (type_of_expr e) |> ignore;
                  Some(make_typed_expr e)
          in 
          check_vardecl stmtordec.annot t;
          try (
            let newglobaltable = {env with variables = add_entry id (None, t,stmtordec.annot) env.variables}
            in !globalenv.env <- newglobaltable;
            {node=LocalDecl((id,t), enode); annot=t}
          )
          with DuplicateEntry(m) -> raise (Semantic_error (stmtordec.annot, "Error: variable "^m^" is already declared in this scope" ))
      )
    | Stmt(stmt) -> 
        let typed_stmt = check_stmt rtype stmt in {node=Stmt(typed_stmt); annot=typed_stmt.annot}
  
and check_stmt rtype stmt = 
  let env = !globalenv.env in 
  match stmt.node with
    | If(expr, stmt1, stmt2) -> 
        if type_of_expr expr <> TBool then raise (Semantic_error (expr.annot, "Error: if guard expression has not type bool" ))
        else let typed_stmt1 = check_stmt rtype stmt1 in 
        let typed_stmt2 = check_stmt rtype stmt2 in 
        let typed_expr = make_typed_expr expr in 
        {node=If(typed_expr, typed_stmt1,typed_stmt2); annot=TVoid}
    | While(expr, stmt1) -> 
        if type_of_expr expr <> TBool then raise (Semantic_error (expr.annot, "Error: guard expression has not type bool" ))
        else let typed_stmt = check_stmt rtype stmt1 in 
        let typed_expr = make_typed_expr expr in 
        {node=While(typed_expr, typed_stmt); annot=TVoid}
    | Expr(expr) -> 
        type_of_expr expr |> ignore;
        let typed_expr = make_typed_expr expr in 
        {node=Expr(typed_expr); annot=typed_expr.annot}
    | Return(expr_opt) -> (
        match expr_opt with 
          | None -> 
              if rtype <> TVoid then raise (Semantic_error (stmt.annot, "Error: return type does not match function type" )) 
              else {node=Return(None); annot=TVoid}
          | Some(expr) -> 
              if type_of_expr expr <> rtype then raise (Semantic_error (stmt.annot, "Error: return type does not match function type" )) 
              else let typed_expr = make_typed_expr expr in 
              {node=Return(Some(typed_expr)); 
              annot=typed_expr.annot})
    | Block(stmtordec_l) -> 
        let env_block = {env with variables = begin_block env.variables} in 
        !globalenv.env <- env_block;
        let typed_stmtordec_l = List.map (check_stmtordec rtype) stmtordec_l in 
        !globalenv.env <- env;
        {node=Block(typed_stmtordec_l); annot=TVoid}
    | Skip -> {node=Skip; annot=TVoid}


(* checks if a block has a return statement that is always executed *)
let rec has_return stmtordec_l = match stmtordec_l with
| [] -> false
| h :: rl -> 
  match h.node with
    | LocalDecl(_) -> has_return rl
    | Stmt(stmt) -> match stmt.node with  
        | Return(_) -> true
        | If (e, s1, s2) -> (
            match (s1.node, s2.node) with 
              | (Return(_), Return(_)) -> true
              | (If(_,_,_), If(_,_,_)) -> (has_return [{node=Stmt(s1); annot=s1.annot}] && has_return [{node=Stmt(s2); annot=s2.annot}]) || has_return rl
              | (Return(_)), If(e2, _,_) -> (has_return [{node=Stmt(s2); annot=s2.annot}]) || has_return rl
              | (If(_,_,_), Return(_)) -> (has_return [{node=Stmt(s1); annot=s1.annot}]) || has_return rl
              | (Block(sd_l), If(_,_,_)) ->  (has_return sd_l && has_return [{node=Stmt(s2); annot=s2.annot}]) || has_return rl
              | (If(_,_,_), Block(sd_l)) -> (has_return [{node=Stmt(s1); annot=s1.annot}] && has_return sd_l) || has_return rl
              | (Block(sd_l1), Block(sd_l2)) -> (has_return sd_l1 && has_return sd_l2) || has_return rl
              | (Block(sd_l1), Return(_)) -> has_return sd_l1 || has_return rl
              | (Return(_), Block(sd_l2)) -> has_return sd_l2 || has_return rl
              | (_,_) -> has_return rl)
        | While(e, s) -> has_return rl
        | Expr(_) -> has_return rl
        | Block(sd_l) -> has_return sd_l || has_return rl
        | Skip -> has_return rl


(* traverses the AST and removes instructions that are located after an always executed "return" *)
let rec remove_unreachable stmordecl = 
  match stmordecl with
  | [] -> []
  | h :: rl -> 
      match h.node with 
        | LocalDecl(_) -> [h] @ remove_unreachable rl 
        | Stmt(s) ->
            match s.node with 
              | If(e, s1, s2) -> 
                  let news1 = 
                    match s1.node with 
                      | Block(tsd_l1) -> {s1 with node = Block(remove_unreachable tsd_l1)}
                      | _ -> s1
                  in
                  let news2 = 
                    match s2.node with 
                      | Block(tsd_l2) -> {s1 with node = Block(remove_unreachable tsd_l2)}
                      | _ -> s2
                  in
                  let newstmt = {s with node = If(e, news1, news2)} in 
                  let newstmtordecl = {h with node=Stmt(newstmt)} in
                  if has_return [h] then [newstmtordecl]
                  else [newstmtordecl] @ remove_unreachable rl

              | While(e, s1) -> [h] @ remove_unreachable rl
              | Block(sd_l) -> 
                  let newstmt = {s with node = Block(remove_unreachable sd_l)} in 
                  let newstmtordecl = {h with node=Stmt(newstmt)} in
                  if has_return sd_l then [newstmtordecl]
                  else [newstmtordecl] @ remove_unreachable rl
                  
              | Return(_) -> [h]
              | Skip -> [h] @ remove_unreachable rl
              | Expr(_) -> [h] @ remove_unreachable rl


(* checks that the function parameter is legal and that there are no parameters with the same name *)
let check_function_parameter loc param = 
  let env = !globalenv.env in 
  match param with (id, t) ->
  check_parameter loc t; 
  try (
     let newglobaltable = {env with variables = add_entry id (None, t, loc) env.variables} in 
     !globalenv.env <- newglobaltable
    )
  with DuplicateEntry(m) -> raise (Semantic_error (loc, "Error: parameter "^m^" is already declared in this scope" ))


(* semantic check for functions and function prototypes *)
let check_function loc f = 
  match f with {rtype=ftype; fname=id; formals=param; body=b}-> 
    List.iter (check_function_parameter loc) param;
    match b with
      | None -> {node=FunDecl({rtype=ftype; fname=id; formals=param; body=None}); annot=TFun(list_of_second param,ftype)}
      | Some(stmt) -> 
          let typed_statement = check_stmt ftype stmt in 
          match typed_statement.node with 
            | Block(sd_l) -> 
                let typed_statement = {typed_statement with node = Block(remove_unreachable sd_l)} in 
                if has_return sd_l || ftype=TVoid || id="main" then {node=FunDecl({rtype=ftype; fname=id; formals=param; body=Some(typed_statement)}); annot=TFun(list_of_second param,ftype)} 
                else raise (Semantic_error (loc, "Error: function body must have a return statement" ))
                
            | _ -> failwith "Internal Error: this should not happen"


let add_memberdecl_to_env env member_decl = 
  match member_decl.node with
    | FunDecl({rtype=ftype; fname=id; formals=param; body=b})-> (
        try{ env with functions = add_entry id (None, TFun((list_of_second param), ftype), member_decl.annot) env.functions}
        with DuplicateEntry(m) -> raise (Semantic_error (member_decl.annot, "Error: function "^m^" is already declared in this scope" )))
    | VarDecl((id,t),_) -> 
        try { env with variables = add_entry id (None, t, member_decl.annot) env.variables}
        with  DuplicateEntry(m) -> raise (Semantic_error (member_decl.annot, "Error: variable "^m^" is already declared in this scope" ))


(* checks that an interface memberdecl is well-formed and returns its (id, typ, pos) *)
let get_interface_memberdecl_bindings interface member_decl = 
  let env = !globalenv.env in 
  match member_decl.node with
    | FunDecl({rtype=ftype; fname=id; formals=param; body=b}) ->
        let interenv = {env with variables = begin_block env.variables} in 
        !globalenv.env <- interenv;
        check_function member_decl.annot {rtype=ftype; fname=id; formals=param; body=b} |> ignore;
        !globalenv.env <- env;
        (interface, id, TFun((list_of_second param), ftype), member_decl.annot)
    | VarDecl((id,t), _) -> 
        check_parameter member_decl.annot t;
        (interface, id, t, member_decl.annot)


(* checks that a component memberdecl is well-formed  *)
let check_memberdecl member_decl = 
  let rec check_globalvar_init e = 
    match e.node with 
      | UnaryOp(_,e1) -> check_globalvar_init e1 
      | BinaryOp(_,e1,e2) -> 
          check_globalvar_init e1;
          check_globalvar_init e2;
      | ILiteral(_)
      | CLiteral(_)
      | BLiteral(_) -> ()
      | _ -> raise (Semantic_error (e.annot, "Error: this expression is not allowed for global variable initialization" )) 
  in
  let env = !globalenv.env in 
  match member_decl.node with
    | FunDecl(fdecl) -> 
        let funenv = {env with variables = begin_block env.variables} in 
        !globalenv.env <- funenv ;
        let typed_fucntion = check_function member_decl.annot fdecl in 
        !globalenv.env <- env;
        typed_fucntion
    | VarDecl((id,t),eopt) ->  
        check_vardecl member_decl.annot t;
        let enode = 
          match eopt with 
            | None -> None
            | Some(e) -> 
                check_globalvar_init e;
                type_of_assignment member_decl.annot t (type_of_expr e) |> ignore;
                Some(make_typed_expr e)
        in
        {node=VarDecl((id,t),enode); annot=t}
        

(* adds binding to the env *)
let make_component_env_interf cloc env binding = 
  match binding with (interface, id, t, loc) -> 
    match t with 
      | TFun(_,ftype) -> 
          { 
            env with functions = 
              try (add_entry id (Some(interface), t, loc) env.functions)
              with DuplicateEntry(m) -> raise (Semantic_error (cloc, "Error: function "^m^" is declared in multiple interfaces"))
          }
      | _ -> 
          { 
            env with variables = 
              try (add_entry id (Some(interface), t, loc) env.variables)
              with DuplicateEntry(m) -> raise (Semantic_error (cloc, "Error: variable "^m^" is declared in multiple interfaces"))
          }


(* given a list of interfaces names, returns a list of with their memberdecls info *)
let get_bindings env interfaces = 
  let rec get_bindings_rec env interfaces sol = 
    match interfaces with 
    | [] -> sol
    | h :: l -> 
        let bindings = lookup h env.interfaces in 
        match bindings with
        | None -> get_bindings_rec env l sol
        | Some(info) -> 
            match info with (b, pos)-> get_bindings_rec env l (sol @ b)
  in
  get_bindings_rec env interfaces []


(* given a memberdecl, it checks if it is implemented by a component *)
let rec is_implemented loc def binding = match binding with (interf, binid, bintyp, binloc) ->
  match def with 
  | [] ->  raise (Semantic_error (loc, "Error: " ^ interf ^ "." ^ binid ^ " is not implemented in this component" ))
  | h :: l -> match h.node with
      | FunDecl({rtype=ft;fname=name;formals=params;body=b}) -> (
          match bintyp with 
            | TFun(binparams, binrt) -> 
                if name<>binid || binrt<>ft then is_implemented loc l binding
                else let fparams = list_of_second params in 
                if List.length binparams <> List.length fparams then is_implemented loc l binding
                else List.iter2 (fun a b -> if a<>b then raise (Semantic_error (loc, "Error: " ^ interf ^ "." ^ binid ^ " is not implemented in this component" ))) binparams fparams
            | _ -> is_implemented loc l binding)
      | VarDecl((id,t),_)-> 
            if id=binid && t=bintyp then ()
            else is_implemented loc l binding

  
(*  Adds the declaration in defnode to the current environment. Used to allow mutual recursion inside a component *)
let make_component_env_def compname env defnode = match defnode with {node=def; annot=loc} -> match def with 
  | FunDecl({rtype=ft;fname=name;formals=param;body=b}) ->  (
      try{env with functions = add_entry name (None, TFun((list_of_second param), ft), loc) env.functions}
      with DuplicateEntry(m) -> raise (Semantic_error (loc, "Error: function "^m^" is already declared in this scope" )))
  | VarDecl((id,t),_)-> 
        try {env with variables = add_entry id (Some(compname), t,loc) env.variables}
        with DuplicateEntry(m) -> raise (Semantic_error (loc, "Error: variable "^m^" is already declared in this scope" ))


(* This is the main driver function for semantically checking a component and converting it into a typed node *)
let check_component component = match component with {node=comp; annot=loc} ->
  match comp with ComponentDecl{cname=name; uses=uses; provides=iprovides; definitions=def} ->

    let env = !globalenv.env in
    (* check if Prelude is provided or if App is used *)
    if List.mem "Prelude" iprovides then raise (Semantic_error (loc, "Error: Prelude interface cannot be provided"))
    else if List.mem "App" uses then raise (Semantic_error (loc, "Error: App interface cannot be used"))
    (* add Prelude to used interfaces *)
    else let iuses = if List.mem "Prelude" uses then uses else uses @ ["Prelude"] in
    (* checking possible duplicates in the interfaces lists *)
    if has_duplicates iprovides then raise (Semantic_error (loc, "Error: duplicated entry in provided interfaces"))
    else if has_duplicates iuses then raise (Semantic_error (loc, "Error: duplicated entry in used interfaces"))
    else if has_duplicates (iuses @ iprovides) then raise (Semantic_error (loc, "Error: an interface cannot be provided and used at the same time"))
    (* checking that the used/provided interfaces are in this scope *)
    else List.iter (is_interface env loc) (iuses @ iprovides); 

    (* setting up the environment for the component *) 
    let ctable = try add_entry name (uses, iprovides, loc) env.components
                 with DuplicateEntry(m) -> raise (Semantic_error (loc, "Error: component "^m^" is already declared"))
    in 
    let env_ctable = 
      {
        env with
          components = ctable;
          functions = begin_block env.functions;
          variables = begin_block env.variables
      }
    (* adding to the environment the bindings provided by the interfaces used by the component *)
    in 
    let uses_bin = get_bindings env iuses in
    let env_interf = List.fold_left (make_component_env_interf loc) env_ctable uses_bin in
    (* add component's functions for mutual recursion *)
    let env_def = List.fold_left (make_component_env_def name) env_interf def in
    !globalenv.env <- env_def;
    (* check the component's memberdecls *)
    let typed_memberdecl_l = List.map check_memberdecl def; in
    (* check that provided interfaces are implemented *)
    let provides_bin = get_bindings env iprovides in
    List.iter (is_implemented loc def) provides_bin;
    let newglobaltable = {env with components = ctable} in
    !globalenv.env <- newglobaltable;
    let typed_node = ComponentDecl{cname=name; uses=uses; provides=iprovides; definitions=typed_memberdecl_l} in
    {node=typed_node; annot=TComponent(name)}


(* This is the main driver function for semantycally checking an interface and converting it into a typed node *)
let check_interface interface = match interface with {node=interf; annot=loc} ->
  let env = !globalenv.env in 
  match interf with InterfaceDecl{iname=name; declarations=member_decls; _} -> 
    let environment =
      {
        env with
          functions = begin_block env.functions;
          variables = begin_block env.variables;
      }
    in 
    (* checks that the memberdecls are well formed and forms a list of the interface bindings *)
    let ibind = List.map (get_interface_memberdecl_bindings name) member_decls in 
    (* checks for duplicates inside the interface *)
    List.fold_left add_memberdecl_to_env environment member_decls |> ignore;
    (* updates global symbol table *)
    (
      try let newglobaltable = {env with interfaces = add_entry name (ibind, loc) env.interfaces} in !globalenv.env <- newglobaltable
      with DuplicateEntry(m) -> raise (Semantic_error (loc, "Error: interface "^m^" is already declared"))
    );
    (* generate the typed interface node *)
    let typed_memberdecl_l = List.map check_memberdecl member_decls in 
    let typed_node = InterfaceDecl{iname=name; declarations=typed_memberdecl_l; extends=[]} in {node=typed_node; annot=TInterface(name)}



    
(* each interface is filled with the members of the interfaces it extends *)
let solve_interfaces_inheritance interfaces = 
  let pos = Location.dummy_code_pos in 

  let get_nodes_elist interface = 
    match interface.node with 
      InterfaceDecl{iname=name; declarations=member_decls; extends=elist} -> (elist,name) 
  in 
  let set_edges ht (elist,node) = Hashtbl.add ht node elist
  in

  (* use a DFS to detect cycles *)
  let has_cycle nodes edges = 
    let rec rec_has_cycle visited nodes = 
      match nodes with 
      | [] -> () 
      | node::rl -> 
          if (Hashtbl.mem edges node)=false then raise (Semantic_error (pos, "Error: extended interface "^node^" is not declared"))
          else let status = Hashtbl.find visited node in 
          if status = 2 then ()
          else if status = 1 then raise (Semantic_error (pos, "Error: there exists a cycle among inheritance relations")) 
          else Hashtbl.add visited node 1;
          let neighbours = Hashtbl.find edges node in 
          rec_has_cycle visited neighbours;
          Hashtbl.add visited node 2;
          rec_has_cycle visited rl
    in
    let visited = Hashtbl.create 10 in
    (* tag each node with its DFS status: 0=white, 1=grey, 2=black *)
    let initialize_visited ht node = Hashtbl.add ht node 0 in 
    List.iter (initialize_visited visited) nodes;
    rec_has_cycle visited nodes
  in

  (* setting up the graph *)
  let nodes_elist = List.map get_nodes_elist interfaces in 
  let edges = Hashtbl.create 10 in 
  List.iter (set_edges edges) nodes_elist;
  let nodes = list_of_second nodes_elist in 
  (* checking if there is a cycle *)
  has_cycle nodes edges;

  (* adding inherited members to interfaces *)
  let add_interface_members ht interface = 
    match interface.node with InterfaceDecl{iname=name; declarations=member_decls; extends=elist} -> Hashtbl.add ht name member_decls 
  in 
  let interfaces_members = Hashtbl.create 10 in
  List.iter (add_interface_members interfaces_members) interfaces;
  
  let rec inherited_members ht parents = match parents with 
    | [] -> []
    | inter::rl -> 
        let grandparents = Hashtbl.find edges inter in 
        (Hashtbl.find ht inter) @ (inherited_members ht grandparents) @ (inherited_members ht rl) 
  in
  let make_interface ht interface = 
    match interface.node with InterfaceDecl{iname=name; declarations=member_decls; extends=elist} ->
      let members = member_decls @ (inherited_members ht elist) in 
      let newnode = InterfaceDecl{iname=name; declarations=members; extends=elist}  in 
      {interface with node=newnode}

  in List.map (make_interface interfaces_members) interfaces




(* main function starting the type checking and returning a typed AST *)
let type_check (CompilationUnit{interfaces=interf; components=comp; connections=conn}) = 
  let interf = solve_interfaces_inheritance interf in 
  let typed_interfaces = List.map check_interface interf in 
  let typed_components = List.map check_component comp
  in CompilationUnit{interfaces=typed_interfaces; components=typed_components ; connections=conn}
