exception LinkingError of string

open Ast
open Symbol_table



(* each component is mapped to a tuple (used interfaces, provided interfaces) *)
let build_env components = 
  let get_entry comp = 
    match comp.node with ComponentDecl{cname=name; uses=uses; provides=provides; definitions=def} ->
     (name, (uses,provides)) 
  in 
  let entries = List.map get_entry components in 
  of_alist entries


(* create a symbol table where each interface is mapped to the component providing it *)
let create_provides_table connections = 
  let get_entry connection = 
    match connection with Link(cuses, iuses, cprov, iprov) -> 
      (iuses,cprov) 
  in 
  let get_stdlib_entries = [("App", "App")] @ [("Prelude","Prelude")] in 
  let entries = get_stdlib_entries @ (List.map get_entry connections) in 
  of_alist entries


(* checks if a list has duplicates *)
let rec has_duplicates list = match list with
  | [] -> false 
  | h :: l -> if List.mem h l then true else has_duplicates l


(* Checks that the App interface is provided only once *)         
let check_app comps = 
  let rec check_app_rec components isfound = 
    match components with 
    | [] -> isfound
    | h :: l -> 
        match h.node with ComponentDecl{cname=name; uses=iuses; provides=iprovides; definitions=def} ->
          let isprovided = List.mem "App" iprovides 
          in
          if isprovided=false then check_app_rec l isfound
          else if isfound then raise (LinkingError "App interface must be provided only once")
          else check_app_rec l true
  
  in 
  let b = check_app_rec comps false in 
  if b = false then raise (LinkingError "App interface must be provided")
  else ()


(* Checks that a connection is well-formed *)
let rec check_connection env conn = 
  match conn with Link(cuses, iuses, cprov, iprov) -> 
    (* the provided/used interface must be the same *)
    if iuses <> iprov then raise (LinkingError ("connencting different interfaces ("^iuses^" and "^iprov^")"))
    else
    (* Prelude cannot be provided or used *)
    if ("Prelude"=iuses || "Prelude"=iprov) then raise (LinkingError "Prelude cannot be defined in a connection")
    else
    (* check that iprov is in the provided interfaces list of cprov *)
    let cprovenv =  lookup cprov env in 
    (match cprovenv with 
      | None -> raise (LinkingError ("component "^cprov^ " is not defined in this scope"))
      | Some((envuses,envprovides)) -> 
          if (List.mem iprov envprovides)=false then raise (LinkingError ("component "^cprov^ " does not provide "^iprov))
          else ());
    (* check that iuses is in the used interfaces list of cuses *)
    let cusesenv = lookup cuses env in 
    (match cusesenv with
      | None -> raise (LinkingError ("component "^cuses^ " is not defined in this scope"))
      | Some((envuses,envprovides)) ->
        if (List.mem iuses envuses)=false then raise (LinkingError ("component "^cuses^ " does not use "^iuses))
        else ())


let check_component_uses conn_uses component = 
  match component.node with  ComponentDecl{cname=name; uses=uses; provides=iprovides; definitions=def} ->
    List.iter (fun usesi -> 
                if (List.mem (name,usesi) conn_uses)=false then raise (LinkingError ("component "^name^ " uses "^usesi^ " but no connection is provided"))
                else ()
    ) uses

(* main function to check that connections are well-formed *)
let check_connections env components connections = 
  (* check that connections contain interfaces/components that are defined *)
  List.iter (check_connection env) connections;
  (* check that there are no duplicates in links *)
  let firsttwo = List.map (fun l -> match l with Link(a,b,_,_) -> (a,b)) connections in 
  let secondtwo = List.map (fun l -> match l with Link(_,_,c,d) -> (c,d)) connections in 
  if has_duplicates firsttwo || has_duplicates secondtwo then raise (LinkingError ("duplicate in connection list"));
  (* check that, if component c uses interface i, then there exists a Link(_,_,c,i) *)
  List.iter (check_component_uses firsttwo) components



(* The interface associated with external names is changed with the component implementing such interface  *)
let wire_component env component = 

  let rec wire_exp e = 
    match e.node with
      | LV(lval) -> let tnode = LV(wire_lval lval) in {node=tnode; annot = e.annot}
      | Assign(atype, lval, expr) -> let tnode = Assign(atype, wire_lval lval, wire_exp expr) in {node=tnode; annot = e.annot}
      | ILiteral(_) -> e
      | CLiteral(_) -> e
      | BLiteral(_) -> e
      | Increment(inctype, lval, k) ->
        (
          match inctype with
          | Pre -> let tnode = Increment(Pre, wire_lval lval, k) in {node=tnode; annot = e.annot}
          | Post -> let tnode = Increment(Post, wire_lval lval, k) in {node=tnode; annot = e.annot}
        ) 
      | UnaryOp(uop, expr) -> let tnode = UnaryOp(uop, wire_exp expr) in {node=tnode; annot = e.annot}
      | Address(lval) -> let tnode = Address(wire_lval lval) in {node=tnode; annot = e.annot}
      | BinaryOp(bop, expr1, expr2) -> let tnode = BinaryOp(bop, wire_exp expr1, wire_exp expr2) in {node=tnode; annot = e.annot}
      | Call(iopt, id, exprlist) -> 
          match iopt with
            | None ->
              (
                match component.node with ComponentDecl{cname=name; uses=_; provides=_; definitions=_} ->
                let tnode = Call(Some(name), id, List.map wire_exp exprlist) in {node=tnode; annot = e.annot}
              ) 
            | Some(interface) -> 
                let comp = Option.get (lookup interface env) in 
                let tnode = Call(Some(comp), id, List.map wire_exp exprlist) in 
                {node=tnode; annot = e.annot}
  and wire_lval lval = 
    match lval.node with
      | AccVar(iopt, id) -> (
          match iopt with
            | None -> lval
            | Some(interface) -> 
                let comp_opt =  lookup interface env in 
                let comp = (match comp_opt with None -> interface | Some(cp) -> cp) in
                let tnode = AccVar(Some(comp),id) in 
                {node=tnode; annot = lval.annot})
      | AccIndex(lvalue, expr) -> let tnode = AccIndex(wire_lval lvalue, wire_exp expr) in {node=tnode; annot = lval.annot}

  in 
  let rec wire_statement stmt = 
    match stmt.node with
      | If(e1, s1, s2) -> let tnode = If(wire_exp e1, wire_statement s1, wire_statement s2) in {node=tnode; annot = stmt.annot}
      | While(e1, s1) -> let tnode = While(wire_exp e1, wire_statement s1) in {node=tnode; annot=stmt.annot}
      | Expr(e) -> let tnode = Expr(wire_exp e) in {node=tnode; annot=stmt.annot}
      | Return(eopt) -> (match eopt with
          | None -> stmt
          | Some(e) -> let tnode = Return(Some(wire_exp e)) in {node=tnode; annot=stmt.annot})
      | Block(stmtordecl) -> let tnode = Block(List.map wire_stmtordec stmtordecl) in {node=tnode; annot=stmt.annot}
      | Skip -> stmt
    and wire_stmtordec stmtordecl = 
      match stmtordecl.node with
        | LocalDecl(_) -> stmtordecl
        | Stmt(s) -> let tnode = Stmt(wire_statement s) in {node=tnode; annot=stmtordecl.annot}

  in 
  let wire_definition def = 
    match def.node with
      | VarDecl(_) -> def
      | FunDecl(f) -> match f.body with
          | None -> def
          | Some(bd) -> 
             let wired_function = FunDecl({rtype=f.rtype; fname=f.fname; formals=f.formals; body=Some(wire_statement bd)}) in 
             {node=wired_function; annot=def.annot}

  in 
  match component.node with ComponentDecl{cname=name; uses=uses; provides=iprovides; definitions=def} ->
    let wired_definitions = List.map wire_definition def in 
    let tcomp = ComponentDecl{cname=name; uses=uses; provides=iprovides; definitions=wired_definitions} in 
    {node=tcomp; annot=component.annot}



let wire_components (CompilationUnit{interfaces=interf; components=comp; connections=conn}) =
  let env = build_env comp in 
  check_connections env comp conn;
  let providestable = create_provides_table conn in 
  let wired_components = List.map (wire_component providestable) comp in 
  check_app comp;
  CompilationUnit{interfaces=interf; components=wired_components; connections=conn}