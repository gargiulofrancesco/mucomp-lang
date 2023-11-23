open Ast
open Symbol_table

module L = Llvm


type env = {
  functions : L.llvalue Symbol_table.t; 
  variables : L.llvalue Symbol_table.t; 
}


let empty_env = {functions=begin_block empty_table; variables=begin_block empty_table}


let name_mangling comp name = "_" ^ comp ^ "_" ^ name


(* The LLVM global context *)
let context = L.global_context ()


(* LLVM IR types *)
let int_type = L.i32_type context
let bool_type = L.i1_type context
let char_type = L.i8_type context
let void_type = L.void_type context


(* translates a mcomp-lang typ to its corresponding LLVM type *)
let rec ltype_of_typ t = match t with
  | TInt -> int_type
  | TBool -> bool_type
  | TChar -> char_type
  | TArray(tp, iopt) -> (
      let atype = ltype_of_typ tp in 
        match iopt with
          | None -> L.pointer_type atype
          | Some(size) -> L.array_type atype (Int32.to_int size))
  | TRef(tp) -> let rtype = ltype_of_typ tp in L.pointer_type rtype
  | TVoid -> void_type
  | TFun(formals, rtyp) -> 
      let rtype = ltype_of_typ rtyp in
      let formalstype = Array.of_list(List.map ltype_of_typ formals) in
      L.function_type rtype formalstype
  | _ -> failwith "Error: this should not happen"


(* generates the initialization llvalue of each typ *)
let rec initial_typ_value typ = 
  match typ with
    | TInt -> L.const_int int_type 0
    | TBool -> L.const_int bool_type 0
    | TChar -> L.const_int char_type 0
    | TArray(tp,size) -> 
        let ltype = ltype_of_typ tp in
        let ival = initial_typ_value tp in
        let n = Int32.to_int (Option.get size) in
        L.const_array ltype (Array.make n ival)
    | TRef(tp) -> L.const_pointer_null (ltype_of_typ typ)
    | _ -> failwith "Error: this should not happen"


(* if a block doesn't already have a terminator, then add it. Otherwise do nothing *)
let add_terminator builder b = 
  match L.block_terminator (L.insertion_block builder) with 
    | Some(_) -> ()
    | None -> b builder |> ignore  


let rec build_expr env func builder e =
  match e.node with 
    | LV(lval) -> 
        let lvalptr = build_lvalue env func builder lval in 
        (
          match (lval.node, lval.annot) with 
            | (AccVar(_,_), TArray(_,Some(_))) -> L.build_in_bounds_gep lvalptr ([| (L.const_int int_type 0) ; (L.const_int int_type 0) |] ) "" builder
            | (_,_) -> 
                (
                  let lvalload = L.build_load lvalptr "" builder in (
                  match lval.annot with 
                    | TArray(TRef(_), _) 
                    | TRef(_) -> L.build_load lvalload "" builder (* automatical dereferencing *)
                    | _ -> lvalload)
                )
        )
    | Assign(atype, lval, e1) -> 
        let exprval = build_expr env func builder e1 in 
        let lvalaccess =
          match(lval.annot, e1.node) with 
            | (TArray(TRef(_), _), Address(_)) -> 
                build_lvalue env func builder lval 
            | (TArray(TRef(_),_),_) -> 
                let lvalptr = build_lvalue env func builder lval in 
                L.build_load lvalptr "" builder  
            | (TRef(_), Address(_)) -> (* "ref = address" assignment *) 
                build_lvalue env func builder lval
            | (TRef(_), _) -> (* "ref=value" assignment *)
                let lvalptr = build_lvalue env func builder lval in 
                L.build_load lvalptr "" builder 
            | (_,_) -> (* normal assignment *) 
                build_lvalue env func builder lval
        in 
        let lvalvalue = L.build_load lvalaccess "" builder in
        let result = 
          match atype with 
            | Eq -> exprval
            | Plus -> L.build_add lvalvalue exprval "" builder
            | Minus -> L.build_sub lvalvalue exprval "" builder
            | Times -> L.build_mul lvalvalue exprval "" builder
            | Div -> L.build_sdiv lvalvalue exprval "" builder
            | Mod -> L.build_srem lvalvalue exprval "" builder
        in
        L.build_store result lvalaccess builder |> ignore;
        result
      
    | Increment(inctype, lval, k) -> 
        let constant = L.const_int int_type (Int32.to_int k) in 
        let lvalptr = build_lvalue env func builder lval in 
        let lvalptr = 
        match lval.annot with 
            | TArray(TRef(_),_)
            | TRef(_) -> L.build_load lvalptr "" builder
            | _ -> lvalptr
        in
        let oldvalue = L.build_load lvalptr "" builder in 
        let newvalue = L.build_add oldvalue constant "" builder in 
        L.build_store newvalue lvalptr builder |> ignore;
        (
          match inctype with
            | Pre -> newvalue
            | Post -> oldvalue
        )
    | ILiteral(n) -> L.const_int int_type (Int32.to_int n)
    | CLiteral(c) -> L.const_int char_type (Char.code c)
    | BLiteral(b) -> L.const_int bool_type (Bool.to_int b)
    | UnaryOp(uop, e1) -> 
      (
        match uop with 
          | Neg -> let exprval = build_expr env func builder e1 in L.build_neg exprval "" builder
          | Not -> let exprval = build_expr env func builder e1 in L.build_not exprval "" builder
      )
    | Address(lval) -> build_lvalue env func builder lval 
    | BinaryOp(binop, e1, e2) ->
      (  
        match binop with 
          | And
          | Or ->
              (* Short-circuit Evaluation *)
              (* create new blocks and the corresponding builders *)
              let left_block = L.append_block context "SC.l" func in 
              let right_block = L.append_block context "SC.r" func in 
              let merge_block =  L.append_block context "SC.merge" func in 
              let left_builder = L.builder_at_end context left_block in 
              let right_builder = L.builder_at_end context right_block in 
              let merge_builder = L.builder_at_end context merge_block in 
              (* jump from the current block to the left evaluation block *)
              add_terminator builder (L.build_br left_block);
              (* evaluate left expression *)
              let e1_eval = build_expr env func left_builder e1 in
              (* build the conditional jump to the right-expression evaluation block *)
              let jump_instruction = 
                match binop with 
                  | And -> L.build_cond_br e1_eval right_block merge_block
                  | Or -> L.build_cond_br e1_eval merge_block right_block
                  | _ -> failwith "Error: this should not happen"
              in
              add_terminator left_builder jump_instruction;
              (* evaluate right expression *)
              let e2_eval = build_expr env func right_builder e2 in
              add_terminator right_builder (L.build_br merge_block);
              (* get the actual result *)
              let left_phi_block = L.insertion_block left_builder in
              let right_phi_block = L.insertion_block right_builder in
              let phi = L.build_phi ([(e1_eval, left_phi_block); (e2_eval, right_phi_block)]) "" merge_builder in
              L.position_at_end merge_block builder; 
              phi
          | _ -> 
              let expr1val = build_expr env func builder e1 in
              let expr2val = build_expr env func builder e2 in
              match binop with 
                | Add -> L.build_add expr1val expr2val "" builder
                | Sub -> L.build_sub expr1val expr2val "" builder
                | Mult -> L.build_mul expr1val expr2val "" builder
                | Div -> L.build_sdiv expr1val expr2val "" builder
                | Mod -> L.build_srem expr1val expr2val "" builder
                | Equal -> L.build_icmp L.Icmp.Eq expr1val expr2val "" builder
                | Neq -> L.build_icmp L.Icmp.Ne expr1val expr2val "" builder
                | Less -> L.build_icmp L.Icmp.Slt expr1val expr2val "" builder
                | Leq -> L.build_icmp L.Icmp.Sle expr1val expr2val "" builder
                | Greater -> L.build_icmp L.Icmp.Sgt expr1val expr2val "" builder
                | Geq -> L.build_icmp L.Icmp.Sge expr1val expr2val "" builder
                | _ -> failwith "Error: this should not happen"
      )
    | Call(comp, tid, formals) -> 
        let id = if tid="main" then tid else name_mangling (Option.get comp) tid in 
        let funval = Option.get (lookup id env.functions) in
        let paramsval = List.map (build_expr env func builder) formals in  
        L.build_call funval (Array.of_list paramsval) "" builder


and build_lvalue env func builder lval = 
  match lval.node with
  | AccVar(comp,id) ->(
      let id = (match comp with None -> id | Some(compp) -> name_mangling compp id ) in 
      Option.get (lookup id env.variables) )
  | AccIndex(lv, e) -> 
      match lv.annot with 
        | TArray(_,None) -> 
            let index = build_expr env func builder e in 
            let arrptr = build_lvalue env func builder lv in 
            let arr =  L.build_load arrptr "" builder in 
            L.build_in_bounds_gep arr ([| index |] ) "" builder 
        | TArray(_, Some(_)) -> 
            let index = build_expr env func builder e in 
            let arr = build_lvalue env func builder lv in
            L.build_in_bounds_gep arr ([| (L.const_int int_type 0) ; index |] ) "" builder 
        | _ -> failwith "Error: this should not happen"
      



let rec codegen_stmt func env builder stmt = 

  match stmt.node with 
    | If(e,s1,s2) -> 
        (* generate the "then", "else", and "merge" blocks *)
        let then_block = L.append_block context "If.then" func in 
        let else_block = L.append_block context "If.else" func in 
        let merge_block = L.append_block context "If.merge" func in         
        (* fill the "then" and "else" blocks with instructions *)
        let then_builder = L.builder_at_end context then_block in 
        let else_builder = L.builder_at_end context else_block in 
        codegen_stmt func env then_builder s1;
        codegen_stmt func env else_builder s2;
        (* generate an unconditional jump from "then" and "else" to "merge" *)
        add_terminator then_builder (L.build_br merge_block);
        add_terminator else_builder (L.build_br merge_block);
        (* generate the conditional branch *)
        let guard = build_expr env func builder e in 
        add_terminator builder (L.build_cond_br guard then_block else_block);
        (* move the builder at the end of the "merge" block *)
        L.position_at_end merge_block builder
    | While(e,s) ->
        (* generate the "condition", "loop", and "continuation" blocks *)
        let condition_block = L.append_block context "While.condition" func in 
        let loop_block = L.append_block context "While.loop" func in 
        let continuation_block = L.append_block context "While.continuation" func in 
        (* generate an unconditional jump to the "condition" block *)
        add_terminator builder (L.build_br condition_block);
        (* fill the "condition" block *)
        let condition_builder =  L.builder_at_end context condition_block in 
        let guard = build_expr env func condition_builder e in 
        add_terminator condition_builder (L.build_cond_br guard loop_block continuation_block);
        (* fill the "loop" body *)
        let loop_builder = L.builder_at_end context loop_block in 
        let benv = {env with variables = begin_block env.variables} in
        codegen_stmt func benv loop_builder s;
        add_terminator loop_builder (L.build_br condition_block);
        (* move the builder at the end of the "continuation" block *)
        L.position_at_end continuation_block builder
    | Expr(e) -> build_expr env func builder e |> ignore
    | Return(eopt) -> (match eopt with
                        | None -> L.build_ret_void builder |>ignore
                        | Some(e) -> L.build_ret (build_expr env func builder e) builder |> ignore )
      
    | Block(bl) -> let benv = {env with variables = begin_block env.variables} in 
                   List.iter (codegen_stmtordec func benv builder) bl
    | Skip -> ()
  
and codegen_stmtordec func env builder stmtordec = 
  match stmtordec.node with 
    | Stmt(s) -> codegen_stmt func env builder s
    | LocalDecl((id,typ),eopt) -> 
        let local = L.build_alloca (ltype_of_typ typ) id builder in 
        add_entry id local env.variables |> ignore;
        match eopt with 
          | None -> ()
          | Some(e) ->
              let lval = {node=AccVar(None, id); annot=typ} in
              let assign = {node=Assign(Eq, lval, e); annot=typ} in
              build_expr env func builder assign |> ignore


let codegen_function_bodies lmodule env comp =
  (* allocates memory for a single function parameter and stores it *)
  let codegen_function_parameter env builder (id, typ) param = 
    let local = L.build_alloca (ltype_of_typ typ) id builder in 
    L.build_store param local builder |> ignore;
    add_entry id local env.variables |> ignore
  in
  let codegen_function_bodies_def def =
    match def.node with 
      | VarDecl(_) -> ()
      | FunDecl({rtype=ft;fname=fname;formals=params;body=b}) -> 
          match comp.node with ComponentDecl{cname=cname; uses=_; provides=_; definitions=_} ->
            let fenv = {env with variables = begin_block env.variables} in
            let fname = if fname="main" then fname else name_mangling cname fname in 
            let funp = Option.get (lookup fname env.functions) in 
            let builder = L.builder_at_end context (L.entry_block funp) in 
            (* allocating function parameters *)
            List.iter2 (codegen_function_parameter fenv builder) params (Array.to_list (L.params funp)); 
            (* building function body *)
            let benv = {fenv with variables = begin_block fenv.variables} in 
            codegen_stmt funp benv builder (Option.get b);
            (* adding a return at the end of the block if it doesn't exist *)
            let tempret = 
              (
                match ft with 
                  | TVoid -> L.build_ret_void
                  | tp -> L.build_ret (initial_typ_value tp)
              )
            in add_terminator builder tempret
  in
  match comp.node with ComponentDecl{cname=name; uses=uses; provides=iprovides; definitions=def} ->
    List.iter codegen_function_bodies_def def



(* declaring function prototypes of a component to allow mutual recursion *)
let codegen_function_prototypes lmodule env comp = 
  let codegen_function_prototypes_def def = 
    match def.node with
      | VarDecl(_) -> ()
      | FunDecl({rtype=ft;fname=fname;formals=params;body=b}) -> 
          match comp.node with ComponentDecl{cname=cname; uses=_; provides=_; definitions=_} ->
            let fname = if fname="main" then fname else name_mangling cname fname in 
            let ltype = ltype_of_typ def.annot in
            let proto = L.define_function fname ltype lmodule in 
            add_entry fname proto env.functions |> ignore

  in
  match comp.node with ComponentDecl{cname=name; uses=uses; provides=iprovides; definitions=def} ->
    List.iter codegen_function_prototypes_def def


(* declares stdlib function prototypes *)
let codegen_stdlib_prototypes lmodule env =
    let getint_name =  name_mangling "Prelude" "getint" in
    let getint_ltype = ltype_of_typ (TFun([],TInt)) in 
    let getint_proto = L.declare_function getint_name getint_ltype lmodule in 
    add_entry getint_name getint_proto env.functions |> ignore;
    let print_name = name_mangling "Prelude" "print" in 
    let print_ltype = ltype_of_typ (TFun([TInt], TVoid)) in
    let print_proto = L.declare_function print_name print_ltype lmodule in 
    add_entry print_name print_proto env.functions |> ignore

(* defines components global variables as global variables using name mangling *)
let codegen_global_variables lmodule env comp = 
  let rec globalvar_initialization e = 
    match e.node with 
      | ILiteral(n) -> L.const_int int_type (Int32.to_int n)
      | CLiteral(c) -> L.const_int char_type (Char.code c)
      | BLiteral(b) -> L.const_int bool_type (Bool.to_int b)
      | UnaryOp(uop,e1) -> 
        (
          match uop with 
            | Neg -> L.const_neg (globalvar_initialization e1)
            | Not -> L.const_not (globalvar_initialization e1)
        )
      | BinaryOp(binop, e1, e2) ->
        (
          let e1const = globalvar_initialization e1 in 
          let e2const = globalvar_initialization e2 in 
          match binop with 
            | Add -> L.const_add e1const e2const
            | Sub -> L.const_sub e1const e2const
            | Mult -> L.const_mul e1const e2const
            | Div -> L.const_sdiv e1const e2const
            | Mod -> L.const_srem e1const e2const
            | Equal -> L.const_icmp L.Icmp.Eq e1const e2const
            | Neq -> L.const_icmp L.Icmp.Ne e1const e2const
            | Less -> L.const_icmp L.Icmp.Sle e1const e2const
            | Leq -> L.const_icmp L.Icmp.Sle e1const e2const
            | Greater -> L.const_icmp L.Icmp.Sgt e1const e2const
            | Geq -> L.const_icmp L.Icmp.Sge e1const e2const
            | And -> L.const_and e1const e2const
            | Or -> L.const_or e1const e2const
        )
      | _ -> failwith "Error: this should not happen"
  in
  let codegen_global_variables_def def = 
    match def.node with
      | FunDecl(_) -> ()
      | VarDecl((id,t),eopt) -> 
          match comp.node with ComponentDecl{cname=name; uses=_; provides=_; definitions=_} ->
            let id = name_mangling name id in
            let init = match eopt with
              | None -> initial_typ_value t
              | Some(e) -> globalvar_initialization e
            in
            let gvar = L.define_global id init lmodule in
            add_entry id gvar env.variables |> ignore
  in
  match comp.node with ComponentDecl{cname=name; uses=uses; provides=iprovides; definitions=def} ->
    List.iter codegen_global_variables_def def
    



let to_llvm_module (CompilationUnit{interfaces=interf; components=comp; connections=conn}) = 
  let lmodule = L.create_module context "mcomp-module" in
  let env = empty_env in
  (* add components global variables *)
  List.iter (codegen_global_variables lmodule env) comp;
  (* add prelude external function prototypes *)
  codegen_stdlib_prototypes lmodule env;
  (* add components function prototypes *)
  List.iter (codegen_function_prototypes lmodule env) comp;
  (* add function bodies *)
  List.iter (codegen_function_bodies lmodule env) comp; 
  lmodule
  

