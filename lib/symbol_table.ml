exception DuplicateEntry of Ast.identifier


type 'a t =
  | Empty
  | Scope of 'a t * (Ast.identifier, 'a) Hashtbl.t (* Scope's parent, symbol table declared in the scope *)


let empty_table = Empty


let begin_block table = Scope(table, Hashtbl.create 0)


let end_block table = match table with
  | Empty -> Empty
  | Scope(parent, _) -> parent


let add_entry symbol info table = match table with
| Empty -> failwith "Error: cannot add a symbol to an empty node"
| Scope(p,htbl) -> 
    if Hashtbl.mem htbl symbol then raise (DuplicateEntry(symbol))
    else Hashtbl.add htbl symbol info;
         Scope(p, htbl)


let of_alist (entries : (Ast.identifier * 'a) list) = 
  let add_entry table (id,entry) = add_entry id entry table
  in let etable = begin_block empty_table 
  in List.fold_left add_entry etable entries


let rec lookup symbol table = match table with
  | Empty -> None
  | Scope(p,htbl) -> 
      if Hashtbl.mem htbl symbol then Some(Hashtbl.find htbl symbol)
      else lookup symbol p
