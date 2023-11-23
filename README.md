# µcomp-lang
This repository contains a compiler for µcomp-lang, a toy component-based imperative language.

The `report.pdf` file contains the design choices made during development and their motivations.

## Syntax 
```
interface Adder {
  def add(a : int, b : int) : int;
}

component CAdder provides Adder { 
  def add(a : int, b : int) : int {
    var c : int;
    c = a + b;
    return c;
  }
}

component Entry provides App uses Adder {
  def main() : int {
    var d : int;
    d = add(52, 10);
    print(d);
    return 0;
  }
}  

connect Entry.Adder <- CAdder.Adder
```

## Source code

The `lib/` directory contains the modules for each phase of the compiler. 

More precisely, the `lib/` directory provides:

    ast.ml                       <-- Definition of the abstract syntax tree of µcomp-lang 
    location.ml                  <-- The module Location provides two data types to represent code locations
    location.mli                 <-- The interface of the module Location   
    parser.mly                   <-- Menhir specification of the grammar
    parsing.ml                   <-- The module Parsing implements the parser of µcomp-lang
    parsing.mli                  <-- The interface of the module Parsing  
    scanner.mll                  <-- ocamllex specification of the scanner 
    scanner.mli                  <-- The interface of the module Scanner
    symbol_table.ml              <-- The module Symbol_table provides the implementation of a symbol table
    symbol_table.mli             <-- The interface of the module Symbol_table
    semantic_analysis.ml         <-- The module Semantic_analysis implements the semantic checker of µcomp-lang
    semantic_analysis.mli        <-- The interface of the module Semantic_analysis
    linker.ml                    <-- The module Linker implements the linking phase of µcomp-lang
    linker.mli                   <-- The interface of the module Linker
    codegen.ml                   <-- The module Codegen translates a µcomp-lang into a LLVM module
    codegen.mli                  <-- The interface of the module Codegen
    optimizer.ml                 <-- The module Optimizer runs a sequence of optimization on a LLVM module
    optimizer.mli                <-- The interface of the module Optimizer 

The `bin/` directory provide:

    mcompc.ml                    <-- The code of the compiler executable
    mcompc.mli                   <-- A dummy interface
    rt-support.c                 <-- A simple implementation of the functions provided by `Prelude`
