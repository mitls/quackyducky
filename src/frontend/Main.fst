module Main
open FStar.All
open Ast
open ParserDriver

let test =
  let cmdline = FStar.Getopt.cmdline() in
  match cmdline with
  | [_; fn] ->
    let decls = ParserDriver.parse fn in
    let decls = Binding.bind_prog decls in
    FStar.IO.print_string (String.concat "\n" (List.map Ast.print_decl decls))
  | _ ->
    failwith "Not enough arguments"
