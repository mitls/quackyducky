open Ast
let prog_to_json (p:prog)
  : string
  = let yj = Ast.prog_to_yojson p in
    Yojson.Safe.to_string yj
