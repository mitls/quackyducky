(*
   Copyright 2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain as copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module StaticAssertions
open FStar.All
open Ast
module B = Binding

noeq
type sizeof_assertion = {
  type_name : ident;
  size : int
}

noeq
type static_asserts = {
  includes : list string;
  sizeof_assertions : list sizeof_assertion
}

let empty_static_asserts = {
  includes = [];
  sizeof_assertions = []
}

let compute_static_asserts (benv:B.global_env)
                           (senv:TypeSizes.size_env)
                           (r:option type_refinement)
  : ML static_asserts
  = let env = B.mk_env benv, senv in
    match r with
    | None -> empty_static_asserts
    | Some r -> 
      let sizeof_assertions =
        r.type_map
        |> List.map
          (fun (i, jopt) ->
            let j =
              match jopt with
              | None -> i
              | Some j -> j
            in
            let t_j = with_dummy_range (Type_app j []) in
            match TypeSizes.size_of_typ env t_j with
            | TypeSizes.Fixed n
            | TypeSizes.WithVariableSuffix n ->
             { type_name = i;
               size = n }
            | _ -> 
              Ast.error 
                (Printf.sprintf
                  "Type %s is variable sized and cannot refine a C type %s"
                  (ident_to_string j) (ident_to_string i))
                i.range)
      in
      {
        includes = r.Ast.includes;
        sizeof_assertions = sizeof_assertions
      }

let no_static_asserts (sas: static_asserts) : Tot bool =
  Nil? sas.includes &&
  Nil? sas.sizeof_assertions

let has_static_asserts (sas: static_asserts) : Tot bool =
  not (no_static_asserts sas)

let print_static_asserts (sas:static_asserts)
  : ML string
  = let includes =
        sas.includes
        |> List.map (fun i -> Printf.sprintf "#include \"%s\"" i)
        |> String.concat "\n"
    in
    let sizeof_assertions =
        sas.sizeof_assertions
        |> List.map (fun sa -> Printf.sprintf "C_ASSERT(sizeof(%s) == %d);" (ident_to_string sa.type_name) sa.size)
        |> String.concat "\n"
    in
    includes ^ "\n" ^ sizeof_assertions
