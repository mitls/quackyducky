(*
   Copyright 2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Binding
open FStar.All
open Ast

val global_env : Type0

val env : Type0
val mk_env (g:global_env) : ML env
val global_env_of_env (e:env) : ML global_env

val resolve_typedef_abbrev (_:env) (_:ident): ML ident
val lookup_expr_name (_:env) (_:ident) : ML typ
val lookup_macro_definition (_:env) (_:ident) : ML (option expr)
val has_reader (_:global_env) (_:ident) : ML bool
val parser_kind_nz (env:global_env) (id:ident) : ML (option bool)
val parser_weak_kind  (env:global_env) (id:ident) : ML (option weak_kind)
val size_of_integral_typ (_:env) (_:typ) (_:range) : ML int
val bind_decls (g:global_env) (p:list decl) : ML (list decl & global_env)
//val add_field_error_code_decls (ge: env) : ML (list decl)

val initial_global_env (_:unit) : ML global_env
val get_exported_decls (ge:global_env) (mname:string) : ML (list ident' & list ident')  //exported, private
val finish_module (ge:global_env) (mname:string) (e_and_p:list ident' & list ident')
  : ML global_env
