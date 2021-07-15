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
module Target
(* The abstract syntax for the code produced by 3d *)
open FStar.All
module A = Ast
open Binding

/// The same as A.op, but with `SizeOf` removed
/// and arithmetic operators resolved to their types
type op =
  | Eq
  | Neq
  | And
  | Or
  | Not
  | Plus of A.integer_type
  | Minus of A.integer_type
  | Mul of A.integer_type
  | Division of A.integer_type
  | Remainder of A.integer_type
  | BitwiseAnd of A.integer_type
  | BitwiseXor of A.integer_type
  | BitwiseOr of A.integer_type
  | BitwiseNot of A.integer_type
  | ShiftRight of A.integer_type
  | ShiftLeft of A.integer_type
  | LT of A.integer_type
  | GT of A.integer_type
  | LE of A.integer_type
  | GE of A.integer_type
  | IfThenElse
  | BitFieldOf of int //BitFieldOf(i, from, to)
  | Cast : from:A.integer_type -> to:A.integer_type -> op
  | Ext of string

/// Same as A.expr, but with `This` removed
///
/// Carrying around the range information from AST.expr so that we
///   can report errors in terms of their 3d file locations

noeq
type expr' =
  | Constant   : c:A.constant -> expr'
  | Identifier : i:A.ident -> expr'
  | App        : hd:op -> args:list expr -> expr'
  | Record     : type_name:A.ident -> list (A.ident * expr) -> expr'

and expr = expr' & A.range

let mk_expr (e:expr') = e, A.dummy_range

type lam a = (option A.ident) & a

noeq
type atomic_action =
  | Action_return of expr
  | Action_abort
  | Action_field_pos
  | Action_field_ptr
  | Action_deref of A.ident
  | Action_assignment : lhs:A.ident -> rhs:expr -> atomic_action
  | Action_call : f:A.ident -> args:list expr -> atomic_action

noeq
type action =
  | Atomic_action of atomic_action
  | Action_seq : hd:atomic_action -> tl:action -> action
  | Action_ite : hd:expr -> then_:action -> else_:action -> action
  | Action_let : i:A.ident -> a:atomic_action -> k:action -> action

(* A subset of F* types that the translation targets *)
noeq
type typ =
  | T_false    : typ
  | T_app      : hd:A.ident -> args:list index -> typ
  | T_dep_pair : dfst:typ -> dsnd:(A.ident & typ) -> typ
  | T_refine   : base:typ -> refinement:lam expr -> typ
  | T_if_else  : e:expr -> t:typ -> f:typ -> typ
  | T_pointer  : typ -> typ
  | T_with_action: typ -> action -> typ
  | T_with_dep_action: typ -> a:lam action -> typ
  | T_with_comment: typ -> A.comments -> typ

(* An index is an F* type or an expression
   -- we reuse Ast expressions for this
*)
and index = either typ expr

let field_typ = typ

type param = A.ident & typ

noeq
type struct_field = {
  sf_dependence: bool;
  sf_ident: A.ident;
  sf_typ: field_typ
}

type field = struct_field

noeq
type typedef_body =
  | TD_abbrev : typ -> typedef_body
  | TD_struct : list field  -> typedef_body

noeq
type typedef_name = {
  td_name:A.ident;
  td_params:list param;
  td_entrypoint:bool
}
type typedef = typedef_name & typedef_body

////////////////////////////////////////////////////////////////////////////////

noeq
type parser_kind' =
  | PK_return
  | PK_impos
  | PK_base     : hd:A.ident -> parser_kind'
  | PK_list     : parser_kind'
  | PK_t_at_most: parser_kind'
  | PK_t_exact  : parser_kind'
  | PK_filter   : k:parser_kind -> parser_kind'
  | PK_and_then : k1:parser_kind -> k2:parser_kind -> parser_kind'
  | PK_glb      : k1:parser_kind -> k2:parser_kind -> parser_kind'
  | PK_string   : parser_kind'

and parser_kind = {
  pk_kind : parser_kind';
  pk_weak_kind : A.weak_kind ;
  pk_nz: bool
}

val expr_eq (e1 e1:expr) : bool
val exprs_eq (es1 es1:list expr) : bool
val fields_eq (fs1 fs2:list (A.ident & expr)) : bool
val parser_kind_eq (k k':parser_kind) : bool

noeq
type parser' =
  | Parse_return    : v:expr -> parser'
  | Parse_app       : hd:A.ident -> args:list index -> parser'
  | Parse_nlist     : n:expr -> t:parser -> parser'
  | Parse_t_at_most : n:expr -> t:parser -> parser'
  | Parse_t_exact   : n:expr -> t:parser -> parser'
  | Parse_pair      : n1: A.ident -> p:parser -> q:parser -> parser'
  | Parse_dep_pair  : n1: A.ident -> p:parser -> k:lam parser -> parser'
  | Parse_dep_pair_with_refinement: n1: A.ident -> dfst:parser -> refinement:lam expr -> dsnd:lam parser -> parser'
  | Parse_dep_pair_with_action: dfst:parser -> a:lam action -> dsnd:lam parser -> parser'
  | Parse_dep_pair_with_refinement_and_action: n1: A.ident -> dfst:parser -> refinement:lam expr -> a:lam action -> dsnd:lam parser -> parser'
  | Parse_map       : p:parser -> f:lam expr -> parser'
  | Parse_refinement: n:A.ident -> p:parser -> f:lam expr -> parser'
  | Parse_refinement_with_action : n:A.ident -> p:parser -> f:lam expr -> a:lam action -> parser'
  | Parse_with_dep_action : name:A.ident -> p:parser -> a:lam action -> parser'
  | Parse_with_action: name: A.ident -> p:parser -> a:action -> parser'
  | Parse_weaken_left: p:parser ->  k:parser_kind -> parser'
  | Parse_weaken_right: p:parser ->  k:parser_kind -> parser'
  | Parse_if_else   : e:expr -> parser -> parser -> parser'
  | Parse_impos     : parser'
  | Parse_with_comment: p:parser -> c:A.comments -> parser'
  | Parse_string    : p:parser -> zero:expr -> parser'

and parser = {
  p_kind:parser_kind;
  p_typ:typ;
  p_parser:parser';
  p_typename: A.ident;
  p_fieldname: string;
}

noeq
type reader =
  | Read_u8
  | Read_u16
  | Read_u32
  | Read_filter : r:reader -> f:lam expr -> reader
  | Read_app : hd:A.ident -> args:list index -> reader

noeq
type validator' =
  | Validate_return:
    validator'

  | Validate_app:
    hd:A.ident ->
    args:list index ->
    validator'

  | Validate_nlist:
    n:expr ->
    v:validator ->
    validator'

  | Validate_nlist_constant_size_without_actions:
    n:expr ->
    v:validator ->
    validator'

  | Validate_t_at_most:
    n:expr ->
    v:validator ->
    validator'

  | Validate_t_exact:
    n:expr ->
    v:validator ->
    validator'

  | Validate_pair:
    n1:A.ident ->
    v1:validator ->
    v2:validator ->
    validator'

  | Validate_dep_pair:
    n1:A.ident ->
    v:validator ->
    r:reader ->
    k:lam validator ->
    validator'

  | Validate_dep_pair_with_refinement:
    p1_is_constant_size_without_actions:bool ->
    n1:A.ident ->
    dfst:validator ->
    r:reader ->
    refinement:lam expr ->
    dsnd:lam validator ->
    validator'

  | Validate_dep_pair_with_action:
    dfst:validator ->
    r:reader ->
    a:lam action ->
    dsnd:lam validator ->
    validator'

  | Validate_dep_pair_with_refinement_and_action:
    p1_is_constant_size_without_actions:bool ->
    n1:A.ident ->
    dfst:validator ->
    r:reader ->
    refinement:lam expr ->
    a:lam action ->
    dsnd:lam validator ->
    validator'

  | Validate_map:
    p:validator ->
    f:lam expr ->
    validator'

  | Validate_refinement:
    n:A.ident ->
    v:validator ->
    r:reader ->
    f:lam expr ->
    validator'

  | Validate_refinement_with_action:
    n:A.ident ->
    v:validator ->
    r:reader ->
    f:lam expr ->
    a:lam action ->
    validator'

  | Validate_with_dep_action:
    name:A.ident ->
    v:validator ->
    r:reader ->
    a:lam action ->
    validator'

  | Validate_with_action:
    name:A.ident ->
    v:validator ->
    a:action ->
    validator'

  | Validate_weaken_left:
    v:validator ->
    k:parser_kind ->
    validator'

  | Validate_weaken_right:
    v:validator ->
    k:parser_kind ->
    validator'

  | Validate_if_else:
    e:expr ->
    validator ->
    validator ->
    validator'

  | Validate_impos:
    validator'

  | Validate_with_error_handler:
    typename:A.ident ->
    fieldname:string ->
    v:validator ->
    validator'

  | Validate_with_comment:
    v:validator ->
    c:A.comments ->
    validator'

  | Validate_string:
    v:validator ->
    r:reader ->
    zero:expr ->
    validator'

and validator = {
  v_allow_reading: bool;
  v_parser:parser;
  v_validator:validator'
}

////////////////////////////////////////////////////////////////////////////////

noeq
type type_decl = {
  decl_name: typedef_name;
  decl_typ: typedef_body;
  decl_parser: parser;
  decl_validator: validator;
  decl_reader: option reader
}

let definition = A.ident * list param * typ * expr

let assumption = A.ident * typ

type decl_attributes = {
  is_hoisted: bool;
  is_exported: bool;
  should_inline: bool;
  comments: list string;
}

noeq
type decl' =
  | Assumption : assumption -> decl'
  | Definition : definition -> decl' //the bool marks it for inline_for_extraction
  | Type_decl : type_decl -> decl'

let decl = decl' * decl_attributes

val error_handler_decl : decl
val print_typ (mname:string) (t:typ) : ML string //(decreases t)
val print_decls (modul: string) (ds:list decl) : ML string
val print_types_decls (modul: string) (ds:list decl) : ML string
val print_decls_signature (modul: string) (ds:list decl) : ML string
val print_c_entry (modul: string) (env: global_env) (ds:list decl)
  : ML (string & string)
