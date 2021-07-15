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
module Binding

(*
  This module implements a pass over the source AST
     -- checking that all names are properly bound
     -- well-typed
     -- computing the size of types
     -- computing which fields are dependent on others
*)
open FStar.Mul
open Ast
open FStar.All
module H = Hashtable

/// Computed attributes for a decl:
///    -- its size in bytes
///    -- whether or not it ends with a variable-length field (suffix)
///    -- whether or not its validator may fail
///    -- whether the type is an integral type, i.e., can it be decomposed into bitfields
type decl_attributes = {
  may_fail:bool;
  integral:option integer_type;
  has_reader:bool;
  parser_weak_kind:weak_kind;
  parser_kind_nz:option bool
}

noeq
type macro_signature = {
  macro_arguments_t: list typ;
  macro_result_t: typ;
  macro_defn_t:option expr
}

let nullary_macro t d = {
  macro_arguments_t = [];
  macro_result_t = t;
  macro_defn_t = d
}

(* Type-checking environments *)

/// global_env ge_h field is a hash (hence `_h`) table that:
///  -- maps top-level identifiers to their corresponding declaration
///  -- maps type identifiers to decl_attributes
///  -- maps macro names to their types
///
/// global_env ge_fd field maps a unique numerical identifier to each
/// "struct identifier - field (hence `_fd`) name" pair. It is part of
/// the global environment so that numerical field identifiers are
/// proper to the current module, and not shared across different .3d
/// files given on the command line

type global_hash_t = H.t ident' (decl & either decl_attributes macro_signature)

noeq
type global_env = {
  ge_h: global_hash_t
}

/// Maps locally bound names, i.e., a field name to its type
///  -- the bool signifies that this identifier has been used, and is
///     therefore marked as a dependent field
///
/// The modul_name in these ident' must be None -- TODO: add a refinement?
let local_env = H.t ident' (ident' & typ & bool)

/// `env` includes both a global and local env, together with a
/// binding for the `this` variable (bound to the name of a type) in
/// the current scope
noeq
type env = {
  this: option ident;
  locals: local_env;
  globals: global_env;
}

let mk_env (g:global_env) =
  { this = None;
    locals = H.create 10;
    globals = g }

let global_env_of_env e = e.globals

let params_of_decl (d:decl) : list param =
  match d.d_decl.v with
  | ModuleAbbrev _ _
  | Define _ _ _
  | TypeAbbrev _ _
  | Enum _ _ _ -> []
  | Record _ params _ _
  | CaseType _ params _ -> params

let check_shadow (e:H.t ident' 'a) (i:ident) (r:range) =
  match H.try_find e i.v with
  | Some j ->
    let msg = Printf.sprintf "Declaration %s clashes with previous declaration" (ident_to_string i) in
    error msg i.range
  | _ -> ()

let typedef_names (d:decl) : option typedef_names =
  match d.d_decl.v with
  | Record td _ _ _
  | CaseType td _ _ -> Some td
  | _ -> None

let format_identifier (e:env) (i:ident) : ML ident =
  let j =
    match String.list_of_string i.v.name with
    | [] ->
      failwith "Impossible: empty identifier"
    | c0::cs ->
      if FStar.Char.lowercase c0 = c0
      then i //it starts with a lowercase symbol; that's ok
      else //otherwise, add an underscore
           {i with v = {i.v with name=Ast.reserved_prefix ^ i.v.name}}
  in
  match H.try_find e.globals.ge_h j.v, H.try_find e.locals j.v with
  | None, None -> j
  | _ ->
    let msg = Printf.sprintf
      "This name (%s) starts will clash with another name in scope (%s) as it is translated. \
       Please rename it"
       (ident_to_string i) (ident_to_string j) in
    error msg i.range

let add_global (e:global_env) (i:ident) (d:decl) (t:either decl_attributes macro_signature) : ML unit =
  let insert k v = H.insert e.ge_h k v in

  check_shadow e.ge_h i d.d_decl.range;
  let env = mk_env e in
  let i' = format_identifier env i in
  insert i.v (d, t);
  insert i'.v (d, t);
  match typedef_names d with
  | None -> ()
  | Some td ->
    if td.typedef_abbrev.v <> i.v
    then begin
      check_shadow e.ge_h td.typedef_abbrev d.d_decl.range;
      let abbrev = format_identifier env td.typedef_abbrev in
      insert td.typedef_abbrev.v (d, t);
      insert abbrev.v (d, t)
    end

let add_local (e:env) (i:ident) (t:typ) : ML unit =
  check_shadow e.globals.ge_h i t.range;
  check_shadow e.locals i t.range;
  let i' = format_identifier e i in
  H.insert e.locals i.v (i'.v, t, false);
  H.insert e.locals i'.v (i'.v, t, false)

let lookup (e:env) (i:ident) : ML (either typ (decl & either decl_attributes macro_signature)) =
  match H.try_find e.locals i.v with
  | Some (_, t, true) ->
    Inl t
  | Some (j, t, false) ->  //mark it as used
    H.remove e.locals i.v;
    H.insert e.locals i.v (j, t, true);
    Inl t
  | None ->
    match H.try_find e.globals.ge_h i.v with
    | Some d -> Inr d
    | None -> error (Printf.sprintf "Variable %s not found" (ident_to_string i)) i.range

let remove_local (e:env) (i:ident) : ML unit =
  match H.try_find e.locals i.v with
  | Some (j, _, _) ->
    H.remove e.locals i.v;
    H.remove e.locals j
  | _ -> ()

let resolve_typedef_abbrev (env:env) (i:ident) =
    match lookup env i with
    | Inr ({d_decl={v=Record names _ _ _}}, _)
    | Inr ({d_decl={v=CaseType names _ _}}, _) ->
      names.typedef_name
    | _ -> i

let lookup_expr_name (e:env) (i:ident) : ML typ =
  match lookup e i with
  | Inl t -> t
  | Inr (_, Inr ({ macro_arguments_t=[]; macro_result_t=t })) -> t
  | Inr _ ->
    error (Printf.sprintf "Variable %s is not an expression identifier" (ident_to_string i)) i.range

let lookup_macro_name (e:env) (i:ident) : ML macro_signature =
  match lookup e i with
  | Inr (_, Inr m) -> m
  | _ -> error (Printf.sprintf "%s is an unknown operator" (ident_to_string i)) i.range

let lookup_macro_definition (e:env) (i:ident) =
  try
    let m = lookup_macro_name e i in
    m.macro_defn_t
  with
  | _ -> None

let try_lookup_enum_cases (e:env) (i:ident)
  : ML (option (list ident & typ))
  = match lookup e i with
    | Inr ({d_decl={v=Enum t _ tags}}, _) ->
      Some (Desugar.check_desugared_enum_cases tags, t)
    | _ -> None

let lookup_enum_cases (e:env) (i:ident)
  : ML (list ident & typ)
  = match try_lookup_enum_cases e i with
    | Some (tags, t) -> tags, t
    | _ -> error (Printf.sprintf "Type %s is not an enumeration" (ident_to_string i)) i.range

let is_used (e:env) (i:ident) : ML bool =
  match H.try_find e.locals i.v with
  | Some (_, t, b) -> b
  | _ ->  error (Printf.sprintf "Variable %s not found" (ident_to_string i)) i.range

let type_of_integer_type = function
  | UInt8  -> tuint8
  | UInt16 -> tuint16
  | UInt32 -> tuint32
  | UInt64 -> tuint64

let check_integer_bounds t i =
    match t with
    | UInt8  -> FStar.UInt.fits i 8
    | UInt16 -> FStar.UInt.fits i 16
    | UInt32 -> FStar.UInt.fits i 32
    | UInt64 -> FStar.UInt.fits i 64

let type_of_constant rng (c:constant) : ML typ =
  match c with
  | Unit -> tunit
  | Int tag i ->
    if check_integer_bounds tag i
    then type_of_integer_type tag
    else error (Printf.sprintf "Constant %d is too large for its type %s" i (Ast.print_integer_type tag)) rng
  | XInt tag _ -> //bounds checked by the syntax
    type_of_integer_type tag
  | Bool _ -> tbool


let parser_may_fail (env:env) (t:typ) : ML bool =
  match t.v with
  | Pointer _ -> true
  | Type_app hd _ ->
    match lookup env hd with
    | Inr (d, Inl attrs) -> attrs.may_fail
    | _ -> false

let typ_is_integral env (t:typ) : ML bool =
  match t.v with
  | Pointer _ -> false
  | Type_app hd _ ->
    match lookup env hd with
    | Inr (d, Inl attrs) -> Some? attrs.integral
    | _ -> false

let tag_of_integral_typ env (t:typ) : ML (option _) =
  match t.v with
  | Pointer _ -> None
  | Type_app hd _ ->
    match lookup env hd with
    | Inr (_, Inl attrs) -> attrs.integral
    | _ -> None

let has_reader (env:global_env) (id:ident) : ML bool =
  match H.try_find env.ge_h id.v with
  | Some (_, Inl attrs) -> attrs.has_reader
  | _ -> false

let parser_kind_nz (env:global_env) (id:ident) : ML (option bool) =
  match H.try_find env.ge_h id.v with
  | Some (_, Inl attrs) -> attrs.parser_kind_nz
  | _ -> None

let parser_weak_kind (env:global_env) (id:ident) : ML (option _) =
  match H.try_find env.ge_h id.v with
  | Some (_, Inl attrs) -> Some attrs.parser_weak_kind
  | _ -> None

let typ_weak_kind env (t:typ) : ML (option weak_kind) =
  match t.v with
  | Pointer _ -> None
  | Type_app hd _ -> parser_weak_kind env.globals hd

let typ_has_reader env (t:typ) : ML bool =
  match t.v with
  | Pointer _ -> false
  | Type_app hd _ ->
    has_reader env.globals hd

let rec unfold_typ_abbrevs (env:env) (t:typ) : ML typ =
  match t.v with
  | Type_app hd [] -> //type abbreviations are not parameterized
    begin
    match lookup env hd with
    | Inr (d, _) ->
      begin
      match d.d_decl.v with
      | TypeAbbrev t _ -> unfold_typ_abbrevs env t
      | Enum t _ _ -> unfold_typ_abbrevs env t
      | _ -> t
      end
    | _ -> t
    end
  | _ -> t

let size_of_integral_typ (env:env) (t:typ) r
  : ML int
  = let t = unfold_typ_abbrevs env t in
    if not (typ_is_integral env t)
    then error (Printf.sprintf "Expected and integral type, got %s"
                                                (print_typ t))
               r;
    match tag_of_integral_typ env t with
    | None -> failwith "Impossible"
    | Some UInt8 -> 1
    | Some UInt16 -> 2
    | Some UInt32 -> 4
    | Some UInt64 -> 8

let eq_typ env t1 t2 =
  if Ast.eq_typ t1 t2 then true
  else Ast.eq_typ (unfold_typ_abbrevs env t1) (unfold_typ_abbrevs env t2)

let eq_typs env ts =
  List.for_all (fun (t1, t2) -> eq_typ env t1 t2) ts

let cast e t t' = { e with v = App (Cast (Some t) t') [e] }

let try_cast_integer env et to : ML (option expr) =
  let e, from = et in
  let i_to = typ_is_integral env to in
  let i_from = typ_is_integral env from in
  if i_from && i_to
  then
    let i_from = typ_as_integer_type (unfold_typ_abbrevs env from) in
    let i_to = typ_as_integer_type (unfold_typ_abbrevs env to) in
    if i_from = i_to
    then Some e
    else if integer_type_leq i_from i_to
    then Some (cast e i_from i_to)
    else None
  else None

let _or_ b1 b2 = b1 || b2
let _and_ b1 b2 = b1 && b2
let try_retype_arith_exprs (env:env) e1 e2 rng : ML (option (expr & expr & typ))=
  let e1, t1 = e1 in
  let e2, t2 = e2 in
  let fail #a i : ML a  = raise (Error (Printf.sprintf "(%d) Failed to retype exprs (%s : %s) and (%s : %s)"
                                                        i
                                                        (print_expr e1)
                                                        (print_typ t1)
                                                        (print_expr e2)
                                                        (print_typ t2))) in
  try
    let t1, t2 = unfold_typ_abbrevs env t1, unfold_typ_abbrevs env t2 in
    if not (typ_is_integral env t1 `_and_`
            typ_is_integral env t2)
    then fail 1;
    let tt1 = typ_as_integer_type t1 in
    let tt2 = typ_as_integer_type t2 in
    let cast e t t' = { e with v = App (Cast (Some t) t') [e] } in
    let e1, e2, t =
      if integer_type_leq tt1 tt2
      then cast e1 tt1 tt2,
           e2,
           t2
      else if integer_type_leq tt2 tt1
      then e1,
           cast e2 tt2 tt1,
           t1
      else fail 0
    in
    // FStar.IO.print_string
    //   (Printf.sprintf "Retyped to (%s, %s, %s)\n"
    //     (print_expr e1)
    //     (print_expr e2)
    //     (print_typ t));
    Some (e1, e2, t)
  with
    | Error msg ->
      FStar.IO.print_string msg;
      None
    | _ -> None


#push-options "--z3rlimit_factor 4"
let rec check_typ (pointer_ok:bool) (env:env) (t:typ)
  : ML typ
  = match t.v with
    | Pointer t0 ->
      if pointer_ok
      then { t with v = Pointer (check_typ pointer_ok env t0) }
      else error (Printf.sprintf "Pointer types are not permissible here; got %s" (print_typ t)) t.range

    | Type_app s es ->
      match lookup env s with
      | Inl _ ->
        error (Printf.sprintf "%s is not a type" (ident_to_string s)) s.range

      | Inr (d, _) ->
        let params = params_of_decl d in
        if List.length params <> List.length es
        then error (Printf.sprintf "Not enough arguments to %s" (ident_to_string s)) s.range;
        let es =
          List.map2 (fun (t, _, _) e ->
            let e, t' = check_expr env e in
            if not (eq_typ env t t')
            then match try_cast_integer env (e, t') t with
                 | Some e -> e
                 | _ -> error "Argument type mismatch" e.range
            else e)
            params
            es
        in
        {t with v = Type_app s es}

and check_expr (env:env) (e:expr)
  : ML (expr & typ)
  = let w e' = with_range e' e.range in
    let arith_op_t op t : ML Ast.op =
      let t = tag_of_integral_typ env t in
      match op with
      | Plus _ -> Plus t
      | Minus _ -> Minus t
      | Mul _ -> Mul t
      | Division _ -> Division t
      | Remainder _ -> Remainder t
      | BitwiseNot _ -> BitwiseNot t
      | BitwiseAnd _ -> BitwiseAnd t
      | BitwiseOr _ -> BitwiseOr t
      | BitwiseXor _ -> BitwiseXor t
      | ShiftLeft _ -> ShiftLeft t
      | ShiftRight _ -> ShiftRight t
      | LE _ -> LE t
      | LT _ -> LT t
      | GE _ -> GE t
      | GT _ -> GT t
      | _ -> op
    in
    match e.v with
    | Constant c ->
      e, type_of_constant e.range c

    | Identifier i ->
      let t = lookup_expr_name env i in
      e, t

    | This ->
      error "`this` is not a valid expression" e.range

    | App (Cast _ to) [n] ->
      let n, from = check_expr env n in
      begin
      if not (typ_is_integral env from)
      then error (Printf.sprintf "Casts are only supported on integral types; %s is not integral"
                    (print_typ from)) e.range
      else match from.v with
           | Type_app i _ ->
             let from_t = as_integer_typ i in
             if integer_type_lub to from_t <> to
             then error (Printf.sprintf "Only widening casts are supported; casting %s to %s loses precision"
                                (print_typ from)
                                (print_integer_type to))
                        e.range
             else
              let e = {e with v = App (Cast (Some from_t) to) [n]} in
              let t = type_of_integer_type to in
              Options.debug_print_string
                (Printf.sprintf "--------------- %s has type %s\n"
                             (print_expr e)
                             (print_typ t));
              e, t
           | _ -> failwith "Impossible: must be an integral type"
      end

    | App SizeOf [{v=This;range=r}] ->
      let e =
        match env.this with
        | None ->
          error "`this` is not in scope" r
        | Some i ->
          with_range (App SizeOf [with_range (Identifier i) r]) e.range
      in
      e, tuint32

    | App SizeOf [{v=Identifier i;range=r}] ->
      begin
      match lookup env i with
      | Inr ({d_decl={v=Enum _ _ _}}, _)
      | Inr ({d_decl={v=Record _ _ _ _ }}, _)
      | Inr ({d_decl={v=CaseType _ _ _}}, _)
      | Inr (_, Inl _) ->  //has decl-attributes
        e, tuint32
      | _ ->
        error "`sizeof` applied to a non-sized-typed" r
      end

    | App (Ext s) es ->
      //TODO: AR: not sure about this Ext node
      let m = lookup_macro_name env (with_range (to_ident' s) e.range) in
      let n_formals = List.length m.macro_arguments_t in
      let n_actuals = List.length es in
      if n_formals <> n_actuals
      then error (Printf.sprintf "%s expects %d arguments; got %d" s n_formals n_actuals) e.range;
      let check_arg e t : ML expr =
        let e, t' = check_expr env e in
        if not (eq_typ env t t')
        then error
               (Printf.sprintf
                  "%s expected argument of type %s; \
                  got argument %s of type %s"
                  s (print_typ t) (print_expr e) (print_typ t))
               e.range;
        e
      in
      let es = List.map2 check_arg es m.macro_arguments_t in
      with_range (App (Ext s) es) e.range,
      m.macro_result_t

    | App op es ->
      let ets = List.map (check_expr env) es in
      match ets with
      | [(e1, t1)] ->
        begin
        match op with
        | Not ->
          if not (eq_typ env t1 tbool)
          then error "Expected bool" e1.range;
          w (App Not [e1]), t1

        | BitwiseNot _ ->
          if typ_is_integral env t1
          then w (App (arith_op_t op t1) [e1]), t1
          else error (Printf.sprintf "Bitwise negation is only available on integral types; got %s"
                                     (print_typ t1))
                     e1.range
        | _ ->
          error "Not a unary op" e1.range
        end

      | [(e1,t1);(e2,t2)] ->
        begin
        match op with
        | Eq
        | Neq ->
          if not (eq_typ env t1 t2)
          then
          begin
            let err #a () : ML a =
                error
                     (Printf.sprintf "Equality on unequal types: %s and %s"
                       (print_typ t1)
                       (print_typ t2))
                     e.range
            in
            let it1 = typ_is_integral env t1 in
            let it2 = typ_is_integral env t2 in
            if it1 && it2
            then match try_retype_arith_exprs env (e1, t1) (e2, t2) e.range with
                 | Some (e1, e2, t) -> w (App op [e1; e2]), tbool
                 | _ -> err ()

            else err ()
          end
          else
            w (App op [e1; e2]), tbool

        | And
        | Or ->
          if not (eq_typs env [(t1,tbool); (t2,tbool)])
          then error "Binary boolean op on non booleans" e.range;
          w (App op [e1; e2]), tbool

        | ShiftLeft _
        | ShiftRight _ ->
          let t1_integral = typ_is_integral env t1 in
          let t2_integral = typ_is_integral env t2 in
          if not t1_integral || not t2_integral
          then error (Printf.sprintf "Bit shifts are only permissible on integral types: got %s and %s"
                                     (print_typ t1)
                                     (print_typ t2))
                     e.range;
          begin
          match try_cast_integer env (e2, t2) tuint32 with
          | None ->
            error (Printf.sprintf "Bit shift offset is too large: got type %s"
                                     (print_typ t2))
                  e2.range

          | Some e2 ->
            w (App (arith_op_t op t1) [e1; e2]), t1
          end

        | Plus _
        | Minus _
        | Mul _
        | Division _
        | Remainder _
        | LT _
        | GT _
        | LE _
        | GE _
        | BitwiseAnd _
        | BitwiseOr _
        | BitwiseXor _ ->
          let result_typ t =
              match op with
              | LT _ | GT _ | LE _ | GE _ -> tbool
              | _ -> t
          in
          let t1_integral = typ_is_integral env t1 in
          let t2_integral = typ_is_integral env t2 in
          if not t1_integral || not t2_integral
          then error (Printf.sprintf "Binary integer op on non-integral types: %s and %s"
                                     (print_typ t1)
                                     (print_typ t2))
               e.range;


          if not (eq_typs env [(t1,t2)])
          then match try_retype_arith_exprs env (e1, t1) (e2, t2) e.range with
               | Some (e1, e2, t) ->
                 w (App (arith_op_t op t) [e1; e2]), result_typ t

               | _ ->
                 error (Printf.sprintf "Binary integer operator (%s) on non-equal types: %s and %s"
                                     (print_expr e)
                                     (print_typ t1)
                                     (print_typ t2))
                     e.range
          else w (App (arith_op_t op t1) [e1; e2]), result_typ t1

        | _ ->
          error "Not a binary op" e.range
        end

      | [(e1, t1); (e2, t2); (e3, t3)] ->
        begin
        match op with
        | IfThenElse ->
          if not (eq_typ env t1 tbool)
          then error (Printf.sprintf "If-then-else expects a boolean guard, got %s" (print_typ t1))
                     e1.range;
          if not (eq_typ env t2 t3)
          then match try_retype_arith_exprs env (e2, t2) (e3, t3) e.range with
               | Some (e2, e3, t) ->
                 w (App IfThenElse [e1;e2;e3]), t
               | None ->
                 error (Printf.sprintf "then- and else-branch do not have the same type: got %s and %s"
                                       (print_typ t2)
                                       (print_typ t3))
                       e.range
          else
            w (App IfThenElse [e1;e2;e3]), t2

        | BitFieldOf n ->
          let base_size = size_of_integral_typ env t1 e1.range in
          let size = 8 * base_size in
          if n <> size
          then error
                 (Printf.sprintf "BitFieldOf size %d is not equal to %d, i.e., the bit size %s"
                   n size (print_expr e1))
                 e1.range;
          begin
          match e2.v, e2.v with
          | Constant (Int UInt32 from), (Constant (Int UInt32 to)) ->
            if not
               (from <= size
            && from <= to
            && to <= size)
            then error "bitfield-of expresssions is out of bounds" e.range;
            w (App (BitFieldOf n) [e1; e2; e3]), t1
          | _ ->
           error "bitfield-of with non-32-bit-consant indices" e.range
          end

        | _ ->
          error "Unexpected arity" e.range
        end
      | _ -> error "Unexpected arity" e.range

#pop-options
#push-options "--z3rlimit_factor 2"

let rec check_field_action (env:env) (f:field) (a:action)
  : ML (action & typ)
  = let check_atomic_action env (r:range) (a:atomic_action)
      : ML (atomic_action & typ)
      = match a with
        | Action_return e ->
          let e, t = check_expr env e in
          Action_return e, t

        | Action_abort ->
          Action_abort, tunit

        | Action_field_pos ->
          Action_field_pos, tuint32

        | Action_field_ptr ->
          Action_field_ptr, puint8

        | Action_deref i ->
          let t = lookup_expr_name env i in
          begin
          match t.v with
          | Pointer t -> Action_deref i, t
          | _ -> error "Dereferencing a non-pointer" i.range
          end

        | Action_assignment lhs rhs ->
          let t = lookup_expr_name env lhs in
          let rhs, t' = check_expr env rhs in
          begin
          match t.v with
          | Pointer t0 ->
            if not (eq_typ env t0 t')
            then warning (Printf.sprintf
                          "Assigning to pointer %s of type %s a value of incompatible type %s"
                          (print_ident lhs)
                          (print_typ t)
                          (print_typ t'))
                       rhs.range;
            Action_assignment lhs rhs, tunit
          | _ ->
            error "Assigning to a non-pointer" lhs.range
          end

        | Action_call f args ->
          error "Extern calls are not yet supported" r
    in
    match a.v with
    | Atomic_action aa ->
      let aa, t = check_atomic_action env a.range aa in
      { a with v=Atomic_action aa }, t

    | Action_seq a0 as ->
      let a0, _ = check_atomic_action env a.range a0 in
      let as, t = check_field_action env f as in
      { a with v=Action_seq a0 as }, t

    | Action_ite hd then_ else_ ->
      let hd, t = check_expr env hd in
      if not (eq_typ env t tbool)
      then error (Printf.sprintf
                      "Branching is only permitted on boolean expressions, %s has type %s"
                        (print_expr hd)
                        (print_typ t))
                 hd.range;
      let then_, t = check_field_action env f then_ in
      let else_, t' =
        match else_ with
        | None -> None, tunit
        | Some else_ ->
          let else_, t = check_field_action env f else_ in
          Some else_, t
      in
      let branches_eq_t = eq_typ env t t' in
      let eq_t_unit = eq_typ env t tunit in
      if not branches_eq_t
      || (None? else_ && not eq_t_unit)
      then error (Printf.sprintf "The branches of a conditional must both have the same type; got %s and %s"
                                 (print_typ t)
                                 (print_typ t'))
                a.range;
      { a with v = Action_ite hd then_ else_ }, t

    | Action_let i aa k ->
      let aa, t = check_atomic_action env a.range aa in
      add_local env i t;
      let k, t = check_field_action env f k in
      remove_local env i;
      { a with v = Action_let i aa k }, t

#pop-options

#push-options "--z3rlimit_factor 4"
let check_field (env:env) (extend_scope: bool) (f:field)
  : ML field
  = let sf = f.v in
    let sf_field_type = check_typ false env sf.field_type in
    let check_annot (e: expr) : ML expr =
        let e, t = check_expr env e in
        if not (eq_typ env t tuint32)
        then match try_cast_integer env (e, t) tuint32 with
             | Some e -> e
             | _ ->  error (Printf.sprintf "Array expression %s has type %s instead of UInt32"
                          (print_expr e)
                          (print_typ t))
                    e.range
        else e
    in
    let fa = match sf.field_array_opt with
    | FieldScalar -> FieldScalar
    | FieldArrayQualified (e, b) -> FieldArrayQualified (check_annot e, b)
    | FieldString sz -> FieldString (map_opt check_annot sz)
    in
    let fc = sf.field_constraint |> map_opt (fun e ->
        add_local env sf.field_ident sf.field_type;
        let e = fst (check_expr env e) in
        remove_local env sf.field_ident;
        e)
    in
    let f_act = sf.field_action |> map_opt (fun (a, _) ->
        add_local env sf.field_ident sf.field_type;
        let a, _ = check_field_action env f a in
        let dependent = is_used env sf.field_ident in
        remove_local env sf.field_ident;
        a, dependent)
    in
    if extend_scope then add_local env sf.field_ident sf.field_type;
    let sf = {
        sf with
        field_type = sf_field_type;
        field_array_opt = fa;
        field_constraint = fc;
        field_action = f_act
    } in
    Options.debug_print_string
      (Printf.sprintf "Field %s has comments <%s>\n"
                  (print_ident sf.field_ident)
                  (String.concat "\n" f.comments));
    { f with v = sf }

let is_strong_prefix_field_array (a: field_array_t) : Tot bool =
  not (FieldScalar? a)

let weak_kind_of_field (env: env) (f: field) : ML weak_kind =
  if is_strong_prefix_field_array f.v.field_array_opt
  then WeakKindStrongPrefix
  else match typ_weak_kind env f.v.field_type with
  | Some e -> e
  | None -> failwith (Printf.sprintf "cannot find the weak kind of field %s : %s" (print_ident f.v.field_ident) (print_typ f.v.field_type))

let weak_kind_of_case (env: env) (c: case) : ML weak_kind =
  match c with
  | DefaultCase f
  | Case _ f
    -> weak_kind_of_field env f

#pop-options

#push-options "--z3rlimit_factor 8"
let check_switch (env:env) (s:switch_case)
  : ML (switch_case & decl_attributes)
  = let head, cases = s in
    let head, scrutinee_t = check_expr env head in
    let fail_non_equality_type (#a:Type) ()  : ML (option a) =
        let integral = typ_is_integral env scrutinee_t in
        let is_bool = eq_typ env scrutinee_t tbool in
        if not integral
        && not is_bool
        then error (Printf.sprintf "Case analysis of a non-integral or non-boolean type (%s) is not supported"
                                     (print_typ scrutinee_t))
                     head.range;
        None
    in
    let tags_t_opt =
      match scrutinee_t.v with
      | Pointer _ -> fail_non_equality_type ()
      | Type_app hd es ->
        match try_lookup_enum_cases env hd with
        | Some enum -> Some enum
        | _ -> fail_non_equality_type ()
    in
    let check_case (c:case{Case? c}) : ML case =
      let Case pat f = c in
      let pat, pat_t = check_expr env pat in
      let f = check_field env false f in
      let pat = //check type of patterns
        match tags_t_opt with
        | None ->
          //Not an enum; just check that its a valid u32
          if not (eq_typ env scrutinee_t pat_t)
          then match try_cast_integer env (pat, pat_t) scrutinee_t with
               | Some pat -> pat
               | _ ->
                 error (Printf.sprintf "Type of case (%s) does not match type of switch expression (%s)"
                                       (print_typ pat_t)
                                       (print_typ scrutinee_t))
                       pat.range
          else pat

        | Some (enum_tags, t) ->
          //expected an enumerated type;
          //check that patterns are valid cases of the enum
          let case_exists =
            match pat.v with
            | Identifier pat ->
              Some? (List.tryFind (fun (case:ident) -> case.v = pat.v) enum_tags)
            | _ ->
              false
          in
          if not (eq_typ env pat_t t)
          then error (Printf.sprintf "Type of case (%s) does not match type of switch expression (%s)"
                                     (print_typ pat_t)
                                     (print_typ t))
                     pat.range;

          if not case_exists
          then error (Printf.sprintf "Case (%s) is not in the enumerated type %s"
                                     (print_expr pat)
                                     (print_typ scrutinee_t))
                     pat.range;
          pat
      in
      Case pat f
    in
    let check_default_case (c:case{DefaultCase? c}) : ML case =
       let DefaultCase f = c in
       let f = check_field env false f in
       DefaultCase f
    in
    let cases =
      List.map (fun (o:case) -> if Case? o then check_case o else check_default_case o) cases in
    let _ =
      List.fold_right
        (fun case default_ok ->
           match case with
           | Case _ _ -> false
           | DefaultCase f ->
              if default_ok then false
              else raise (error "default is only allowed in the last case"
                                f.v.field_ident.range))
        cases
        true
    in
    let wk = match cases with
    | [] -> failwith "no cases in switch"
    | c :: cases' ->
      List.fold_left
        (fun wk case -> weak_kind_glb wk (weak_kind_of_case env case))
        (weak_kind_of_case env c)
        cases'
    in
    let attrs = {
      may_fail = false;
      integral = None;
      has_reader = false;
      parser_weak_kind = wk;
      parser_kind_nz = None
    } in
    (head, cases), attrs
#pop-options


(** Computes a layout for bit fields,
    decorating each field with a bitfield index
    and a bit range within that bitfield to store the given field.

    Collapsing adjacent bitfields into a single field is done in a
    separate phase, see BitFields.fst
 *)
let elaborate_bit_fields env (fields:list field)
  : ML (list field)
  = let new_bit_field index sf bw r : ML (field & option (typ & int & int)) =
        let size = size_of_integral_typ env sf.field_type r in
        let bit_size = 8 * size in
        let remaining_size = bit_size - bw.v in
        let from = 0 in
        let to = bw.v in
        let bf_attr = {
            bitfield_width = bw.v;
            bitfield_identifier = index;
            bitfield_type = sf.field_type;
            bitfield_from = from;
            bitfield_to = to
        } in
        let sf = { sf with field_bitwidth = Some (Inr (with_range bf_attr r)) } in
        with_range sf r,
        Some (sf.field_type, to, remaining_size)
    in
    let rec aux bf_index open_bit_field fields
      : ML (list field)
      = match fields with
        | [] ->
          []

        | hd::tl ->
          let sf = hd.v in
          match sf.field_bitwidth, open_bit_field with
          | None, None ->
            hd :: aux bf_index open_bit_field tl

          | None, Some _ ->  //end the bit field
            hd :: aux (bf_index + 1) None tl

          | Some (Inr _), _ ->
            failwith "Bitfield is already elaborated"

          | Some (Inl bw), None ->
            let hd, open_bit_field = new_bit_field bf_index sf bw hd.range in
            let tl = aux bf_index open_bit_field tl in
            hd :: tl

          | Some (Inl bw), Some (bit_field_typ, pos, remaining_size) ->
            Options.debug_print_string
              (Printf.sprintf
                "Field type = %s; bit_field_type = %s\n"
                  (print_typ sf.field_type)
                  (print_typ bit_field_typ));

            if remaining_size < bw.v //not enough space in this bit field, start a new one
            then let next_index = bf_index + 1 in
                 let hd, open_bit_field = new_bit_field next_index sf bw hd.range in
                 let tl = aux next_index open_bit_field tl in
                 hd :: tl
            else //extend this bit field
                 begin
                   if not (eq_typ env sf.field_type bit_field_typ)
                   then raise (error "Packing fields of different types into the same bit field is not yet supported" hd.range);
                   let remaining_size = remaining_size - bw.v in
                   let from = pos in
                   let to = pos + bw.v in
                   let bf_attr = {
                       bitfield_width = bw.v;
                       bitfield_identifier = bf_index;
                       bitfield_type = bit_field_typ;
                       bitfield_from = from;
                       bitfield_to = to
                   } in
                   let sf = { sf with field_bitwidth = Some (Inr (with_range bf_attr bw.range)) } in
                   let hd = { hd with v = sf } in
                   let open_bit_field = Some (bit_field_typ, to, remaining_size) in
                   let tl = aux bf_index open_bit_field tl in
                   hd :: tl
                 end
      in
      aux 0 None fields

let check_params (env:env) (ps:list param) : ML unit =
  ps |> List.iter (fun (t, p, _q) ->
      let _ = check_typ true env t in
      add_local env p t)

let rec weak_kind_of_fields (e: env) (l: list field) : ML weak_kind =
  match l with
  | [] -> WeakKindStrongPrefix
  | [a] -> weak_kind_of_field e a
  | a :: q ->
    let wk = weak_kind_of_field e a in
    if wk <> WeakKindStrongPrefix
    then failwith
          (Printf.sprintf "weak_kind_of_fields: \
                           field %s : %s should be of strong kind \
                           instead of %s"
                           (print_ident a.v.field_ident)
                           (print_typ a.v.field_type)
                           (print_weak_kind wk))
    else weak_kind_of_fields e q

let elaborate_record (e:global_env)
                     (tdnames:Ast.typedef_names)
                     (params:list param)
                     (where:option expr)
                     (fields:list field)
                     (range:range)
                     (comments:comments)
                     (is_exported:bool)
  : ML decl
  = let env = { mk_env e with this=Some tdnames.typedef_name } in

    (* Check parameters, that their types are well-formed;
       extend the environments with them *)
    check_params env params;

    (* If a where-clause is present, elaborate it into a refined unit field *)
    let where, maybe_unit_field =
      match where with
      | None ->
        None, []
      | Some e ->
        let e, t = check_expr env e in
        if not (eq_typ env t tbool)
        then error (Printf.sprintf "Expected a boolean where clause; got %s"
                   (print_typ t))
                 e.range;
        let w = Some e in
        let field =
          { field_dependence = true;
            field_ident = with_range (to_ident' "__precondition") e.range;
            field_type = tunit;
            field_array_opt = FieldScalar;
            field_constraint = w;
            field_bitwidth = None;
            field_action = None
          }
        in
        w, [with_range field e.range]
    in

    (* Elaborate and check each field in order;
       Checking each field extends the local environment with the name of that field *)
    let fields = fields |> List.map (check_field env true) in

    (* Infer which of the fields are dependent by seeing which of them are used in refinements *)
    let nfields = List.length fields in
    let fields = fields |> List.mapi (fun i f ->
      let sf = f.v in
      let used = is_used env sf.field_ident in
      let last_field = i = (nfields - 1) in
      let dependent = used || (Some? sf.field_constraint && not last_field) in
      let f =
        with_range_and_comments
          ({ sf with field_dependence = dependent })
          f.range
          f.comments
      in
      let has_reader = typ_has_reader env f.v.field_type in
      if f.v.field_dependence
      && not has_reader
      then error "The type of this field does not have a reader, \
                  either because its values are too large \
                  or because reading it may incur a double fetch; \
                  subsequent fields cannot depend on it" f.range
      else f)
    in

    let fields = maybe_unit_field@fields in

    let fields = elaborate_bit_fields env fields in

    let d = mk_decl (Record tdnames params where fields) range comments is_exported in

    let attrs = {
        may_fail = false; //only its fields may fail; not the struct itself
        integral = None;
        has_reader = false;
        parser_weak_kind = weak_kind_of_fields env fields;
        parser_kind_nz = None
      }
    in
    add_global e tdnames.typedef_name d (Inl attrs);
    d

let bind_decl (e:global_env) (d:decl) : ML decl =
  match d.d_decl.v with
  | ModuleAbbrev i m -> d
  | Define i None c ->
    let t = type_of_constant d.d_decl.range c in
    let d = decl_with_v d (Define i (Some t) c) in
    add_global e i d (Inr (nullary_macro t (Some (with_range (Constant c) d.d_decl.range))));
    d

  | Define i (Some t) c ->
    let env = mk_env e in
    let t = check_typ false env t in
    let t' = type_of_constant d.d_decl.range c in
    let d = decl_with_v d (Define i (Some t) c) in
    if eq_typ env t t'
    then (add_global e i d (Inr (nullary_macro (type_of_constant d.d_decl.range c)
                                               (Some (with_range (Constant c) d.d_decl.range))));
          d)
    else error "Ill-typed constant" d.d_decl.range

  | TypeAbbrev t i ->
    let env = mk_env e in
    let t = check_typ false env t in
    let wk =
      match typ_weak_kind env t with
      | None -> failwith (Printf.sprintf "Weak kind not found for type %s" (print_typ t))
      | Some wk -> wk
    in
    let attrs =
      {
        may_fail = parser_may_fail env t;
        integral = tag_of_integral_typ env t;
        has_reader = typ_has_reader env t;
        parser_weak_kind = wk;
        parser_kind_nz = None
      }
    in
    let d = decl_with_v d (TypeAbbrev t i) in
    add_global e i d (Inl attrs);
    d

  | Enum t i cases ->
    let env = mk_env e in
    let t = check_typ false env t in
    let cases_idents = Desugar.check_desugared_enum_cases cases in
    cases_idents |> List.iter (fun i ->
      let _, t' = check_expr env (with_dummy_range (Identifier i)) in
      if not (eq_typ env t t')
      then error (Printf.sprintf "Inconsistent type of enumeration identifier: Expected %s, got %s"
                   (print_typ t)
                   (print_typ t'))
                 d.d_decl.range);
    let attrs =
      {
        may_fail = true;
        integral = Some (typ_as_integer_type t);
        has_reader = false; //it's a refinement, so you can't read it again because of double fetches
        parser_weak_kind = WeakKindStrongPrefix;
        parser_kind_nz = None
      }
    in
    let d = decl_with_v d (Enum t i cases) in
    add_global e i d (Inl attrs);
    d

  | Record tdnames params where fields ->
    elaborate_record e tdnames params where fields d.d_decl.range d.d_decl.comments d.d_exported

  | CaseType tdnames params switch ->
    let env = { mk_env e with this=Some tdnames.typedef_name } in
    check_params env params;
    let switch, attrs = check_switch env switch in
    let d = mk_decl (CaseType tdnames params switch) d.d_decl.range d.d_decl.comments d.d_exported in
    add_global e tdnames.typedef_name d (Inl attrs);
    d

let bind_decls (g:global_env) (p:list decl) : ML (list decl & global_env) =
  List.map (bind_decl g) p, g

let initial_global_env () =
  let e = {
    ge_h = H.create 10
  }
  in
  let nullary_decl i =
    let td_name = {
      typedef_name = i;
      typedef_abbrev = i;
      typedef_ptr_abbrev = i;
      typedef_attributes = []
    }
    in
    mk_decl (Record td_name [] None []) dummy_range [] true
  in
  let _type_names =
    [ ("unit",     { may_fail = false; integral = None; has_reader = true; parser_weak_kind = WeakKindStrongPrefix; parser_kind_nz=Some false});
      ("Bool",     { may_fail = true;  integral = None; has_reader = true; parser_weak_kind = WeakKindStrongPrefix; parser_kind_nz=Some true});
      ("UINT8",    { may_fail = true;  integral = Some UInt8 ; has_reader = true; parser_weak_kind = WeakKindStrongPrefix; parser_kind_nz=Some true });
      ("UINT16",   { may_fail = true;  integral = Some UInt16 ; has_reader = true; parser_weak_kind = WeakKindStrongPrefix; parser_kind_nz=Some true });
      ("UINT32",   { may_fail = true;  integral = Some UInt32 ; has_reader = true; parser_weak_kind = WeakKindStrongPrefix; parser_kind_nz=Some true});
      ("UINT64",   { may_fail = true;  integral = Some UInt64 ; has_reader = true; parser_weak_kind = WeakKindStrongPrefix; parser_kind_nz=Some true});
      ("UINT16BE",   { may_fail = true;  integral = Some UInt16 ; has_reader = true; parser_weak_kind = WeakKindStrongPrefix; parser_kind_nz=Some true });
      ("UINT32BE",   { may_fail = true;  integral = Some UInt32 ; has_reader = true; parser_weak_kind = WeakKindStrongPrefix; parser_kind_nz=Some true});
      ("UINT64BE",   { may_fail = true;  integral = Some UInt64 ; has_reader = true; parser_weak_kind = WeakKindStrongPrefix; parser_kind_nz=Some true});
      ("field_id", { may_fail = true;  integral = Some UInt32 ; has_reader = false; parser_weak_kind = WeakKindStrongPrefix; parser_kind_nz=Some true});
      ("all_bytes", { may_fail = false;  integral = None ; has_reader = false; parser_weak_kind = WeakKindConsumesAll; parser_kind_nz=Some false});
      ("all_zeros", { may_fail = true;  integral = None ; has_reader = false; parser_weak_kind = WeakKindConsumesAll; parser_kind_nz=Some false});
      ("PUINT8",   { may_fail = true;  integral = None ; has_reader = false; parser_weak_kind = WeakKindStrongPrefix; parser_kind_nz=Some true})]
    |> List.iter (fun (i, attrs) ->
      let i = with_dummy_range (to_ident' i) in
      add_global e i (nullary_decl i) (Inl attrs))
  in
  let _operators =
    [ ("is_range_okay", { macro_arguments_t=[tuint32;tuint32;tuint32]; macro_result_t=tbool; macro_defn_t = None}) ]
    |> List.iter (fun (i, d) ->
        let i = with_dummy_range (to_ident' i) in
        add_global e i (nullary_decl i) (Inr d))
  in
  e

let get_exported_decls ge mname =
  H.fold (fun k (d, _) (exported_decls, private_decls) ->
    if not (k.modul_name = Some mname)
    then exported_decls, private_decls
    else if d.d_exported
         then k::exported_decls, private_decls
         else exported_decls, k::private_decls) ge.ge_h ([], [])

let finish_module ge mname e_and_p =
  e_and_p |> snd |> List.iter (H.remove ge.ge_h);
  ge
