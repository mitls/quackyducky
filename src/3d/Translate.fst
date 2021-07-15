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
module Translate
(* This module translates type definitions from the source Ast
   to types, parsers and validators in the Target language *)
open Ast
module A = Ast
module B = Binding
module T = Target
module H = Hashtable
module TS = TypeSizes
open FStar.All
open FStar.Pervasives

noeq
type global_env = {
  benv:B.global_env;
  size_env: TS.env_t;
  has_reader: H.t ident' bool;
  parser_kind_nz: H.t ident' bool;
  parser_weak_kind: H.t ident' A.weak_kind;
  parser_kind_is_constant_size: H.t ident' bool;
}

let has_reader (env:global_env) (id:A.ident) : ML bool =
  if B.has_reader env.benv id
  then true
  else Some? (H.try_find env.has_reader id.v)

let add_reader (env:global_env) (id:A.ident) : ML unit =
  H.insert env.has_reader id.v true

let parser_kind_nz (env:global_env) (id:A.ident) : ML bool =
  match H.try_find env.parser_kind_nz id.v with
  | Some b -> b
  | None ->
    match B.parser_kind_nz env.benv id with
    | Some b -> b
    | None ->
      failwith (Printf.sprintf "Type %s has an unknown parser kind" (ident_to_string id))

let parser_weak_kind (env:global_env) (id:A.ident) : ML A.weak_kind =
  match H.try_find env.parser_weak_kind id.v with
  | Some b -> b
  | None ->
    match B.parser_weak_kind env.benv id with
    | Some b -> b
    | None ->
      failwith (Printf.sprintf "Type %s has an unknown weak kind" (ident_to_string id))

let parser_kind_is_constant_size
  (env: global_env) (id: A.ident)
: ML bool
= 
  match H.try_find env.parser_kind_is_constant_size id.v with
  | Some b -> b
  | None ->
    match TS.size_of_typename env.size_env id with
    | TS.Fixed _ -> true
    | _ -> false

let add_parser_kind_is_constant_size (genv:global_env) (id:A.ident) (is_constant_size:bool) =
  H.insert genv.parser_kind_is_constant_size id.v is_constant_size

/// gensym (top-level effect, safe to ignore)
#push-options "--warn_error -272"
let gen_ident : option string -> St ident =
  let open FStar.ST in
  let ctr : ref int = alloc 0 in
  let next base_name_opt =
    let v = !ctr in
    ctr := v + 1;
    let id =
      match base_name_opt with
      | None -> Printf.sprintf "_x_%d" v
      | Some n -> Printf.sprintf "_%s_%d" n v
    in
    with_dummy_range (to_ident' id)
  in
  next
#pop-options

let underscore_ident = with_dummy_range (to_ident' "_")

(** Some utilities **)
let mk_lam (f:(A.ident -> ML 'a)) : ML (T.lam 'a) =
  let x = gen_ident None in
  Some x, f x

let map_lam (x:T.lam 'a) (g: 'a -> ML 'b) : ML (T.lam 'b) =
  fst x, g (snd x)

let mk_parser k t typename fieldname p = T.({
  p_kind = k;
  p_typ = t;
  p_parser = p;
  p_typename = typename;
  p_fieldname = fieldname
})

// Kind constructors
let pk_return = T.({
  pk_kind = PK_return;
  pk_nz = false;
  pk_weak_kind = WeakKindStrongPrefix;
})
let pk_impos = T.({
  pk_kind = PK_impos;
  pk_nz = true;
  pk_weak_kind = WeakKindStrongPrefix;
})
let pk_base id nz wk = T.({
  pk_kind = PK_base id;
  pk_weak_kind = wk;
  pk_nz = nz
})
let pk_list = T.({
  pk_kind = PK_list;
  pk_weak_kind = WeakKindStrongPrefix;
  pk_nz = false
})
let pk_t_at_most = T.({
  pk_kind = PK_t_at_most;
  pk_weak_kind = WeakKindStrongPrefix;
  pk_nz = false
})
let pk_t_exact = T.({
  pk_kind = PK_t_exact;
  pk_weak_kind = WeakKindStrongPrefix;
  pk_nz = false
})
let pk_string = T.({
  pk_kind = PK_string;
  pk_weak_kind = WeakKindStrongPrefix;
  pk_nz = true
})
let pk_filter k = T.({
  pk_kind = PK_filter k;
  pk_weak_kind = k.pk_weak_kind;
  pk_nz = k.pk_nz
})
let pk_and_then k1 k2 = T.({
  pk_kind = PK_and_then k1 k2;
  pk_weak_kind = k2.pk_weak_kind;
  pk_nz = k1.pk_nz || k2.pk_nz
})
let pk_glb k1 k2 = T.({
  pk_kind = PK_glb k1 k2;
  pk_weak_kind = weak_kind_glb k1.pk_weak_kind k2.pk_weak_kind;
  pk_nz = k1.pk_nz && k2.pk_nz
})

let false_typ = T.T_false
let unit_typ =
    T.T_app (with_dummy_range (to_ident' "unit")) []
let unit_val =
    T.(mk_expr (App (Ext "()") []))
let unit_parser =
    let unit_id = with_dummy_range (to_ident' "unit") in
    mk_parser pk_return unit_typ unit_id "none" (T.Parse_return unit_val)
let pair_typ t1 t2 =
    T.T_app (with_dummy_range (to_ident' "tuple2")) [Inl t1; Inl t2]
let pair_value x y =
    T.Record (with_dummy_range (to_ident' "tuple2"))
             [(with_dummy_range (to_ident' "fst"), T.mk_expr (T.Identifier x));
              (with_dummy_range (to_ident' "snd"), T.mk_expr (T.Identifier y))]
let pair_parser n1 p1 p2 =
    let open T in
    let pt = pair_typ p1.p_typ p2.p_typ in
    let t_id = with_dummy_range (to_ident' "tuple2") in
    mk_parser (pk_and_then p1.p_kind p2.p_kind)
              pt
              t_id
              "none"
              (Parse_pair n1 p1 p2)
let dep_pair_typ t1 (t2:(A.ident & T.typ)) : T.typ =
    T.T_dep_pair t1 t2
let dep_pair_value x y : T.expr =
    T.mk_expr
      (T.Record (with_dummy_range (to_ident' "dtuple2"))
                [(with_dummy_range (to_ident' "fst"), T.mk_expr (T.Identifier x));
                 (with_dummy_range (to_ident' "snd"), T.mk_expr (T.Identifier y))])
let dep_pair_parser n1 p1 (p2:A.ident & T.parser) =
  let open T in
  let t = T_dep_pair p1.p_typ (fst p2, (snd p2).p_typ) in
  let t_id = with_dummy_range (to_ident' "dtuple2") in
  mk_parser
      (pk_and_then p1.p_kind (snd p2).p_kind) 
      t
      t_id
      "none"
      (Parse_dep_pair n1 p1 (Some (fst p2), snd p2))
let dep_pair_with_refinement_parser n1 p1 (e:T.lam T.expr) (p2:A.ident & T.parser) =
  let open T in
  let t1 = T_refine p1.p_typ e in
  let t = T_dep_pair t1 (fst p2, (snd p2).p_typ) in
  let k1 = pk_filter p1.p_kind in
  let t_id = with_dummy_range (to_ident' "dtuple2") in
  mk_parser
      (pk_and_then k1 (snd p2).p_kind)
      t
      t_id
      "none"
      (Parse_dep_pair_with_refinement n1 p1 e (Some (fst p2), snd p2))
let dep_pair_with_refinement_and_action_parser n1 p1 (e:T.lam T.expr) (a:T.lam T.action) (p2:A.ident & T.parser) =
  let open T in
  let t1 = T_refine p1.p_typ e in
  let t = T_dep_pair t1 (fst p2, (snd p2).p_typ) in
  let k1 = pk_filter p1.p_kind in
  let t_id = with_dummy_range (to_ident' "dtuple2") in  
  mk_parser
      (pk_and_then k1 (snd p2).p_kind)
      t
      t_id
      "none"
      (Parse_dep_pair_with_refinement_and_action n1 p1 e a (Some (fst p2), snd p2))
let dep_pair_with_action_parser p1 (a:T.lam T.action) (p2:A.ident & T.parser) =
  let open T in
  let t1 = p1.p_typ in
  let t = T_dep_pair t1 (fst p2, (snd p2).p_typ) in
  let k1 = p1.p_kind in
  let t_id = with_dummy_range (to_ident' "dtuple2") in
  mk_parser
      (pk_and_then k1 (snd p2).p_kind)
      t
      t_id
      "none"
      (Parse_dep_pair_with_action p1 a (Some (fst p2), snd p2))
let translate_op : A.op -> ML T.op = 
  let force_topt (o:option A.integer_type) 
    : ML integer_type
    = match o with
      | None -> failwith (Printf.sprintf "Unelaborated integer operator")
      | Some t -> t
  in
  fun op ->
  match op with
  | Eq -> T.Eq
  | Neq -> T.Neq
  | And -> T.And
  | Or -> T.Or
  | Not -> T.Not
  | Plus topt -> T.Plus (force_topt topt)
  | Minus topt -> T.Minus (force_topt topt)
  | Mul topt -> T.Mul (force_topt topt)
  | Division topt -> T.Division (force_topt topt)
  | Remainder topt -> T.Remainder (force_topt topt)
  | BitwiseAnd topt -> T.BitwiseAnd (force_topt topt)
  | BitwiseXor topt -> T.BitwiseXor (force_topt topt)
  | BitwiseOr topt -> T.BitwiseOr (force_topt topt)
  | BitwiseNot topt -> T.BitwiseNot (force_topt topt)
  | ShiftRight topt -> T.ShiftRight (force_topt topt)
  | ShiftLeft topt -> T.ShiftLeft (force_topt topt)
  | LT topt -> T.LT (force_topt topt)
  | GT topt -> T.GT (force_topt topt)
  | LE topt -> T.LE (force_topt topt)
  | GE topt -> T.GE (force_topt topt)
  | IfThenElse -> T.IfThenElse
  | BitFieldOf i -> T.BitFieldOf i
  | Cast (Some from) to -> T.Cast from to
  | Ext s -> T.Ext s
  | Cast None _
  | SizeOf -> failwith (Printf.sprintf "Operator `%s` should have been eliminated already"
                                  (Ast.print_op op))

let rec translate_expr (e:A.expr) : ML T.expr =
  (match e.v with
   | Constant c -> T.Constant c
   | Identifier i -> T.Identifier i
   | App op exprs -> T.App (translate_op op) (List.map translate_expr exprs)
   | This -> failwith "`this` should have been eliminated already"),
  e.A.range

let rec translate_typ (t:A.typ) : ML T.typ =
  match t.v with
  | Pointer t ->
    let t' = translate_typ t in
    T.T_pointer t'
  | Type_app hd args ->
    T.T_app hd (List.map (fun x -> Inr (translate_expr x)) args)

let has_entrypoint (l:list A.attribute) =
  List.tryFind (function A.Entrypoint -> true | _ -> false) l
  |> Some?

let translate_typedef_name (tdn:A.typedef_names) (params:list Ast.param) : ML T.typedef_name =
  let params = List.map (fun (t, id, _) -> id, translate_typ t) params in //TODO: ignoring qualifier
  let open T in
  { td_name = tdn.typedef_name;
    td_params = params;
    td_entrypoint = has_entrypoint tdn.typedef_attributes }

let make_enum_typ (t:T.typ) (ids:list ident) =
  let refinement i =
    let x = T.Identifier i in
    List.fold_right
      (fun y e -> T.mk_expr (T.App T.Or [T.mk_expr (T.App T.Eq [T.mk_expr x; T.mk_expr (T.Identifier y);]); e]))
      ids
      (T.mk_expr (T.Constant (Bool false)))
  in
  T.T_refine t (mk_lam refinement)

let rec has_refinement_and_action (t:T.typ)
  : ML (option (T.typ &
                option (T.lam T.expr) &
                option (either T.action (T.lam T.action)) &
                option comments))
  = let open T in
    match t with
    | T_refine t e -> Some (t, Some e, None, None)
    | T_with_action t a ->
      begin
      match has_refinement_and_action t with
      | None ->
        Some(t, None, Some (Inl a), None)
      | Some (t, e, None, c) ->
        Some (t, e, Some (Inl a), c)
      | Some (_, _, Some _, _) ->
        failwith "Nested actions: impossible"
      end
    | T_with_dep_action t a ->
      begin
      match has_refinement_and_action t with
      | None ->
        Some (t, None, Some (Inr a), None)
      | Some (t, e, None, c) ->
        Some (t, e, Some (Inr a), c)
      | Some (_, _, Some _, _) ->
        failwith "Nested actions: impossible"
      end
    | T_with_comment t c ->
      begin
      match has_refinement_and_action t with
      | None -> None
      | Some (t, e, a, None) -> 
        Some (t, e, a, Some c)
      | Some (t, e, a, Some c') ->
        Some (t, e, a, Some (c @ c'))
      end
    | _ -> None

let maybe_add_comment t copt =
    match copt with
    | None -> t
    | Some c -> T.T_with_comment t c

let rec parse_typ (env:global_env)
                  (typename: A.ident) 
                  (fieldname:string)
                  (t:T.typ) : ML T.parser =
  let open T in
  let extend_fieldname e = Printf.sprintf "%s.%s" fieldname e in
  match t with
  | T_false ->
    mk_parser pk_impos T_false typename fieldname Parse_impos

  | T.T_app {v={name="nlist"}} [Inr e; Inl t] ->
    let pt = parse_typ env typename (extend_fieldname "element") t in
    mk_parser pk_list
              t
              typename
              fieldname
              (T.Parse_nlist e pt)

  | T.T_app {v={name="t_at_most"}} [Inr e; Inl t] ->
    let pt = parse_typ env typename (extend_fieldname "element") t in
    mk_parser pk_t_at_most
              t
              typename
              fieldname
              (T.Parse_t_at_most e pt)

  | T.T_app {v={name="t_exact"}} [Inr e; Inl t] ->
    let pt = parse_typ env typename (extend_fieldname "element") t in
    mk_parser pk_t_exact
              t
              typename
              fieldname
              (T.Parse_t_exact e pt)

  | T.T_app {v={name="cstring"}} [Inl t; Inr e] ->
    let pt = parse_typ env typename (extend_fieldname "element") t in
    mk_parser pk_string
              t
              typename
              fieldname
              (T.Parse_string pt e)

  | T.T_app hd args ->
    mk_parser (pk_base hd (parser_kind_nz env hd) (parser_weak_kind env hd))
              t
              typename
              fieldname
              (T.Parse_app hd args)

  | T.T_refine t_base refinement ->
    let base = parse_typ env typename fieldname t_base in
    let refined = T.Parse_refinement typename base refinement in
    mk_parser (pk_filter base.p_kind) t typename (extend_fieldname "refinement") refined

  | T.T_if_else e t1 t2 ->
    let p1 = parse_typ env typename fieldname t1 in
    let p2 = parse_typ env typename fieldname t2 in
    let k, p1, p2 =
      if parser_kind_eq p1.p_kind p2.p_kind
      then p1.p_kind, p1, p2
      else let k = pk_glb p1.p_kind p2.p_kind in
           k,
           mk_parser k t1 typename (extend_fieldname "case_left") (Parse_weaken_right p1 p2.p_kind),
           mk_parser k t2 typename (extend_fieldname "case_right") (Parse_weaken_left p2 p1.p_kind)
    in
    mk_parser k t typename fieldname (Parse_if_else e p1 p2)

  | T.T_dep_pair t1 (x, t2) ->
    dep_pair_parser typename (parse_typ env typename (extend_fieldname "first") t1) 
                             (x, parse_typ env typename (extend_fieldname "second") t2)

  | T.T_with_action _ _
  | T.T_with_dep_action _ _ ->
    let ref_action = has_refinement_and_action t in
    begin
    match ref_action with
    | None
    | Some (_, _, None, _) ->
      failwith "Impossible"
    | Some (t, None, Some (Inl a), copt) ->
      let t = maybe_add_comment t copt in
      let p = parse_typ env typename (extend_fieldname "base") t in
      mk_parser p.p_kind t typename fieldname (T.Parse_with_action typename p a)
    | Some (t, None, Some (Inr a), copt) ->
      let t = maybe_add_comment t copt in    
      let p = parse_typ env typename (extend_fieldname "base") t in
      mk_parser p.p_kind t typename fieldname (T.Parse_with_dep_action typename p a)
    | Some (t, Some r, Some (Inl a), copt) ->
      let t = maybe_add_comment t copt in        
      let p = parse_typ env typename (extend_fieldname "base") t in
      mk_parser (pk_filter p.p_kind)
                (T.T_refine t r)
                typename
                fieldname
                (T.Parse_refinement_with_action typename p r (Some underscore_ident, a))
    | Some (t, Some r, Some (Inr a), copt) ->
      let t = maybe_add_comment t copt in            
      let p = parse_typ env typename (extend_fieldname "base") t in
      mk_parser (pk_filter p.p_kind)
                (T.T_refine t r)
                typename
                fieldname
                (T.Parse_refinement_with_action typename p r a)
    end
  | T.T_with_comment t c ->
    let p = parse_typ env typename fieldname t in
    { p with p_parser = T.Parse_with_comment p c }

  | T.T_pointer _ ->
    failwith "No parsers for pointer types"

let pv ar p v = T.({
  v_allow_reading = ar;
  v_parser = p;
  v_validator = v
})

let rec read_typ (env:global_env) (t:T.typ) : ML (option T.reader) =
  let open T in
  match t with
  | T_app ({v={name="UINT8"}}) [] -> Some Read_u8
  | T_app ({v={name="UINT16"}}) [] -> Some Read_u16
  | T_app ({v={name="UINT32"}}) [] -> Some Read_u32
  | T.T_app hd args ->
    if has_reader env hd
    then Some (T.Read_app hd args)
    else None
  | T.T_with_comment t _
  | T.T_with_action t _ ->
    read_typ env t
  | _ -> None

let make_reader (env:global_env) (t:T.typ) : ML T.reader =
  match read_typ env t with
  | None ->
    failwith (Printf.sprintf "Unsupported reader type: %s\n" (T.print_typ "" t))  //AR: TODO: needs a module name
  | Some r ->
    r

let rec translate_action (a:A.action) : ML T.action =
  let translate_atomic_action (a:A.atomic_action)
    : ML T.atomic_action
    = match a with
      | Action_return e ->
        T.Action_return (translate_expr e)
      | Action_abort ->
        T.Action_abort
      | Action_field_pos ->
        T.Action_field_pos
      | Action_field_ptr ->
        T.Action_field_ptr
      | Action_deref i ->
        T.Action_deref i
      | Action_assignment lhs rhs ->
        T.Action_assignment lhs (translate_expr rhs)
      | Action_call f args ->
        T.Action_call f (List.map translate_expr args)
  in
  match a.v with
  | Atomic_action a ->
    T.Atomic_action (translate_atomic_action a)

  | Action_seq hd tl ->
    T.Action_seq (translate_atomic_action hd) (translate_action tl)

  | Action_ite hd then_ (Some else_) ->
    T.Action_ite (translate_expr hd) (translate_action then_) (translate_action else_)

  | Action_ite hd then_ None ->
    T.Action_ite (translate_expr hd)
                 (translate_action then_)
                 (T.Atomic_action (T.Action_return (T.mk_expr (T.Constant A.Unit))))

  | Action_let i a k ->
    T.Action_let i (translate_atomic_action a) (translate_action k)

let rec parser_is_constant_size_without_actions
  (env: global_env)
  (p: T.parser)
: ML bool
= match p.T.p_parser with
  | T.Parse_return _
  | T.Parse_impos
    -> true
  | T.Parse_app hd _
    -> parser_kind_is_constant_size env hd
  | T.Parse_nlist array_size parse_elem
    -> begin match fst array_size with
      | T.Constant (A.Int _ array_size) -> parser_is_constant_size_without_actions env parse_elem
      | _ -> false
      end
  | T.Parse_pair _ hd tl
    -> if parser_is_constant_size_without_actions env hd
      then parser_is_constant_size_without_actions env tl
      else false
  | T.Parse_dep_pair _ parse_key (_, parse_value)
  | T.Parse_dep_pair_with_refinement _ parse_key _ (_, parse_value)
    -> (* the lambda identifier is not global, because the 3d syntax does not allow higher-order types *)
      if parser_is_constant_size_without_actions env parse_key
      then parser_is_constant_size_without_actions env parse_value
      else false
  | T.Parse_t_at_most _ _
  | T.Parse_t_exact _ _  
  | T.Parse_dep_pair_with_action _ _ _
  | T.Parse_dep_pair_with_refinement_and_action _ _ _ _ _
  | T.Parse_refinement_with_action _ _ _ _
  | T.Parse_with_dep_action _ _ _
  | T.Parse_with_action _ _ _
  | T.Parse_if_else _ _ _
  | T.Parse_string _ _
    -> false
  | T.Parse_map p _
  | T.Parse_refinement _ p _
  | T.Parse_weaken_left p _
  | T.Parse_weaken_right p _  
  | T.Parse_with_comment p _
    -> parser_is_constant_size_without_actions env p

let unknown_type_ident = 
  let open Ast in
  let id = {
    modul_name = None;
    name = "<unknown>"
  } in
  with_range id dummy_range

let rec make_validator (env:global_env) (p:T.parser) : ML T.validator =
  let open T in
  let with_error_handler v =
    pv v.v_allow_reading
       v.v_parser
       (Validate_with_error_handler p.p_typename p.p_fieldname v)
  in
  match p.p_parser with
  | Parse_impos ->
    with_error_handler
      (pv true p Validate_impos)

  | Parse_app hd args ->
    with_error_handler
      (pv (has_reader env hd) p (Validate_app hd args))

  | Parse_nlist n p ->
    with_error_handler
      (if parser_is_constant_size_without_actions env p
       then pv false p (Validate_nlist_constant_size_without_actions n (make_validator env p))
       else pv false p (Validate_nlist n (make_validator env p)))

  | Parse_t_at_most n p ->
    with_error_handler
      (pv false p (Validate_t_at_most n (make_validator env p)))

  | Parse_t_exact n p ->
    with_error_handler
      (pv false p (Validate_t_exact n (make_validator env p)))

  | Parse_return e ->
    pv true p Validate_return

  | Parse_pair n1 p1 p2 ->
     pv false p (Validate_pair n1 (make_validator env p1)
                                  (make_validator env p2))

  | Parse_dep_pair n1 p1 k ->
     pv false p (Validate_dep_pair
                     n1
                     (make_validator env p1)
                     (make_reader env p1.p_typ)
                     (map_lam k (make_validator env)))

  | Parse_dep_pair_with_refinement n1 p1 e k ->
    let p1_is_constant_size_without_actions = parser_is_constant_size_without_actions env p1 in
    pv false p (Validate_dep_pair_with_refinement
                      p1_is_constant_size_without_actions
                      n1
                      (make_validator env p1)
                      (make_reader env p1.p_typ)
                      e
                      (map_lam k (make_validator env)))

  | Parse_dep_pair_with_action p1 a k ->
    pv false p (Validate_dep_pair_with_action
                       (make_validator env p1)
                       (make_reader env p1.p_typ)
                       a
                       (map_lam k (make_validator env)))

  | Parse_dep_pair_with_refinement_and_action n1 p1 e a k ->
    let p1_is_constant_size_without_actions = parser_is_constant_size_without_actions env p1 in
    pv false p (Validate_dep_pair_with_refinement_and_action
                     p1_is_constant_size_without_actions
                     n1
                     (make_validator env p1)
                     (make_reader env p1.p_typ)
                     e
                     a
                     (map_lam k (make_validator env)))

  | Parse_map p1 f ->
    pv false p (Validate_map (make_validator env p1) f)

  | Parse_refinement n1 p1 f ->
    with_error_handler 
      (pv false p (Validate_refinement n1 
                                       (make_validator env p1)
                                       (make_reader env p1.p_typ)
                                       f))

  | Parse_refinement_with_action n1 p1 f a ->
    with_error_handler 
      (pv false p (Validate_refinement_with_action n1 
                                                   (make_validator env p1)
                                                   (make_reader env p1.p_typ)
                                                   f 
                                                   a))

  | Parse_with_action n1 p a ->
    with_error_handler
      (pv false p (Validate_with_action n1 (make_validator env p) a))

  | Parse_with_dep_action n1 p a ->
    with_error_handler
      (pv false p (Validate_with_dep_action n1 
                     (make_validator env p)
                     (make_reader env p.p_typ)
                     a))

  | Parse_weaken_left p1 k ->
    let v1 = make_validator env p1 in
    pv v1.v_allow_reading p (Validate_weaken_left v1 k)

  | Parse_weaken_right p1 k ->
    let v1 = make_validator env p1 in
    pv v1.v_allow_reading p (Validate_weaken_right v1 k)

  | Parse_if_else e p1 p2 ->
    pv false p (Validate_if_else e (make_validator env p1) (make_validator env p2))

  | Parse_with_comment p c ->
    let v = make_validator env p in
    pv v.v_allow_reading p (Validate_with_comment v c)

  | Parse_string elem zero ->
    with_error_handler
      (pv false p (Validate_string (make_validator env elem) (make_reader env elem.p_typ) zero))

// x:t1;
// t2;
// t3;
// y:t4;
// t5;
// t6

// (x <-- parse_t1 ;
//  (parse_t2 ;;
//   parse_t3 ;;
//   (y <-- parse_t4;
//     ((parse_t5 ;;
//       parse_t6) `map` (fun x56 -> y, x56))))
//  `map` (fun x_2_3_4_5_6 -> {x = x; y .... }))

let make_zero (r: range) (t: typ) : ML T.expr =
  let it = typ_as_integer_type t in
  (T.Constant (Int it 0), r)

let translate_field (f:A.field) : ML T.struct_field =
    let sf = f.v in
    let t = translate_typ sf.field_type in
    let t =
        let mk_at_most t e : ML T.typ =
          let e = translate_expr e in
          T.T_app (with_range (to_ident' "t_at_most") sf.field_type.range) [Inr e; Inl t]
        in
        match sf.field_array_opt with
        | FieldScalar -> t
        | FieldArrayQualified (e, ByteArrayByteSize)
        | FieldArrayQualified (e, ArrayByteSize) ->
          let e = translate_expr e in
          T.T_app (with_range (to_ident' "nlist") sf.field_type.range) [Inr e; Inl t]
        | FieldArrayQualified (e, ArrayByteSizeAtMost) ->
          mk_at_most t e
        | FieldArrayQualified (e, ArrayByteSizeSingleElementArray) ->
          let e = translate_expr e in
          T.T_app (with_range (to_ident' "t_exact") sf.field_type.range) [Inr e; Inl t]
        | FieldString sz ->
          let r = sf.field_type.range in
          let str = T.T_app (with_range (to_ident' "cstring") r) [Inl t; Inr (make_zero r sf.field_type)] in
          begin match sz with
          | None -> str
          | Some e -> mk_at_most str e
          end
    in
    let t =
      match sf.field_constraint with
      | None -> t
      | Some e ->
        T.T_refine t (Some sf.field_ident, translate_expr e)
    in
    let t =
      match sf.field_action with
      | None -> t
      | Some (a, false) ->
        T.T_with_action t (translate_action a)
      | Some (a, _) ->
        T.T_with_dep_action t (Some sf.field_ident, translate_action a)
    in
    let t : T.typ =
      match f.comments with
      | [] ->
        let c =
          Printf.sprintf "Validating field %s"
            (print_ident sf.field_ident)
        in
        T.T_with_comment t [c]
      | c -> T.T_with_comment t c
    in
    if T.T_pointer? t
    then failwith "Type-checking should have forbidden fields with pointer types"
    else
      T.({sf_dependence=sf.field_dependence;
          sf_ident=sf.field_ident;
          sf_typ=t})

let nondep_group = list T.field
let grouped_fields = list (either T.field nondep_group)
let print_grouped_fields (gfs:grouped_fields) : ML string =
  Printf.sprintf "[%s]"
    (let s = 
      List.Tot.map 
        (fun (f:either T.field nondep_group) -> 
          match f with
          | Inl f -> ident_to_string f.T.sf_ident
          | Inr l -> 
            Printf.sprintf "[%s]" 
              (let s = List.Tot.map (fun f -> ident_to_string f.T.sf_ident) l in
               String.concat "; " s))
        gfs
    in
    String.concat "; " s)
let make_grouped_fields (fs:list T.field) : ML grouped_fields =
  let open T in
  let add_run (out, run) : grouped_fields =
      match run with
      | [] -> out
      | _ -> Inr run :: out
  in
  let extend_run sf (run:nondep_group) : nondep_group =
    sf::run
  in
  let group_non_dependent_fields
          (sf:struct_field)
          (out, run)
    : grouped_fields & nondep_group
    = match out, run with
      | [], [] -> 
        //last field is always non-dependent
        //even though its sf_dependence flag may be sets
        //e.g., because it a field result from coalescing multiple bitfield
        //which may themselves be dependent
        //See BitFields0.3d for a test case
        out, extend_run sf run
      | _ -> 
        if sf.sf_dependence
        then Inl sf::add_run (out, run), []
        else out, extend_run sf run
  in
  let gfs : grouped_fields =
    add_run (List.fold_right group_non_dependent_fields fs ([], []))
  in
  gfs


let parse_grouped_fields (env:global_env) (typename:A.ident) (gfs:grouped_fields)
  : ML T.parser
  = let open T in
    let parse_typ (fieldname:A.ident) = parse_typ env typename Ast.(fieldname.v.name) in
    let rec aux (gfs:grouped_fields) : ML parser =
      match gfs with
      | [] ->
        failwith "Unexpected empty list of fields"

      | Inl sf::gfs ->
        //This a dependent pair, gfs cannot be empty
        let get_action = function
          | Inl a -> (Some sf.sf_ident, a)
          | Inr a -> a
        in
        begin
        match has_refinement_and_action sf.sf_typ with
        | None ->
          dep_pair_parser
            sf.sf_ident
            (parse_typ sf.sf_ident sf.sf_typ)
            (sf.sf_ident, aux gfs)
            
        | Some (_, None, None, copt) ->
          dep_pair_parser
            sf.sf_ident
            (parse_typ sf.sf_ident (maybe_add_comment sf.sf_typ copt))
            (sf.sf_ident, aux gfs)

        | Some (t, Some e, None, copt) ->
          dep_pair_with_refinement_parser
            sf.sf_ident
            (parse_typ sf.sf_ident (maybe_add_comment t copt))
            e
            (sf.sf_ident, aux gfs)

        | Some (t, Some e, Some a, copt) ->
          dep_pair_with_refinement_and_action_parser
            sf.sf_ident
            (parse_typ sf.sf_ident (maybe_add_comment t copt))
            e
            (get_action a)
            (sf.sf_ident, aux gfs)

        | Some (t, None, Some a, copt) ->
          dep_pair_with_action_parser
            (parse_typ sf.sf_ident (maybe_add_comment t copt))
            (get_action a)
            (sf.sf_ident, aux gfs)
        end

      | [Inr gf] ->
        let rec aux (gf:nondep_group)
          : ML T.parser
          = match gf with
            | [] ->
              failwith "Unexpected empty non-dep group"
            | [sf] ->
               parse_typ sf.sf_ident sf.sf_typ
            | sf::sfs ->
              pair_parser
                sf.sf_ident
                (parse_typ sf.sf_ident sf.sf_typ)
                (aux sfs)
        in
        aux gf

      | Inr gf::gfs ->
        List.fold_right
          (fun (sf:struct_field) (p_tl:parser) ->
            pair_parser
              sf.sf_ident
              (parse_typ sf.sf_ident sf.sf_typ)
              p_tl)
          gf
          (aux gfs)
    in
    aux gfs

let parse_fields (env:global_env) (tdn:T.typedef_name) (fs:list T.field)
  : ML T.parser =
  let open T in
  let td_name, td_params = tdn.td_name, tdn.td_params in
  let gfs = make_grouped_fields fs in
  // FStar.IO.print_string
  //   (FStar.Printf.sprintf "parse_fields (tdn = %s), fields=[%s], grouped_fields=%s\n"
  //     tdn.td_name.v 
  //     (List.map (fun x -> x.sf_ident.v) fs |> String.concat ", ")
  //     (print_grouped_fields gfs));
  let p = parse_grouped_fields env tdn.td_name gfs in
  p

let make_tdn (i:A.ident) =
  {
    typedef_name = i;
    typedef_abbrev = with_dummy_range (to_ident' "");
    typedef_ptr_abbrev = with_dummy_range (to_ident' "");
    typedef_attributes = []
  }

let env_t = list (A.ident * T.typ)

let check_in_global_env (env:global_env) (i:A.ident) =
  let _ = B.lookup_expr_name (B.mk_env env.benv) i in ()

let maybe_gen_ident (env:global_env) (s:string) : A.ident =
  with_dummy_range (to_ident' s)

let type_in_local_env (i:A.ident) (env:env_t)
  : ML (option T.typ) =
    match List.tryFind (fun (i', _) -> A.(i.v = i'.v)) env with
    | None -> None
    | Some (_, t) -> Some t

let rec free_vars_expr (genv:global_env)
                       (env:env_t)
                       (out:env_t)
                       (e:T.expr)
  : ML env_t
  = let open T in
    match fst e with
    | Constant _ -> out
    | Identifier i ->
      if Some? (type_in_local_env i out) then out
      else begin
        match type_in_local_env i env with
        | None ->
          check_in_global_env genv i;
          out
        | Some t -> (i, t) :: out
      end
    | App hd args ->
      List.fold_left (free_vars_expr genv env) out args
    | Record _ fields ->
      List.fold_left (fun out (_, e) -> free_vars_expr genv env out e) out fields

let with_attrs (d:T.decl') (h:bool) (e:bool) (i:bool) (c:list string)
  : T.decl
  = d, T.({ is_hoisted = h; is_exported = e; should_inline = i; comments = c } )

let with_comments (d:T.decl') (e:bool) (c:list string)
  : T.decl
  = d, T.({ is_hoisted = false; is_exported = e; should_inline = false; comments = c } )

let rec hoist_typ
          (fn:string)
          (genv:global_env)
          (env:env_t)
          (t:T.typ)
  : ML (list T.decl & T.typ)
  = let open T in
    match t with
    | T_false -> [], t
    | T_app _ _ -> [], t
    | T_dep_pair t1 (x, t2) ->
      let ds, t1 = hoist_typ fn genv env t1 in
      let ds', t2 = hoist_typ fn genv ((x, t1)::env) t2 in
      ds@ds', T_dep_pair t1 (x, t2)
    | T_refine t1 (Some x, e) ->
      let ds, t1 = hoist_typ fn genv env t1 in
      // let fvs = env in //free_vars_expr genv env [] e in
      let params = List.rev env in
      let args = (List.map (fun (x, _) -> Identifier x) params) in
      let def, app =
        let params = params @ [x,t1] in
        let args = args in //@ [Identifier x] in
        let filter_name = fn ^ "_filter" in
        let id = maybe_gen_ident genv filter_name in
        let result_type = T_app (with_dummy_range (to_ident' "bool")) [] in
        let body = e in
        let app = App (Ext id.A.v.name) (List.Tot.map (fun arg -> T.mk_expr arg) args) in
        (id, params, result_type, body),
        T.mk_expr app
      in
      let d = Definition def in
      let t = T_refine t1 (None, app) in
      ds@[with_attrs d true false true []],  //hoisted, not exported, inlineable
      t

    | T_refine t1 (None, e) ->
      let ds, t1 = hoist_typ fn genv env t1 in
      ds, T_refine t1 (None, e)

    | T_if_else e t f ->
      let d1, t = hoist_typ fn genv env t in
      let d2, f = hoist_typ fn genv env f in
      d1@d2, T_if_else e t f

    | T_with_action t a ->
      let d, t = hoist_typ fn genv env t in
      d, T_with_action t a

    | T_with_dep_action t a ->
      let d, t = hoist_typ fn genv env t in
      d, T_with_dep_action t a

    | T_with_comment t c ->
      let d, t = hoist_typ fn genv env t in
      d, T_with_comment t c

    | T_pointer _ ->
      [], t

let add_parser_kind_nz (genv:global_env) (id:A.ident) (nz:bool) (wk: weak_kind) =
  let _ = Options.debug_print_string
    (Printf.sprintf "For %s, adding parser kind %s\n"
      (ident_to_string id)
      (string_of_bool nz)) in
  H.insert genv.parser_weak_kind id.v wk;
  H.insert genv.parser_kind_nz id.v nz

let maybe_add_reader (genv:global_env)
                     (decl_name:_)
                     (t:T.typ)
  : ML (option T.reader)
  = let open T in
    let reader = read_typ genv t in
    let _ =
      if Some? reader
      then begin
        Options.debug_print_string (Printf.sprintf ">>>>>> Adding reader for %s with definition %s\n" (ident_to_string decl_name.td_name) (T.print_typ "" t));  //AR: TODO: needs a module name
        add_reader genv decl_name.td_name
     end
    in
    reader

let hoist_one_type_definition (should_inline:bool)
                              (genv:global_env) (env:env_t) (orig_tdn:T.typedef_name)
                              (prefix:string) (t:T.typ)
  : ML (T.decl & T.field_typ)
  =  let open T in
     let parse_typ = parse_typ genv in
     let type_name = prefix in //^ "_type" in
     let id = maybe_gen_ident genv type_name in
     let args = List.map (fun (x, _) -> Inr (T.mk_expr (Identifier x))) (List.rev env) in
     let tdef = T_app id args in
     let tdef =
       if should_inline
       then tdef
       else T_with_comment tdef
                           [Printf.sprintf "Field %s"
                             prefix]
      in
      let body = t in
      let comment = Printf.sprintf "    Internal helper function:\n        Validator for field %s\n        of type %s"
                                   prefix
                                   (ident_to_string orig_tdn.td_name) in
      let tdn = {
          td_name = id;
          td_params = List.rev env;
          td_entrypoint = false
      } in
      let t_parser = parse_typ orig_tdn.td_name type_name body in
      add_parser_kind_nz genv tdn.td_name t_parser.p_kind.pk_nz t_parser.p_kind.pk_weak_kind;
      add_parser_kind_is_constant_size genv tdn.td_name (parser_is_constant_size_without_actions genv t_parser);
      let reader = maybe_add_reader genv tdn body in
      let td = {
        decl_name = tdn;
        decl_typ = TD_abbrev body;
        decl_parser = t_parser;
        decl_validator = make_validator genv t_parser;
        decl_reader = reader;
      } in
      let td = Type_decl td in
      with_attrs td true false should_inline [comment],  //hoisted, not exported, should_inline
      tdef

let hoist_field (genv:global_env) (env:env_t) (tdn:T.typedef_name) (f:T.field)
  : ML (list T.decl & T.field)
  = let open T in
    let field_name = Printf.sprintf "%s_%s" (ident_name tdn.td_name) (ident_to_string f.sf_ident) in
    let d, t = hoist_typ field_name genv env f.sf_typ in
    let ref_action = has_refinement_and_action t in
    if (f.sf_dependence
     && Some? ref_action) //can't hoist it, otherwise we end up with double fetches
    || (match ref_action with
       | Some (_, Some _, Some (Inr _), _) -> //refinement and dependent action
         true
       | _ -> false)
    then let f = { f with sf_typ = t } in
         d, f
    else
      let td, tdef = hoist_one_type_definition false genv env tdn field_name t in
      let f = { f with sf_typ = tdef } in
      d@[td], f

let hoist_refinements (genv:global_env) (tdn:T.typedef_name) (fields:list T.field)
  : ML (list T.decl * list T.field)
  = let hoist_one_field edf (f:T.field)
        : ML _ =
        let open T in
        let (env, decls, fields) = edf in
        let decls', f = hoist_field genv env tdn f in
        let env = 
          if f.sf_dependence
          then (f.sf_ident, f.sf_typ)::env
          else env
        in
        env, decls@decls', f::fields
    in
    let _, decls, fields =
      List.fold_left
        hoist_one_field
        (List.rev tdn.T.td_params, [], [])
        fields
    in
    decls, List.rev fields

let translate_switch_case_type (genv:global_env) (tdn:T.typedef_name) (sw:Ast.switch_case)
  : ML (T.typ & list T.decl) =
  let sc, cases = sw in
  let sc = translate_expr sc in
  let env = List.rev tdn.T.td_params in
  let translate_one_case f : ML _ = 
    let sf = translate_field f in
    let decls, sfs = hoist_refinements genv tdn [sf] in
    let sf = List.hd sfs in
    decls, sf
  in
  let rest, default_t, decls =
    if List.length cases > 0
    then 
      let rest, last = List.splitAt (List.length cases - 1) cases in
      match last with
      | [DefaultCase f] ->
        let decls, sf = translate_one_case f in
        rest, sf.T.sf_typ, decls
      | _ -> 
        cases, T.T_false, []
    else
      cases, T.T_false, []
  in
  let t,decls,_ = List.fold_right
    (fun case (t_else, decls, n) ->
      match case with
      | DefaultCase _ -> failwith "Impossible"
      | Case e f ->
        let open T in
        let decls', sf = translate_one_case f in
        let guard = T.mk_expr (App Eq [sc; translate_expr e]) in
        let t = T_if_else guard sf.sf_typ t_else in
        let field_name = Printf.sprintf "%s_ite_%d" (ident_name tdn.td_name) n in
        let td, tdef = hoist_one_type_definition true genv env tdn field_name t in
        tdef, decls@decls'@[td], n + 1)
    rest
    (default_t, decls, 0)
  in
  t,
  decls

let translate_decl (env:global_env) (d:A.decl) : ML (list T.decl) =
  match d.d_decl.v with
  | ModuleAbbrev _ _ -> []
  | Define i None s ->
    failwith (Printf.sprintf "Untyped definition remains after elaboration: %s" (ident_to_string i))

  | Define i (Some t) s ->
    let t = translate_typ t in
    [with_comments (T.Definition (i, [], t, T.mk_expr (T.Constant s))) d.d_exported d.d_decl.comments]

  | TypeAbbrev t i ->
    let tdn = make_tdn i in
    let t = translate_typ t in
    let tdn = translate_typedef_name tdn [] in
    let p = parse_typ env i "" t in
    let open T in
    add_parser_kind_nz env tdn.td_name p.p_kind.pk_nz p.p_kind.pk_weak_kind;
    add_parser_kind_is_constant_size env tdn.td_name (parser_is_constant_size_without_actions env p);
    let reader = maybe_add_reader env tdn t in
    let td = {
        decl_name = tdn;
        decl_typ = TD_abbrev t;
        decl_parser = p;
        decl_validator = make_validator env p;
        decl_reader = reader;
    } in
    [with_comments (Type_decl td) d.d_exported A.(d.d_decl.comments)]

  | Enum t i ids ->
    let ids = Desugar.check_desugared_enum_cases ids in
    let tdn = make_tdn i in
    let typ = translate_typ t in
    let tdn = translate_typedef_name tdn [] in
    let refined_typ = make_enum_typ typ ids in
    let p = parse_typ env i "" refined_typ in
    let open T in
    add_parser_kind_nz env tdn.td_name p.p_kind.pk_nz p.p_kind.pk_weak_kind;
    add_parser_kind_is_constant_size env tdn.td_name (parser_is_constant_size_without_actions env p);
    let reader = maybe_add_reader env tdn refined_typ in
    let td = {
        decl_name = tdn;
        decl_typ = TD_abbrev refined_typ;
        decl_parser = p;
        decl_validator = make_validator env p;
        decl_reader = reader;
    } in
    [with_comments (Type_decl td) d.d_exported A.(d.d_decl.comments)]

  | Record tdn params _ ast_fields ->
    let tdn = translate_typedef_name tdn params in
    let fields = List.map translate_field ast_fields in
    let hoists, fields = hoist_refinements env tdn fields in
    let p = parse_fields env tdn fields in
    let open T in
    add_parser_kind_nz env tdn.td_name p.p_kind.pk_nz p.p_kind.pk_weak_kind;
    add_parser_kind_is_constant_size env tdn.td_name (parser_is_constant_size_without_actions env p);
    let decl_typ = TD_abbrev p.p_typ in
    let reader = maybe_add_reader env tdn p.p_typ in
    let td = {
          decl_name = tdn;
          decl_typ = decl_typ;
          decl_parser = p;
          decl_validator = make_validator env p;
          decl_reader = reader
    } in
    hoists @ [with_comments (Type_decl td) d.d_exported A.(d.d_decl.comments)]

  | CaseType tdn0 params switch_case ->
    let tdn = translate_typedef_name tdn0 params in
    let t, decls = translate_switch_case_type env tdn switch_case in
    let p = parse_typ env tdn0.typedef_name "" t in
    let open T in
    add_parser_kind_nz env tdn.td_name p.p_kind.pk_nz p.p_kind.pk_weak_kind;
    add_parser_kind_is_constant_size env tdn.td_name (parser_is_constant_size_without_actions env p);
    let reader = maybe_add_reader env tdn t in
    let td = {
        decl_name = tdn;
        decl_typ = TD_abbrev t;
          decl_parser = p;
          decl_validator = make_validator env p;
        decl_reader = reader;
    } in
    decls @ [with_comments (Type_decl td) d.d_exported A.(d.d_decl.comments)]

noeq
type translate_env = {
  t_has_reader: H.t ident' bool;
  t_parser_kind_nz: H.t ident' bool;
  t_parser_weak_kind: H.t ident' A.weak_kind;
  t_parser_kind_is_constant_size: H.t ident' bool;
}

let initial_translate_env () = {
  t_has_reader = H.create 0;
  t_parser_kind_nz = H.create 0;
  t_parser_weak_kind = H.create 0;
  t_parser_kind_is_constant_size = H.create 0; }

let translate_decls benv senv tenv ds =
  let env = {
    benv = benv;
    size_env = (B.mk_env benv, senv);
    has_reader = tenv.t_has_reader;
    parser_kind_nz = tenv.t_parser_kind_nz;
    parser_weak_kind = tenv.t_parser_weak_kind;
    parser_kind_is_constant_size = tenv.t_parser_kind_is_constant_size;
  } in
  List.collect (translate_decl env) ds,
  { tenv with t_has_reader = env.has_reader;
              t_parser_kind_nz = env.parser_kind_nz;
              t_parser_weak_kind = env.parser_weak_kind;
              t_parser_kind_is_constant_size = env.parser_kind_is_constant_size }

let finish_module en mname e_and_p =
  e_and_p |> snd |> List.iter (fun k ->
    H.remove en.t_has_reader k;
    H.remove en.t_parser_kind_nz k;
    H.remove en.t_parser_weak_kind k;
    H.remove en.t_parser_kind_is_constant_size k);
  en
