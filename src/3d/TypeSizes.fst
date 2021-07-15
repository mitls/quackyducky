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
module TypeSizes
open FStar.All
open Ast
open FStar.Mul
module H = Hashtable
module B = Binding

let product_size (base:size) (n:int) =
  match base with
  | Variable
  | WithVariableSuffix _ ->
    Variable
  | Fixed k ->
    Fixed (k * n)

let typename = ident'

let alignment = option (x:int{x == 1 \/ x == 2 \/ x == 4 \/ x == 8})

type size_env = H.t typename (size & alignment)

//TODO: size of pointer is platform-dependent
let pointer_alignment : alignment = Some 8

let initial_senv () =
  let i = [
       ("unit",     (Fixed 0,  None));
       ("Bool",     (Fixed 1,  Some 1));
       ("UINT8",    (Fixed 1,  Some 1));
       ("UINT16",   (Fixed 2,  Some 2));
       ("UINT32",   (Fixed 4,  Some 4));
       ("UINT64",   (Fixed 8,  Some 8));
       ("UINT16BE",   (Fixed 2,  Some 2));
       ("UINT32BE",   (Fixed 4,  Some 4));
       ("UINT64BE",   (Fixed 8,  Some 8));
       ("field_id", (Fixed 4,  Some 4));
       ("all_bytes", (Variable, None));
       ("all_zeros", (Variable, None));
       ("PUINT8",   (Variable, pointer_alignment))
  ]
  in
  let senv = H.create 17 in
  List.iter (fun (i, k) -> H.insert senv (to_ident' i) k) i;
  senv

let size_and_alignment_of_typename (env:env_t) (i:ident)
  : ML (size & alignment)
  = match H.try_find (snd env) i.v with
    | Some s -> s
    | None ->
      failwith (Printf.sprintf "size_of_typename: Identifier %s not found" (ident_to_string i))

let size_of_typename (env:env_t) (i:ident)
  : ML size
  = fst (size_and_alignment_of_typename env i)

let print_size =
  function
  | Fixed n -> Printf.sprintf "(Fixed %d)" n
  | WithVariableSuffix n -> Printf.sprintf "(WithVariableSuffix %d)" n
  | Variable -> "Variable"

let extend_with_size_of_ident (env:env_t) (i:ident) (n:size) (a:alignment)
  : ML unit
  = Options.debug_print_string
     (Printf.sprintf "***** Size of %s = %s\n"
                     (ident_to_string i) (print_size n));
    H.insert (snd env) i.v (n, a)

let extend_with_size_of_typedef_names (env:env_t) (names:typedef_names) (size:size) (a:alignment)
  : ML unit
  = extend_with_size_of_ident env names.typedef_name size a;
    extend_with_size_of_ident env names.typedef_abbrev size a;
    extend_with_size_of_ident env names.typedef_ptr_abbrev Variable a

let size_and_alignment_of_typ (env:env_t) (t:typ)
  : ML (size & alignment)
  = match t.v with
    | Type_app i _ -> size_and_alignment_of_typename env i
    | Pointer _ -> Variable, Some 8

let size_of_typ (env:env_t) (t:typ)
  : ML size
  = fst (size_and_alignment_of_typ env t)

let rec value_of_const_expr (env:env_t) (e:expr)
  : ML (option (either bool (integer_type & int)))
  =
  match e.v with
  | Constant (Int t n) -> Some (Inr (t, n))
  | Constant (Bool b) -> Some (Inl b)
  | App op [e1; e2] ->
    let v1 = value_of_const_expr env e1 in
    let v2 = value_of_const_expr env e2 in
    begin
    match op, v1, v2 with
    | Plus _,  Some (Inr (t1, n1)), Some (Inr (t2, n2)) -> Some (Inr (integer_type_lub t1 t2, n1 + n2))
    | Minus _, Some (Inr (t1, n1)), Some (Inr (t2, n2)) -> Some (Inr (integer_type_lub t1 t2, n1 - n2))
    | Mul _,   Some (Inr (t1, n1)), Some (Inr (t2, n2)) -> Some (Inr (integer_type_lub t1 t2, n1 * n2))
    | Division _, Some (Inr (t1, n1)), Some (Inr (t2, n2)) ->
      if n2 = 0
      then error ("Division by zero in constant expression") e2.range
      else Some (Inr (integer_type_lub t1 t2, n1 / n2))
    | GT _, Some (Inr (_, n1)), Some (Inr (_, n2)) -> Some (Inl (n1 > n2))
    | LT _, Some (Inr (_, n1)), Some (Inr (_, n2)) -> Some (Inl (n1 < n2))
    | GE _, Some (Inr (_, n1)), Some (Inr (_, n2)) -> Some (Inl (n1 >= n2))
    | LE _, Some (Inr (_, n1)), Some (Inr (_, n2)) -> Some (Inl (n1 <= n2))
    | And, Some (Inl b1), Some (Inl b2) -> Some (Inl (b1 && b2))
    | Or, Some (Inl b1), Some (Inl b2) -> Some (Inl (b1 || b2))
    | _ -> None
    end
  | App Not [e] ->
    let v = value_of_const_expr env e in
    begin
    match v with
    | Some (Inl b) -> Some (Inl (not b))
    | _ -> None
    end
  | App SizeOf [{v=Identifier t}] ->
    begin
    try
      match size_of_typ env (with_range (Type_app t []) t.range) with
      | Fixed n
      | WithVariableSuffix n -> Some (Inr (UInt32, n))
      | _ -> None
    with
      | _ -> None
    end
  | App (Cast _ t) [e] ->
    let v = value_of_const_expr env e in
    begin
    match v with
    | Some (Inr (_, n)) ->
      Some (Inr (t, n))
    | _ -> None
    end
  | Identifier i ->
    begin
    match B.lookup_macro_definition (fst env) i with
    | Some e ->
      value_of_const_expr env e
    | _ -> None
    end
  | _ -> None

let size_and_alignment_of_field (env:env_t) (f:field)
  : ML (size & alignment)
  = let base_size, align = size_and_alignment_of_typ env f.v.field_type in
    let size =
      match f.v.field_array_opt with
      | FieldScalar ->
        base_size

      | FieldArrayQualified (n, ByteArrayByteSize) ->
        if base_size <> Fixed 1
        then warning "Expected a byte array; if the underlying array elements are larger than a byte, use the '[:byte-size' notation"
                     f.range;
        let n = value_of_const_expr env n in
        begin
        match n with
        | Some (Inr (_, k)) ->
          Fixed k
        | _ ->
          Variable
        end

      | FieldString (Some n)
      | FieldArrayQualified (n, ArrayByteSize)
      | FieldArrayQualified (n, ArrayByteSizeSingleElementArray) ->
        let n = value_of_const_expr env n in
        begin
        match n with
        | Some (Inr (_, k)) -> Fixed k

        | _ ->
          Variable
        end

      | _ -> Variable
    in
    size, align

#push-options "--warn_error -272"
let gen_alignment_ident
  : unit -> ML ident
  = let ctr : ref int = alloc 0 in
    fun () ->
      let next = !ctr in
      ctr := next + 1;
      with_range
        (to_ident' (Printf.sprintf "%salignment_padding_%d" Ast.reserved_prefix next))
        dummy_range
#pop-options

let padding_field (env:env_t) (enclosing_struct:ident) (padding_msg:string) (n:int)
  : ML (list field)
  =
  if n <= 0
  then []
  else (
    let field_name = gen_alignment_ident() in
    let n_expr = with_range (Constant (Int UInt32 n)) dummy_range in
    FStar.IO.print_string
      (Printf.sprintf "Adding padding field in %s for %d bytes at %s\n"
                       (ident_to_string enclosing_struct)
                       n
                       padding_msg);
    let sf = {
      field_dependence = false;
      field_ident = field_name;
      field_type = tuint8;
      field_array_opt=(if n = 1 then FieldScalar else FieldArrayQualified(n_expr, ByteArrayByteSize));
      field_constraint=None;
      field_bitwidth=None;
      field_action=None
    } in
    [with_dummy_range sf]
  )

let should_align (td:typedef_names)
  : bool
  = List.Tot.Base.mem Aligned td.typedef_attributes

let alignment_padding env (enclosing_name:typedef_names) (msg:string) (offset:size) (a:alignment)
  : ML (int & list field)
  = if not (should_align enclosing_name)
    then 0, []
    else (
      let pad_size =
          match offset, a with
          | _, None ->
            0 //no alignment for this type
          | Fixed o, Some n ->
            if o % n = 0
            then 0 //already aligned
            else n - (o % n)
          | _ ->
            //variable offset;
            //this is beyond what is expressed in C
            //no alignment needed
            0
      in
      pad_size,
      padding_field env enclosing_name.typedef_name msg pad_size
    )

let sum_size (n : size) (m:size)
  = match n with
    | Variable
    | WithVariableSuffix _ -> n
    | Fixed n ->
      match m with
      | Fixed m -> Fixed (n + m)
      | WithVariableSuffix m -> WithVariableSuffix (n + m)
      | Variable -> WithVariableSuffix n

let decl_size_with_alignment (env:env_t) (d:decl)
  : ML decl
  = match d.d_decl.v with
    | ModuleAbbrev _ _ -> d
    | Define _ _ _ -> d

    | TypeAbbrev t i
    | Enum t i _ ->
      let s, a = size_and_alignment_of_typ env t in
      extend_with_size_of_ident env i s a;
      d

    | Record names params where fields ->
      let aligned_field_size
            (offset:size)
            (max_align:alignment)
            (fields:list field)
            (f:field)
        : ML (size & alignment & list field)
        = let field_size, field_alignment = size_and_alignment_of_field env f in
          let pad_size, padding_field =
            let msg = Printf.sprintf "(preceding field %s)" (ident_to_string f.v.field_ident) in
            alignment_padding env names msg offset field_alignment
          in
          let offset =
            (offset `sum_size` (Fixed pad_size)) `sum_size`
            field_size
          in
          let max_align =
            match max_align, field_alignment with
            | None, _ -> field_alignment
            | _, None -> max_align
            | Some n, Some m -> Some (FStar.Math.Lib.max n m)
          in
          let fields =
            f ::
            padding_field @
            fields
          in
          offset, max_align, fields
      in
      let size, max_align, fields_rev =
        List.fold_left
          (fun (o, m, fs) f -> aligned_field_size o m fs f)
          (Fixed 0, None, [])
          fields
      in
      let pad_size, end_padding =
          alignment_padding env names "(end padding)" size max_align
      in
      let size = size `sum_size` (Fixed pad_size) in
      let fields_rev = end_padding @ fields_rev in
      let fields = List.rev fields_rev in
      extend_with_size_of_typedef_names env names size max_align;
      decl_with_v d (Record names params where fields)

    | CaseType names params cases ->
      let case_sizes =
        List.map
          (function
            | Case _ f
            | DefaultCase f ->
              size_and_alignment_of_field env f)
          (snd cases)
      in
      let combine_size_and_alignment
          (accum_size, accum_align)
          (f_size, f_align)
       = let size =
             match accum_size with
             | None -> Some f_size
             | Some s ->
               if s = f_size
               then Some s
               else Some Variable
         in
         let alignment : alignment =
           if None? accum_align then f_align
           else if None? f_align then accum_align
           else let Some n = accum_align in
                let Some m = f_align in
                Some (FStar.Math.Lib.max n m)
         in
         size, alignment
      in
      let size, alignment =
        List.fold_left
          combine_size_and_alignment
          (None, None)
          case_sizes
      in
      let size =
        match size with
        | None -> Fixed 0 //empty case type
        | Some s -> s
      in
      let alignment = if Fixed? size then alignment else None in
      let all_fixed =
        List.for_all
          (fun (size, _) ->
            match size with
            | Fixed _ -> true
            | _ -> false)
          case_sizes
      in
      if should_align names
      then (
        let all_cases_fixed =
          List.for_all (function (Fixed _, _) -> true | _ -> false) case_sizes
        in
        if all_cases_fixed
        && not (Fixed? size)
        then error
              "With the --align option, \
               all cases of a union with a fixed size \
               must have the same size; \
               union padding is not yet supported"
               d.d_decl.range
      );
      extend_with_size_of_typedef_names env names size alignment;
      d

let size_of_decls (genv:B.global_env) (senv:size_env) (ds:list decl) =
  let env =
    B.mk_env genv, senv in
    // {senv with sizes = H.create 10} in
  let ds = List.map (decl_size_with_alignment env) ds in
  ds, snd env

let finish_module en mname e_and_p =
  e_and_p |> snd |> List.iter (H.remove en);
  en
  
