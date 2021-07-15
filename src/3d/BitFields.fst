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
module BitFields
open FStar.Mul
open Ast
open FStar.All
module B = Binding
module H = Hashtable

(* This module implements a pass over the source AST

   coalescing adjacent bit fields and replacing expressions on
   bitfields using offsets into larger fgields

*)

let bitfield_group = int & typ & list field
let grouped_fields = either field bitfield_group

let group_bit_fields (fields: list field)
  : ML (list grouped_fields)
  = List.fold_right
      (fun field out ->
        match field.v.field_bitwidth with
        | None ->
          Inl field :: out

        | Some (Inl _) ->
          failwith "Bit fields should have been elaborated already"

        | Some (Inr bf) ->
          match out with
          | Inr (index, typ, fields)::tl ->
            if index = bf.v.bitfield_identifier
            then Inr(index, typ, field::fields) :: tl //extend this bitfield group
            else Inr(bf.v.bitfield_identifier, bf.v.bitfield_type, [field]) :: out //new bitfield group

          | _ -> Inr (bf.v.bitfield_identifier, bf.v.bitfield_type, [field]) :: out //new bitfield group
        )
       fields
       []

let coalesce_grouped_bit_field env (f:bitfield_group)
  : ML (field & list (ident & expr))
  = let id, typ, fields = f in
    let size = B.size_of_integral_typ env typ typ.range in
    let bitsize = 8 * size in
    let field_id = with_range (to_ident' (Printf.sprintf "__bitfield_%d" id)) dummy_range in
    let id = with_range (Identifier field_id) field_id.range in
    let mk_e (e:expr') :expr = with_range e field_id.range in
    let bitfield_attrs f : ML _ =
      match f.field_bitwidth with
      | Some (Inr bf) -> bf.v
      | _ -> failwith "Must have elaborated bitfield"
    in
    let field_dependence, field_constraint, subst =
      List.fold_left
        (fun (dep, acc_constraint, subst) f ->
          let f = f.v in
          let dep = dep || f.field_dependence in
          let acc_constraint =
            match f.field_constraint, acc_constraint with
            | None, _ -> acc_constraint
            | Some _, None -> f.field_constraint
            | Some c, Some acc -> Some (mk_e (App And [acc; c]))
          in
          let bf_exp =
            App
              (BitFieldOf bitsize)
              [id;
              mk_e (Constant (Int UInt32 (bitfield_attrs f).bitfield_from));
              mk_e (Constant (Int UInt32 (bitfield_attrs f).bitfield_to))]
          in
          let subst = (f.field_ident, mk_e bf_exp) :: subst in
          dep, acc_constraint, subst)
       (false, None, [])
       fields
    in
    let struct_field = {
      field_dependence = field_dependence;
      field_ident = field_id;
      field_type = typ;
      field_array_opt = FieldScalar;
      field_constraint = field_constraint;
      field_bitwidth = None;
      field_action = None; //TODO conjunction of all actions on individual fields?
    } in
    with_dummy_range struct_field,
    subst

let coalesce_fields (env:B.global_env) (fields:list field)
  : ML (list field & list (ident & expr))
  = let fs = group_bit_fields fields in
    let fs, subst =
      List.fold_right
        (fun f (fields, subst) ->
          match f with
          | Inl f -> (f::fields, subst)
          | Inr gf ->
            let f, subst' = coalesce_grouped_bit_field (B.mk_env env) gf in
            f::fields, subst'@subst)
        fs
        ([], [])
    in
    fs,
    subst

let eliminate_one_decl (env:B.global_env) (d:decl) : ML decl =
  match d.d_decl.v with
  | Record names params where fields ->
    let fields, subst = coalesce_fields env fields in
    List.iter (fun f ->
      Options.debug_print_string
            (Printf.sprintf "Bitfields: Field %s has comments <%s>\n"
                  (print_ident f.v.field_ident)
                  (String.concat "\n" f.comments))) fields;

    List.iter (fun (i, e) ->
      Options.debug_print_string (Printf.sprintf "subst(%s -> %s)\n" (ident_to_string i) (print_expr e)))
      subst;
    let fields = List.map (subst_field (mk_subst subst)) fields in
    let fields =
      match fields with
      | [f] -> //just one field, it need no longer be dependent
        let sf = { f.v with field_dependence = false } in
        [{ f with v = sf }]
      | _ -> fields
    in
    decl_with_v d (Record names params where fields)
  | _ -> d

let eliminate (env:B.global_env) (ds:list decl) : ML (list decl) =
  List.map (eliminate_one_decl env) ds
