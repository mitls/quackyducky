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
module Actions
module LP = LowParse.Spec.Base
module LPC = LowParse.Spec.Combinators
module LPL = EverParse3d.InputBuffer
module R = EverParse3d.Readable
module LPLC = LowParse.Low.Combinators
module LPLL = LowParse.Low.List
module LPLF = LowParse.Spec.FLData
module Cast = FStar.Int.Cast
module HS = FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer
friend Prelude
open Prelude
module B = LowStar.Buffer
module U8 = FStar.UInt8

let app_ctxt = B.pointer U8.t
let app_loc (x:app_ctxt) (l:eloc) : eloc = B.loc_buffer x `loc_union` l

inline_for_extraction
let action p inv l on_success a
  = ctxt:app_ctxt ->
    #len: U32.t ->
    sl: input_buffer_t len ->
    pos:LPL.pos_t ->
    res:U64.t ->
    Stack a
      (requires fun h ->
        let open LPL in
        LPL.live_input_buffer h sl /\
        B.live h ctxt  /\
        inv (LPL.slice_of sl).LPL.base h /\
        loc_not_unused_in h `loc_includes` (app_loc ctxt l) /\
        address_liveness_insensitive_locs `loc_includes` (app_loc ctxt l) /\
        (app_loc ctxt l) `loc_disjoint` 
        (loc_buffer (LPL.slice_of sl).base `loc_union` R.loc_perm (LPL.perm_of sl)) /\
        (U64.v res <= U64.v validator_max_length ==>
           valid_pos p h (LPL.slice_of sl) (uint64_to_uint32 pos) (uint64_to_uint32 res)) /\
        (on_success ==> U64.v res <= U64.v validator_max_length))
      (ensures fun h0 _ h1 ->
        modifies (app_loc ctxt l) h0 h1 /\
        B.live h1 ctxt /\        
        h1 `extends` h0 /\
        inv (LPL.slice_of sl).LPL.base h1)

inline_for_extraction
let error_handler = typename:string ->
                    fieldname:string ->
                    error_reason:string ->
                    action (parse_impos()) true_inv eloc_none false unit

inline_for_extraction
let validate_with_action_t' (#k:LP.parser_kind) (#t:Type) (p:LP.parser k t) (inv:slice_inv) (l:eloc) (allow_reading:bool) =
  (ctxt: app_ctxt) ->
  (err : error_handler) ->
  (#len: U32.t) ->
  (sl: input_buffer_t len) ->
  (pos: U64.t) ->
  Stack U64.t
  (requires fun h ->
    let open LPL in
    live_input_buffer h sl /\
    B.live h ctxt /\
    inv (slice_of sl).base h /\
    loc_not_unused_in h `loc_includes` (app_loc ctxt l) /\
    address_liveness_insensitive_locs `loc_includes` (app_loc ctxt l) /\
    (app_loc ctxt l) `loc_disjoint` (loc_buffer (slice_of sl).base `loc_union` R.loc_perm (perm_of sl)) /\
    U64.v pos <= U32.v (slice_of sl).len /\
    R.readable h (perm_of sl) (uint64_to_uint32 pos) (slice_of sl).len
  )
  (ensures fun h res h' ->
    let open LPL in
    h' `extends` h /\
    live_input_buffer h' sl /\
    B.live h' ctxt /\
    inv (slice_of sl).base h' /\
    (is_success res ==> valid_pos p h (slice_of sl) (uint64_to_uint32 pos) (uint64_to_uint32 res)) /\
    modifies
      (if allow_reading
       then (app_loc ctxt l)
       else (app_loc ctxt l) `loc_union` 
            (R.loc_perm_from_to (perm_of sl) (uint64_to_uint32 pos) (if is_success res then uint64_to_uint32 res else (slice_of sl).len)))
      h h' /\
    ((~ allow_reading) ==> R.unreadable h' (perm_of sl) (uint64_to_uint32 pos) (if is_success res then uint64_to_uint32 res else (slice_of sl).len))
  )

inline_for_extraction
let validate_with_action_t p inv l allow_reading =
  validate_with_action_t' p inv l allow_reading

let validate_eta v =
  fun ctxt err #inputLength input startPosition -> v ctxt err input startPosition

inline_for_extraction noextract
let act_with_comment
  (s: string)
  #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
  (#inv:slice_inv) (#l:eloc) (#b:_) (res:Type)
  (a: action p inv l b res)
: Tot (action p inv l b res)
= fun ctxt #inputLength input startPosition endPosition ->
  LPL.comment s;
  a ctxt input startPosition endPosition

inline_for_extraction
let leaf_reader
  #nz
  #k
  (#t: Type)
  (p: parser k t)
: Tot Type
= (#len: U32.t) ->
  (sl: input_buffer_t len) ->
  (pos: U32.t) ->
  Stack t
  (requires (fun h ->
    LPL.valid p h (LPL.slice_of sl) pos /\
    R.readable h (LPL.perm_of sl) pos (LPL.get_valid_pos p h (LPL.slice_of sl) pos)
  ))
  (ensures (fun h res h' ->
    let pos' = LPL.get_valid_pos p h (LPL.slice_of sl) pos in
    modifies (R.loc_perm_from_to (LPL.perm_of sl) pos pos') h h' /\
    R.unreadable h' (LPL.perm_of sl) pos pos' /\
    h' `extends` h /\
    res == LPL.contents p h (LPL.slice_of sl) pos
  ))

inline_for_extraction noextract
let lift_constant_size_leaf_reader #nz 
                                   (#k: parser_kind nz WeakKindStrongPrefix)
                                   #t
                                   (#p:parser k t)
                                   (r:LPL.leaf_reader p)
                                   (sz: U32.t { k.LPL.parser_kind_high == Some k.LPL.parser_kind_low /\ k.LPL.parser_kind_low == U32.v sz })
  : leaf_reader p
  = fun #inputLength input startPosition ->
      LPL.read_with_perm r (LPL.jump_constant_size p sz ()) input startPosition

inline_for_extraction
noextract
let with_drop_if
  (#t: Type)
  (cond: bool)
  (inv: slice_inv)
  (#len: U32.t)
  (sl: input_buffer_t len)
  (from: U32.t)
  (fto: ((x: t) -> Tot U32.t))
  (x: t)
: HST.Stack t
  (requires (fun h ->
    let to = fto x in
    U32.v from <= U32.v to /\
    U32.v to <= U32.v (LPL.slice_of sl).LPL.len /\
    LPL.live_input_buffer h sl /\
    inv (LPL.slice_of sl).LPL.base h
  ))
  (ensures (fun h res h' ->
    B.modifies (if cond then R.loc_perm_from_to (LPL.perm_of sl) from (fto x) else B.loc_none) h h' /\
    LPL.live_input_buffer h' sl /\
    (cond ==> R.unreadable h' (LPL.perm_of sl) from (fto x)) /\
    inv (LPL.slice_of sl).LPL.base h' /\
    res == x
  ))
= let h1 = HST.get () in
  if cond then LPL.drop sl from (fto x);
  let h2 = HST.get () in
  [@inline_let] let _ = assert (h2 `extends` h1) in
  x

inline_for_extraction
noextract
let validate_drop
   #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t) (#inv:slice_inv) (#l:eloc) (#allow_reading:bool)
   (v: validate_with_action_t p inv l allow_reading)
: Tot (validate_with_action_t p inv l false)
= fun
  ctxt
  err
  input
  (startPosition: U64.t) ->
    with_drop_if true inv input (LPL.uint64_to_uint32 startPosition)
                                (fun (y: U64.t) -> if LPL.is_success y then LPL.uint64_to_uint32 y else LPL.slice_length input)
                                (v ctxt err input startPosition)

inline_for_extraction
noextract
let validate_with_success_action' 
       (name: string)
       #nz
       #wk
       (#k1:parser_kind nz wk)
       #t1
       (#p1:parser k1 t1)
       (#inv1:_)
       (#l1:eloc)
       (#ar:_)
       (v1:validate_with_action_t p1 inv1 l1 ar)
       (#inv2:_)
       (#l2:eloc)
       #b
       (a:action p1 inv2 l2 b bool)
  : validate_with_action_t p1 (conj_inv inv1 inv2) (l1 `eloc_union` l2) ar
  = fun ctxt err input startPosition ->
    let h0 = HST.get () in
    [@(rename_let ("positionAfter" ^ name))]
    let pos1 = v1 ctxt err input startPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    if LPL.is_success pos1
    then
         [@(rename_let ("action_success_" ^ name))]
         let b = a ctxt input startPosition pos1 in
         if not b
         then
           with_drop_if (not ar) (conj_inv inv1 inv2) input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input) validator_error_action_failed
         else
           pos1
    else
         pos1

let validate_with_success_action name v1 a
  = validate_drop (validate_with_success_action' name v1 a)

module P = Prelude
  

inline_for_extraction noextract
let validate_with_error_handler (typename:string) 
                                (fieldname:string)
                                #nz
                                #wk
                                (#k1:parser_kind nz wk)
                                 #t1
                                (#p1:parser k1 t1)
                                (#inv1:_)
                                (#l1:eloc)
                                (#ar:_)
                                (v1:validate_with_action_t p1 inv1 l1 ar)
  : validate_with_action_t p1 inv1 l1 ar
  = fun ctxt err input startPosition ->
    let h0 = HST.get () in
    [@(rename_let ("positionAfter" ^ typename))]
    let pos1 = v1 ctxt err input startPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    if LPL.is_success pos1
    then pos1
    else (
         err typename fieldname (ResultOps.error_reason_of_result pos1) ctxt input startPosition pos1;
         pos1
    )

inline_for_extraction noextract
let validate_with_error_action'
      (name: string)
      #nz
      #wk
      (#k1:parser_kind nz wk)
      #t1
      (#p1:parser k1 t1)
      (#inv1:_)
      (#l1:eloc)
      (#ar:_)
      (v1:validate_with_action_t p1 inv1 l1 ar)
      (#inv2:_)
      (#l2:eloc)
      (a:action p1 inv2 l2 false bool)
  : validate_with_action_t p1 (conj_inv inv1 inv2) (l1 `eloc_union` l2) ar
  = fun ctxt err input startPosition ->
    let h0 = HST.get () in
    [@(rename_let ("positionAfter" ^ name))]
    let pos1 = v1 ctxt err input startPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    if LPL.is_success pos1
    then pos1
    else
         [@(rename_let ("action_error_" ^ name))]
         let b = a ctxt input startPosition pos1 in
         if not b then validator_error_action_failed else pos1

let validate_with_error_action
  name v1 a
= validate_drop (validate_with_error_action' name v1 a)

inline_for_extraction noextract
let validate_ret
  : validate_with_action_t (parse_ret ()) true_inv eloc_none true
  = fun ctxt err input startPosition ->
    let h = HST.get () in
    [@inline_let] let _ = LPL.valid_facts (parse_ret ()) h (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition) in
    startPosition

#push-options "--z3rlimit 16"

inline_for_extraction noextract
let validate_pair'
       (name1: string)
       #nz1 
       (#k1:parser_kind nz1 WeakKindStrongPrefix)
       #t1
       (#p1:parser k1 t1)
       (#inv1:_) 
       (#l1:eloc)
       (#ar1:_)
       (v1:validate_with_action_t p1 inv1 l1 ar1)
       #nz2
       #wk2
       (#k2:parser_kind nz2 wk2)
       #t2
       (#p2:parser k2 t2)
       (#inv2:_)
       (#l2:eloc)
       (#ar2:_)
       (v2:validate_with_action_t p2 inv2 l2 ar2)
  : validate_with_action_t (p1 `parse_pair` p2) (conj_inv inv1 inv2) (l1 `eloc_union` l2) (ar1 && ar2)
  = fun ctxt err input startPosition ->
    let h = HST.get () in
    [@inline_let] let _ = LPLC.valid_nondep_then h p1 p2 (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition) in
    [@(rename_let ("positionAfter" ^ name1))]
    let pos1 = v1 ctxt err input startPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h1;
    if LPL.is_error pos1
    then begin
      with_drop_if (not (ar1 && ar2))
                   (conj_inv inv1 inv2)
                   input
                   (LPL.uint64_to_uint32 startPosition)
                   (fun _ -> LPL.slice_length input)
                   pos1
    end
    else
      [@inline_let] 
      let _ = R.readable_split 
                h
                (LPL.perm_of input)
                (LPL.uint64_to_uint32 startPosition)
                (LPL.uint64_to_uint32 pos1)
                (LPL.slice_length input)
      in
      [@inline_let]
      let _ = LPL.valid_facts p2 h (LPL.slice_of input) (LPL.uint64_to_uint32 pos1) in
      with_drop_if (not (ar1 && ar2))
                   (conj_inv inv1 inv2)
                   input 
                   (LPL.uint64_to_uint32 startPosition)
                   (fun (x: U64.t) -> if LPL.is_success x then LPL.uint64_to_uint32 x else LPL.slice_length input)
                   (v2 ctxt err input pos1)

let validate_pair
  name1 v1 v2
= validate_drop (validate_pair' name1 v1 v2)

inline_for_extraction noextract
let validate_dep_pair
      (name1: string)
      #nz1 
      (#k1:parser_kind nz1 _)
      #t1
      (#p1:parser k1 t1)
      #inv1
      #l1
      (v1:validate_with_action_t p1 inv1 l1 true)
      (r1: leaf_reader p1)
      #nz2
      #wk2
      (#k2:parser_kind nz2 wk2)
      (#t2:t1 -> Type)
      (#p2:(x:t1 -> parser k2 (t2 x)))
      #inv2
      #l2
      #ar2
      (v2:(x:t1 -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t (p1 `parse_dep_pair` p2) (conj_inv inv1 inv2) (l1 `eloc_union` l2) false)
  = fun ctxt err input startPosition ->
      let h = HST.get () in
      [@inline_let] let _ = LPLC.valid_dtuple2 h p1 p2 (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition) in
      [@(rename_let ("positionAfter" ^ name1))]
      let pos1 = v1 ctxt err input startPosition in
      let h1 = HST.get() in
      if LPL.is_error pos1
      then begin
        with_drop_if 
          true
          (conj_inv inv1 inv2)
          input
          (LPL.uint64_to_uint32 startPosition)
          (fun _ -> LPL.slice_length input)
          pos1
      end
      else
        [@inline_let]
        let _ = 
          R.readable_split
            h
            (LPL.perm_of input)
            (LPL.uint64_to_uint32 startPosition)
            (LPL.uint64_to_uint32 pos1)
            (LPL.slice_length input)
        in
        [@(rename_let ("" ^ name1))]
        let x = r1 input (LPL.uint64_to_uint32 startPosition) in
        let h15 = HST.get () in
        let _ = modifies_address_liveness_insensitive_unused_in h h15 in
        [@inline_let]
        let _ = 
          LPLC.valid_facts
            (p2 x)
            h
            (LPL.slice_of input)
            (LPL.uint64_to_uint32 pos1)
        in
        with_drop_if
          true
          (conj_inv inv1 inv2)
          input
          (LPL.uint64_to_uint32 startPosition)
          (fun (y: U64.t) -> if LPL.is_success y then LPL.uint64_to_uint32 y else LPL.slice_length input)
          (v2 x ctxt err input pos1)

#pop-options

#push-options "--z3rlimit 64"

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action'
      (name1: string)
      #nz1
      (#k1:parser_kind nz1 _)
      #t1
      (#p1:parser k1 t1)
      #inv1
      #l1
      (v1:validate_with_action_t p1 inv1 l1 true)
      (r1: leaf_reader p1)
      (f: t1 -> bool)
      #inv1'
      #l1' 
      #b
      (a:t1 -> action p1 inv1' l1' b bool)
      #nz2
      #wk2
      (#k2:parser_kind nz2 wk2)
      (#t2:refine _ f -> Type)
      (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2
      #l2
      #ar2
      (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 (conj_inv inv1' inv2))
             (l1 `eloc_union` (l1' `eloc_union` l2))
             false)
  = fun ctxt err input startPosition ->
      let h0 = HST.get () in
      [@inline_let] 
      let _ =
        LPLC.valid_filter
          h0
          p1
          f
          (LPL.slice_of input)
          (LPL.uint64_to_uint32 startPosition)
        in
      [@(rename_let ("positionAfter" ^ name1))]
      let res = v1 ctxt err input startPosition in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPL.is_error res
      then begin
        with_drop_if
          true
          (conj_inv inv1 (conj_inv inv1' inv2))
          input
          (LPL.uint64_to_uint32 startPosition)
          (fun _ -> LPL.slice_length input)
          res
      end
      else begin
        [@inline_let]
        let _ = 
          R.readable_split
            h0
            (LPL.perm_of input)
            (LPL.uint64_to_uint32 startPosition) 
            (LPL.uint64_to_uint32 res)
            (LPL.slice_length input)
        in
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input (LPL.uint64_to_uint32 startPosition) in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("pos_or_error_after_" ^ name1))]
        let res1 = check_constraint_ok_with_field_id ok startPosition res 1uL in
        if LPL.is_error res1
        then
          with_drop_if 
            true
            (conj_inv inv1 (conj_inv inv1' inv2))
            input
            (LPL.uint64_to_uint32 startPosition)
            (fun _ -> LPL.slice_length input)
            res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h1 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             // [@(rename_let ("action_" ^ name1))]
             // let action_result =  in
             if not (a field_value ctxt input startPosition res)
             then //action failed
                  with_drop_if 
                     true
                     (conj_inv inv1 (conj_inv inv1' inv2))
                     input
                     (LPL.uint64_to_uint32 startPosition)
                     (fun _ -> LPL.slice_length input)
                     (LPL.set_validator_error_pos_and_code validator_error_action_failed startPosition 1uL)
             else begin
               let open LPL in
               // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               [@inline_let] 
               let _ = 
                 LPLC.valid_facts
                   (p2 field_value)
                   h0
                   (LPL.slice_of input)
                   (LPL.uint64_to_uint32 res1)
               in
               [@inline_let]
               let _ =
                 LPLC.valid_dtuple2
                   h0
                   (p1 `LPC.parse_filter` f)
                   p2
                   (LPL.slice_of input)
                   (LPL.uint64_to_uint32 startPosition)
               in
               with_drop_if
                 true
                 (conj_inv inv1 (conj_inv inv1' inv2))
                 input
                 (LPL.uint64_to_uint32 startPosition)
                 (fun (x: U64.t) -> if LPL.is_success x then LPL.uint64_to_uint32 x else LPL.slice_length input)
                 (v2 field_value ctxt err input res1)
             end
        end

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action_total_zero_parser'
      (name1: string)
      #nz1
      (#k1:parser_kind nz1 _)
      #t1
      (#p1:parser k1 t1)
      #inv1
      #l1
      (v1:validate_with_action_t p1 inv1 l1 true)
      (r1: leaf_reader p1)
      (f: t1 -> bool)
      #inv1'
      #l1'
      #b
      (a:t1 -> action p1 inv1' l1' b bool)
      #nz2
      #wk2
      (#k2:parser_kind nz2 wk2)
      (#t2:refine _ f -> Type)
      (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2
      #l2
      #ar2
      (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Pure (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 (conj_inv inv1' inv2))
             (l1 `eloc_union` (l1' `eloc_union` l2))
             false)
         (requires (
           let open LP in
           k1.parser_kind_high == Some 0 /\
           k1.parser_kind_metadata == Some ParserKindMetadataTotal
         ))
         (ensures (fun _ -> True))
  = fun ctxt err input startPosition ->
      let h0 = HST.get () in
      [@inline_let] 
      let _ =
        LPLC.valid_filter h0 p1 f (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition)
      in
      [@inline_let]
      let _ =
        LPLC.valid_facts p1 h0 (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition) 
      in
      [@inline_let]
      let _ = LP.parser_kind_prop_equiv k1 p1 in
      begin
        LowStar.Comment.comment ("Validating field " ^ name1);
        [@inline_let]
        let _ = 
          R.readable_split
            h0
            (LPL.perm_of input)
            (LPL.uint64_to_uint32 startPosition)
            (LPL.uint64_to_uint32 startPosition)
            (LPL.slice_length input) 
        in
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input (LPL.uint64_to_uint32 startPosition) in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("pos_or_error_after_" ^ name1))]
        let res1 = check_constraint_ok_with_field_id ok startPosition startPosition 1uL in
        if LPL.is_error res1
        then
             with_drop_if
               true
               (conj_inv inv1 (conj_inv inv1' inv2))
               input
               (LPL.uint64_to_uint32 startPosition)
               (fun _ -> LPL.slice_length input)
               res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h0 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             // [@(rename_let ("action_" ^ name1))]
             // let action_result =  in
             if not (a field_value ctxt input startPosition startPosition)
             then //action failed
                  with_drop_if
                    true
                    (conj_inv inv1 (conj_inv inv1' inv2))
                    input
                    (LPL.uint64_to_uint32 startPosition)
                    (fun _ -> LPL.slice_length input)
                    (LPL.set_validator_error_pos_and_code validator_error_action_failed startPosition 1uL)
             else begin
               let open LPL in
               // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               [@inline_let] 
               let _ = 
                 LPLC.valid_facts 
                   (p2 field_value)
                   h0
                   (LPL.slice_of input)
                   (LPL.uint64_to_uint32 res1) 
               in
               [@inline_let]
               let _ = 
                 LPLC.valid_dtuple2
                   h0
                   (p1 `LPC.parse_filter` f)
                   p2
                   (LPL.slice_of input)
                   (LPL.uint64_to_uint32 startPosition)
               in
               with_drop_if
                 true
                 (conj_inv inv1 (conj_inv inv1' inv2))
                 input
                 (LPL.uint64_to_uint32 startPosition)
                 (fun (x: U64.t) -> if LPL.is_success x then LPL.uint64_to_uint32 x else LPL.slice_length input)
                 (v2 field_value ctxt err input res1)
             end
        end

inline_for_extraction noextract
let validate_dep_pair_with_refinement'
      (name1: string)
      #nz1
      (#k1:parser_kind nz1 _)
      #t1
      (#p1:parser k1 t1)
      #inv1
      #l1
      (v1:validate_with_action_t p1 inv1 l1 true)
      (r1: leaf_reader p1)
      (f: t1 -> bool)
      #nz2
      #wk2
      (#k2:parser_kind nz2 wk2)
      (#t2:refine _ f -> Type)
      (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2
      #l2
      #ar2
      (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 inv2)
             (l1 `eloc_union` l2)
             false)
  = fun ctxt err input startPosition ->
      let h0 = HST.get () in
      [@inline_let] let _ = LPLC.valid_filter h0 p1 f (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition) in
      [@(rename_let ("positionAfter" ^ name1))]
      let res = v1 ctxt err input startPosition in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPL.is_error res
      then begin
        with_drop_if true (conj_inv inv1 inv2) input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input) res
      end
      else begin
        [@inline_let] let _ = R.readable_split h0 (LPL.perm_of input) (LPL.uint64_to_uint32 startPosition) (LPL.uint64_to_uint32 res) (LPL.slice_length input) in
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input (LPL.uint64_to_uint32 startPosition) in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("positionOrErrorAfter" ^ name1))]
        let res1 = check_constraint_ok_with_field_id ok startPosition res 1uL in
        if LPL.is_error res1
        then
             with_drop_if true (conj_inv inv1 inv2) input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input) res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h1 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             let open LPL in
             // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
             let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
             [@inline_let] let _ = LPLC.valid_facts (p2 field_value) h0 (LPL.slice_of input) (LPL.uint64_to_uint32 res1) in
             [@inline_let] let _ = LPLC.valid_dtuple2 h0 (p1 `LPC.parse_filter` f) p2 (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition) in
             with_drop_if true (conj_inv inv1 inv2) input (LPL.uint64_to_uint32 startPosition) (fun (y: U64.t) -> if LPL.is_success y then LPL.uint64_to_uint32 y else LPL.slice_length input) (v2 field_value ctxt err input res1)
        end

inline_for_extraction noextract
let validate_dep_pair_with_refinement_total_zero_parser'
      (name1: string)
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Pure (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 inv2)
             (l1 `eloc_union` l2)
             false)
         (requires (
           let open LP in
           k1.parser_kind_high == Some 0 /\
           k1.parser_kind_metadata == Some ParserKindMetadataTotal
         ))
         (ensures (fun _ -> True))
  = fun ctxt err input startPosition ->
      let h0 = HST.get () in
      [@inline_let] let _ = LPLC.valid_filter h0 p1 f (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition) in
      [@inline_let] let _ = LPLC.valid_facts p1 h0 (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition) in
      [@inline_let] let _ = LP.parser_kind_prop_equiv k1 p1 in
      begin
        LowStar.Comment.comment ("Validating field " ^ name1);
        [@inline_let] let _ = R.readable_split h0 (LPL.perm_of input) (LPL.uint64_to_uint32 startPosition) (LPL.uint64_to_uint32 startPosition) (LPL.slice_length input) in
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input (LPL.uint64_to_uint32 startPosition) in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("positionOrErrorAfter" ^ name1))]
        let res1 = check_constraint_ok_with_field_id ok startPosition startPosition 1uL in
        if LPL.is_error res1
        then with_drop_if true (conj_inv inv1 inv2) input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input) res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h0 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             let open LPL in
             // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
             let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
             [@inline_let] let _ = LPLC.valid_facts (p2 field_value) h0 (LPL.slice_of input) (LPL.uint64_to_uint32 res1) in
             [@inline_let] let _ = LPLC.valid_dtuple2 h0 (p1 `LPC.parse_filter` f) p2 (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition) in
             with_drop_if true (conj_inv inv1 inv2) input (LPL.uint64_to_uint32 startPosition) (fun (y: U64.t) -> if LPL.is_success y then LPL.uint64_to_uint32 y else LPL.slice_length input) (v2 field_value ctxt err input res1)
        end

#pop-options

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #inv1' #l1' #b (a:t1 -> action p1 inv1' l1' b bool)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t ((p1 `parse_filter` f) `parse_dep_pair` p2)
                                (conj_inv inv1 (conj_inv inv1' inv2))
                                (l1 `eloc_union` (l1' `eloc_union` l2))
                                false)
  = if
      p1_is_constant_size_without_actions `LP.bool_and`
      (k1.LP.parser_kind_high = Some 0) `LP.bool_and`
      (k1.LP.parser_kind_metadata = Some LP.ParserKindMetadataTotal)
    then
      validate_dep_pair_with_refinement_and_action_total_zero_parser' name1 v1 r1 f a v2
    else
      validate_dep_pair_with_refinement_and_action' name1 v1 r1 f a v2

#push-options "--z3rlimit 32"

inline_for_extraction noextract
let validate_dep_pair_with_action
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      #inv1' #l1' #b (a:t1 -> action p1 inv1' l1' b bool)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2:t1 -> Type) (#p2:(x:t1 -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:t1 -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t
             (p1 `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 (conj_inv inv1' inv2))
             (l1 `eloc_union` (l1' `eloc_union` l2))
             false)
  = fun ctxt err input startPosition ->
      let h0 = HST.get () in
      let res = v1 ctxt err input startPosition in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPL.is_error res
      then begin
        with_drop_if true (conj_inv inv1 (conj_inv inv1' inv2)) input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input) res
      end
      else begin
        [@inline_let] let _ = R.readable_split h0 (LPL.perm_of input) (LPL.uint64_to_uint32 startPosition) (LPL.uint64_to_uint32 res) (LPL.slice_length input) in
        let field_value = r1 input (LPL.uint64_to_uint32 startPosition) in
        let h2 = HST.get() in
        modifies_address_liveness_insensitive_unused_in h1 h2;
        let action_result = a field_value ctxt input startPosition res in
        if not action_result
        then with_drop_if true (conj_inv inv1 (conj_inv inv1' inv2)) input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input) validator_error_action_failed //action failed
        else begin
               let open LPL in
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               [@inline_let] let _ = LPLC.valid_dtuple2 h0 p1 p2 (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition) in
               with_drop_if true (conj_inv inv1 (conj_inv inv1' inv2)) input (LPL.uint64_to_uint32 startPosition) (fun (y: U64.t) -> if LPL.is_success y then LPL.uint64_to_uint32 y else LPL.slice_length input) (v2 field_value ctxt err input res)
             end
      end

#pop-options

inline_for_extraction noextract
let validate_dep_pair_with_refinement
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t ((p1 `parse_filter` f) `parse_dep_pair` p2)
                                (conj_inv inv1 inv2)
                                (l1 `eloc_union` l2)
                                false)
  = if
      p1_is_constant_size_without_actions `LP.bool_and`
      (k1.LP.parser_kind_high = Some 0) `LP.bool_and`
      (k1.LP.parser_kind_metadata = Some LP.ParserKindMetadataTotal)
    then
      validate_dep_pair_with_refinement_total_zero_parser' name1 v1 r1 f v2
    else
      validate_dep_pair_with_refinement' name1 v1 r1 f v2

inline_for_extraction noextract
let validate_filter' (name: string) #nz (#k:parser_kind nz _) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
  : Tot (validate_with_action_t #nz #WeakKindStrongPrefix (p `LPC.parse_filter` f) inv l false)
  = fun ctxt err input startPosition ->
    let h = HST.get () in
    [@inline_let] let _ = LPLC.valid_filter h p f (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition) in
    [@(rename_let ("positionAfter" ^ name))]
    let res = v ctxt err input startPosition in
    let h1 = HST.get () in
    if LPL.is_error res
    then with_drop_if true inv input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input) res
    else begin
      LowStar.Comment.comment cr;
      [@inline_let] let _ = R.readable_split h (LPL.perm_of input) (LPL.uint64_to_uint32 startPosition) (LPL.uint64_to_uint32 res) (LPL.slice_length input) in
      [@(rename_let ("" ^ name))]
      let field_value = r input (LPL.uint64_to_uint32 startPosition) in
      LowStar.Comment.comment (normalize_term ("start: " ^cf));
      [@(rename_let (name ^ "ConstraintIsOk"))]
      let ok = f field_value in
      LowStar.Comment.comment (normalize_term ("end: " ^ cf));
      with_drop_if true inv input (LPL.uint64_to_uint32 startPosition) (fun (y: U64.t) -> if LPL.is_success y then LPL.uint64_to_uint32 y else LPL.slice_length input) (check_constraint_ok ok res)
    end

inline_for_extraction noextract
let validate_filter (name: string) #nz (#k:parser_kind nz _) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
  : Tot (validate_with_action_t (p `parse_filter` f) inv l false)
  = validate_filter' name v r f cr cf

inline_for_extraction noextract
let validate_filter'_with_action
                    (name: string) #nz (#k:parser_kind nz _) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
                    (#b:bool) #inva (#la:eloc) (a: t -> action #nz #WeakKindStrongPrefix #(filter_kind k) #_ (p `LPC.parse_filter` f) inva la b bool)
  : Tot (validate_with_action_t #nz #WeakKindStrongPrefix (p `LPC.parse_filter` f) (conj_inv inv inva) (eloc_union l la) false)
  = fun ctxt err input startPosition ->
    let h = HST.get () in
    [@inline_let] let _ = LPLC.valid_filter h p f (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition) in
    [@(rename_let ("positionAfter" ^ name))]
    let res = v ctxt err input startPosition in
    let h1 = HST.get () in
    if LPL.is_error res
    then with_drop_if true (conj_inv inv inva) input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input) res
    else begin
      LowStar.Comment.comment cr;
      [@inline_let] let _ = R.readable_split h (LPL.perm_of input) (LPL.uint64_to_uint32 startPosition) (LPL.uint64_to_uint32 res) (LPL.slice_length input) in
      [@(rename_let ("" ^ name))]
      let field_value = r input (LPL.uint64_to_uint32 startPosition) in
      LowStar.Comment.comment (normalize_term ("start: " ^cf));
      [@(rename_let (name ^ "ConstraintIsOk"))]
      let ok = f field_value in
      LowStar.Comment.comment (normalize_term ("end: " ^ cf));
      if ok
        then let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h h15 in
             if a field_value ctxt input startPosition res
             then res
             else with_drop_if true (conj_inv inv inva) input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input) validator_error_action_failed
      else with_drop_if true (conj_inv inv inva) input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input) validator_error_constraint_failed
    end

inline_for_extraction noextract
let validate_filter_with_action
                    (name: string) #nz (#k:parser_kind nz _) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
                    (#b:bool) #inva (#la:eloc) (a: t -> action (p `parse_filter` f) inva la b bool)
  : Tot (validate_with_action_t #nz (p `parse_filter` f) (conj_inv inv inva) (eloc_union l la) false)
  = validate_filter'_with_action name v r f cr cf a


inline_for_extraction noextract
let validate_with_dep_action
                    (name: string) #nz (#k:parser_kind nz _) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p)
                    (#b:bool) #inva (#la:eloc) (a: t -> action p inva la b bool)
  : Tot (validate_with_action_t #nz p (conj_inv inv inva) (eloc_union l la) false)
  = fun ctxt err input startPosition ->
    let h = HST.get () in
    [@(rename_let ("positionAfter" ^ name))]
    let res = v ctxt err input startPosition in
    let h1 = HST.get () in
    if LPL.is_error res
    then with_drop_if true (conj_inv inv inva) input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input) res
    else begin
      [@inline_let] let _ = R.readable_split h (LPL.perm_of input) (LPL.uint64_to_uint32 startPosition) (LPL.uint64_to_uint32 res) (LPL.slice_length input) in
      [@(rename_let ("" ^ name))]
      let field_value = r input (LPL.uint64_to_uint32 startPosition) in
      let h15 = HST.get () in
      let _ = modifies_address_liveness_insensitive_unused_in h h15 in
      if a field_value ctxt input startPosition res
      then res
      else with_drop_if true (conj_inv inv inva) input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input) validator_error_action_failed
    end

inline_for_extraction noextract
let validate_weaken #nz #wk (#k:parser_kind nz wk) #t (#p:parser k t)
                    #inv #l #ar (v:validate_with_action_t p inv l ar)
                    #nz' #wk' (k':parser_kind nz' wk'{k' `is_weaker_than` k})
  : Tot (validate_with_action_t (parse_weaken p k') inv l ar)
  = fun ctxt err input startPosition ->
    let open LPLC in
    let h = HST.get () in
    [@inline_let]
    let _ = valid_weaken k' p h (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition) in
    v ctxt err input startPosition

/// Parser: weakening kinds

inline_for_extraction noextract
let validate_weaken_left (#nz:_) #wk (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
                         (#inv:_) (#l:_) #ar (v:validate_with_action_t p inv l ar)
                         (#nz':_) #wk' (k':parser_kind nz' wk')
  : validate_with_action_t (parse_weaken_left p k') inv l ar
  = validate_weaken v (glb k' k)

/// Parser: weakening kinds

inline_for_extraction noextract
let validate_weaken_right (#nz:_) #wk (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
                         (#inv:_) (#l:_) #ar (v:validate_with_action_t p inv l ar)
                         (#nz':_) #wk' (k':parser_kind nz' wk')
  : validate_with_action_t (parse_weaken_right p k') inv l ar
  = validate_weaken v (glb k k')

inline_for_extraction noextract
let validate_impos ()
  : Tot (validate_with_action_t (parse_impos ()) true_inv eloc_none true)
  = fun _ _ _ _ -> validator_error_impossible

inline_for_extraction noextract
let validate_with_error
  c v
  = fun ctxt err input startPosition ->
    let endPositionOrError = v ctxt err input startPosition in
    LPL.maybe_set_error_code endPositionOrError startPosition c

noextract inline_for_extraction
let validate_ite
  e p1 v1 p2 v2
  = fun ctxt err input startPosition ->
      if e then validate_drop (v1 ()) ctxt err input startPosition else validate_drop (v2 ()) ctxt err input startPosition

unfold
let validate_list_inv
  (#k: LPL.parser_kind)
  (#t: Type)
  (p: LPL.parser k t)
  (inv: slice_inv)
  (l: loc)
  (g0 g1: Ghost.erased HS.mem)
  (#len: U32.t)
  (ctxt:app_ctxt)
  (sl: input_buffer_t len)
  (pos0: U32.t)
  (bpos: pointer U64.t)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
= let h0 = Ghost.reveal g0 in
  let h1 = Ghost.reveal g1 in
  let pos1 = Seq.index (as_seq h bpos) 0 in
  inv (LPL.slice_of sl).LPL.base h0 /\
  h `extends` h0 /\
  loc_not_unused_in h0 `loc_includes` (app_loc ctxt l) /\
  (app_loc ctxt l) `loc_disjoint` (loc_buffer (LPL.slice_of sl).LPL.base `B.loc_union` R.loc_perm (LPL.perm_of sl)) /\
  (app_loc ctxt l) `loc_disjoint` loc_buffer bpos /\
  address_liveness_insensitive_locs `loc_includes` (app_loc ctxt l) /\
  B.loc_buffer bpos `B.loc_disjoint` (B.loc_buffer (LPL.slice_of sl).LPL.base `B.loc_union` R.loc_perm (LPL.perm_of sl)) /\
  U32.v pos0 <= U32.v (LPL.slice_of sl).LPL.len /\
  LPL.live_input_buffer h0 sl /\
  LPL.live_input_buffer h sl /\
  live h0 ctxt /\
  live h ctxt /\
  live h1 bpos /\
  modifies loc_none h0 h1 /\ (
  if
    LPL.is_error pos1
  then
    stop == true
  else
    U32.v pos0 <= U64.v pos1 /\
    U64.v pos1 <= U32.v (LPL.slice_of sl).LPL.len /\
    R.readable h (LPL.perm_of sl) (LPL.uint64_to_uint32 pos1) (LPL.slice_length sl) /\
    (LPL.valid (LPLL.parse_list p) h0 (LPL.slice_of sl) pos0 <==>
     LPL.valid (LPLL.parse_list p) h0 (LPL.slice_of sl) (Cast.uint64_to_uint32 pos1)) /\
    (stop == true ==> U64.v pos1 == U32.v (LPL.slice_of sl).LPL.len)
  ) /\
  modifies (app_loc ctxt l `loc_union`
            loc_buffer bpos `loc_union`
            R.loc_perm_from_to (LPL.perm_of sl) pos0 (if LPL.is_error pos1 then LPL.slice_length sl else LPL.uint64_to_uint32 pos1)) h1 h

#push-options "--z3rlimit 128"

inline_for_extraction
noextract
let validate_list_body
  (#k:LP.parser_kind)
  #t
  (#p:LP.parser k t)
  #inv #l #ar
  (v: validate_with_action_t' p inv l ar)
  (g0 g1: Ghost.erased HS.mem)
  (ctxt:app_ctxt)
  (err:error_handler)
  (#len: U32.t)
  (sl: input_buffer_t len)
  (pos0: LPL.pos_t)
  (bpos: pointer U64.t)
: HST.Stack bool
  (requires (fun h -> validate_list_inv p inv l g0 g1 ctxt sl (LPL.uint64_to_uint32 pos0) bpos h false))
  (ensures (fun h res h' ->
    validate_list_inv p inv l g0 g1 ctxt sl (LPL.uint64_to_uint32 pos0) bpos h false /\
    validate_list_inv p inv l g0 g1 ctxt sl (LPL.uint64_to_uint32 pos0) bpos h' res
  ))
= let h = HST.get () in
  let elementStartPosition = index bpos 0ul in
  assert (U64.v elementStartPosition <= U32.v (LPL.slice_of sl).LPL.len);
  if elementStartPosition = Cast.uint32_to_uint64 (LPL.slice_length sl)
  then true
  else begin
    Classical.move_requires (LPLL.valid_list_intro_cons p (Ghost.reveal g0) (LPL.slice_of sl)) (LPL.uint64_to_uint32 elementStartPosition);
    Classical.move_requires (LPLL.valid_list_elim_cons p (Ghost.reveal g0) (LPL.slice_of sl)) (LPL.uint64_to_uint32 elementStartPosition);
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in (Ghost.reveal g0) h1;
    let elementEndPosition = v ctxt err sl elementStartPosition in
    upd bpos 0ul elementEndPosition;
    (if LPL.is_success elementEndPosition then R.readable_split h1 (LPL.perm_of sl) (LPL.uint64_to_uint32 elementStartPosition) (LPL.uint64_to_uint32 elementEndPosition) (LPL.slice_length sl));
    LPL.is_error elementEndPosition
  end

#pop-options

#push-options "--z3rlimit 64"
inline_for_extraction
noextract
let validate_list'
  (#k:LP.parser_kind)
  #t
  (#p:LP.parser k t)
  #inv #l #ar
  (v: validate_with_action_t' p inv l ar)
  (ctxt: app_ctxt)
  (err: error_handler)
  (#len: U32.t)
  (sl: input_buffer_t len)
  (pos: U64.t)
: HST.Stack U64.t
  (requires (fun h ->
    U64.v pos <= U32.v (LPL.slice_of sl).LPL.len /\
    inv (LPL.slice_of sl).LPL.base h /\
    loc_not_unused_in h `loc_includes` app_loc ctxt l /\
    app_loc ctxt l `loc_disjoint` (loc_buffer (LPL.slice_of sl).LPL.base `B.loc_union` R.loc_perm (LPL.perm_of sl)) /\
    address_liveness_insensitive_locs `loc_includes` app_loc ctxt l /\
    R.readable h (LPL.perm_of sl) (LPL.uint64_to_uint32 pos) (LPL.slice_of sl).LPL.len /\
    LPL.live_slice h (LPL.slice_of sl) /\
    B.live h ctxt
  ))
  (ensures (fun h res h' ->
    inv (LPL.slice_of sl).LPL.base h' /\
    (LPL.is_success res ==> (LPL.valid (LPLL.parse_list p) h (LPL.slice_of sl) (LPL.uint64_to_uint32 pos) /\ U64.v res == U32.v (LPL.slice_of sl).LPL.len)) /\
    modifies (app_loc ctxt l `B.loc_union`
              R.loc_perm_from_to (LPL.perm_of sl) (LPL.uint64_to_uint32 pos)
                                 (if LPL.is_success res then LPL.uint64_to_uint32 res else LPL.slice_length sl))
                                 h h' /\
    LPL.live_input_buffer h' sl /\
    B.live h' ctxt
  ))
= let h0 = HST.get () in
  let g0 = Ghost.hide h0 in
  HST.push_frame ();
  let h02 = HST.get () in
  fresh_frame_modifies h0 h02;
  let currentPosition = alloca pos 1ul in
  let h1 = HST.get () in
  let g1 = Ghost.hide h1 in
  C.Loops.do_while 
    (validate_list_inv p inv l g0 g1 ctxt sl (LPL.uint64_to_uint32 pos) currentPosition)
    (fun _ -> validate_list_body v g0 g1 ctxt err sl pos currentPosition);
  LPLL.valid_list_intro_nil p h0 (LPL.slice_of sl) (LPL.slice_of sl).LPL.len;
  let finalPositionOrError = index currentPosition 0ul in
  let h2 = HST.get () in
  HST.pop_frame ();
  let h' = HST.get () in
  assert (h' `extends` h0);
  finalPositionOrError
#pop-options

inline_for_extraction
noextract
let validate_list
  (#k:LP.parser_kind)
  #t
  (#p:LP.parser k t)
  #inv #l #ar
  (v: validate_with_action_t' p inv l ar)
: Tot (validate_with_action_t' (LowParse.Spec.List.parse_list p) inv l false)
= fun ctxt err input pos ->
  let h = HST.get () in
  Classical.move_requires (LPL.valid_pos_consumes_all (LowParse.Spec.List.parse_list p) h (LPL.slice_of input)) (LPL.uint64_to_uint32 pos);
  with_drop_if true inv input (LPL.uint64_to_uint32 pos)
    (fun (x: U64.t) -> if LPL.is_success x then LPL.uint64_to_uint32 x else LPL.slice_length input) 
    (validate_list' v ctxt err input pos)

#push-options "--z3rlimit 32"
#restart-solver
noextract
inline_for_extraction
let validate_fldata_consumes_all
  (n:U32.t)
  (#k: LP.parser_kind)
  #t
  (#p: LP.parser k t)
  #inv #l #ar
  (v: validate_with_action_t' p inv l ar  { k.LP.parser_kind_subkind == Some LP.ParserConsumesAll })
: Tot (validate_with_action_t' (LowParse.Spec.FLData.parse_fldata p (U32.v n)) inv l false)
= fun ctxt err input pos ->
  let h = HST.get () in
  LPL.valid_facts (LowParse.Spec.FLData.parse_fldata p (U32.v n)) h (LPL.slice_of input) (LPL.uint64_to_uint32 pos);
  LPLF.parse_fldata_consumes_all_correct p (U32.v n) (LPL.bytes_of_slice_from h (LPL.slice_of input) (LPL.uint64_to_uint32 pos));
  if (Cast.uint32_to_uint64 (LPL.slice_length input) `U64.sub` pos) `U64.lt` Cast.uint32_to_uint64 n
  then with_drop_if true inv input (LPL.uint64_to_uint32 pos) (fun _ -> LPL.slice_length input) LPL.validator_error_not_enough_data
  else begin
    let truncatedInput = LPL.truncate_input_buffer input (LPL.uint64_to_uint32 pos `U32.add` n) in
    LPL.valid_facts p h (LPL.slice_of truncatedInput) (LPL.uint64_to_uint32 pos);
    R.readable_split h (LPL.perm_of input) (LPL.uint64_to_uint32 pos) (LPL.slice_length truncatedInput) (LPL.slice_length input);
    with_drop_if true inv input (LPL.uint64_to_uint32 pos)
      (fun (x: U64.t) -> if LPL.is_success x then LPL.uint64_to_uint32 x else LPL.slice_length input)
      (v ctxt err truncatedInput pos)
  end
#pop-options

noextract
inline_for_extraction
let validate_nlist
  (n:U32.t)
  #wk
  (#k:parser_kind true wk)
  #t
  (#p:parser k t)
  #inv #l #ar
  (v: validate_with_action_t p inv l ar)
: Tot (validate_with_action_t (parse_nlist n p) inv l false)
= validate_weaken
    #false #WeakKindStrongPrefix #(LowParse.Spec.FLData.parse_fldata_kind (U32.v n) LowParse.Spec.List.parse_list_kind) #(list t)
    (validate_fldata_consumes_all n (validate_list v))
    kind_nlist

noextract
inline_for_extraction
let validate_nlist_constant_size_without_actions
  (n_is_const: bool)
  (n:U32.t)
  #wk
  (#k:parser_kind true wk)
  #t (#p:parser k t) #inv #l #ar
  (v: validate_with_action_t p inv l ar)
: Tot (validate_with_action_t (parse_nlist n p) inv l false)
= 
  if
    let open LP in
    k.parser_kind_subkind = Some ParserStrong &&
    k.parser_kind_high = Some k.parser_kind_low &&
    k.parser_kind_metadata = Some ParserKindMetadataTotal &&
    k.parser_kind_low < 4294967296
  then
    (fun ctxt err input startPosition ->
      let h = HST.get () in
      assert (forall h' . {:pattern (B.modifies B.loc_none h h')} (B.modifies B.loc_none h h' /\ inv (LPL.slice_of input).LPL.base h) ==> h' `extends` h);
      assert (forall h' . {:pattern (B.modifies B.loc_none h h')} (B.modifies B.loc_none h h' /\ inv (LPL.slice_of input).LPL.base h) ==> inv (LPL.slice_of input).LPL.base h');
      with_drop_if true inv input (LPL.uint64_to_uint32 startPosition) (fun (y: U64.t) -> if LPL.is_success y then LPL.uint64_to_uint32 y else LPL.slice_length input) (validate_nlist_total_constant_size n_is_const n p (FStar.Ghost.elift1 LPL.slice_of input) (LPL.slice_length input) startPosition)
    )
  else
    validate_nlist n v

#push-options "--z3rlimit 32"
#restart-solver

noextract inline_for_extraction
let validate_t_at_most' (n:U32.t) #nz #wk (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
                       (#inv:_) (#l:_) (#ar:_) (v:validate_with_action_t p inv l ar)
  : Tot (validate_with_action_t (parse_t_at_most n p) inv l ar)
  = fun ctxt err input startPosition ->
    let h = HST.get () in
    let _ =
      LPL.valid_weaken kind_t_at_most (LowParse.Spec.FLData.parse_fldata (LPC.nondep_then p LowParse.Spec.Bytes.parse_all_bytes) (U32.v n)) h (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition);
      LPL.valid_facts (LowParse.Spec.FLData.parse_fldata (LPC.nondep_then p LowParse.Spec.Bytes.parse_all_bytes) (U32.v n)) h (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition)
    in
    if (Cast.uint32_to_uint64 (LPL.slice_length input) `U64.sub` startPosition) `U64.lt` Cast.uint32_to_uint64 n
    then
      with_drop_if (not ar) inv input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input)  LPL.validator_error_not_enough_data
    else
      [@inline_let] let input' = LPL.truncate_input_buffer input (LPL.uint64_to_uint32 startPosition `U32.add` n) in
      [@inline_let] let _ = R.readable_split h (LPL.perm_of input) (LPL.uint64_to_uint32 startPosition) (LPL.slice_length input') (LPL.slice_length input) in
      [@inline_let] let _ =
        LPL.valid_facts (LPC.nondep_then p LowParse.Spec.Bytes.parse_all_bytes) h (LPL.slice_of input') (LPL.uint64_to_uint32 startPosition);
        LPLC.valid_nondep_then h p LowParse.Spec.Bytes.parse_all_bytes (LPL.slice_of input') (LPL.uint64_to_uint32 startPosition)
      in
      // FIXME: I'd need a name here
      let positionAfterContents = v ctxt err input' startPosition in
      let h1 = HST.get () in
      let _ = modifies_address_liveness_insensitive_unused_in h h1 in
      if LPL.is_error positionAfterContents
      then with_drop_if (not ar) inv input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input) positionAfterContents
      else
        [@inline_let] let _ =
          LPL.valid_facts LowParse.Spec.Bytes.parse_all_bytes h (LPL.slice_of input') (LPL.uint64_to_uint32 positionAfterContents)
        in
        with_drop_if (not ar) inv input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.uint64_to_uint32 startPosition `U32.add` n) (startPosition `U64.add` Cast.uint32_to_uint64 n)

let validate_t_at_most
  n v
= validate_drop (validate_t_at_most' n v)


#push-options "--fuel 1 --ifuel 1"
#restart-solver

noextract inline_for_extraction
let validate_t_exact' (n:U32.t) (#nz:bool) #wk (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
                       (#inv:_) (#l:_) (#ar:_) (v:validate_with_action_t p inv l ar)
  : Tot (validate_with_action_t (parse_t_exact n p) inv l ar)
  = fun ctxt err input startPosition ->
    let h = HST.get () in
    let _ =
      LPL.valid_weaken kind_t_at_most (LowParse.Spec.FLData.parse_fldata p (U32.v n)) h (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition);
      LPL.valid_facts (LowParse.Spec.FLData.parse_fldata p (U32.v n)) h (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition)
    in
    if (Cast.uint32_to_uint64 (LPL.slice_length input) `U64.sub` startPosition) `U64.lt` Cast.uint32_to_uint64 n
    then
    with_drop_if (not ar) inv input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input) LPL.validator_error_not_enough_data
    else
      [@inline_let] let input' = LPL.truncate_input_buffer input (LPL.uint64_to_uint32 startPosition `U32.add` n) in
      [@inline_let] let _ = R.readable_split h (LPL.perm_of input) (LPL.uint64_to_uint32 startPosition) (LPL.slice_length input') (LPL.slice_length input) in
      [@inline_let] let _ =
        LPL.valid_facts p h (LPL.slice_of input') (LPL.uint64_to_uint32 startPosition)
      in
      // FIXME: I'd need a name here
      let positionAfterContents = v ctxt err input' startPosition in
      let h1 = HST.get () in
      let _ = modifies_address_liveness_insensitive_unused_in h h1 in
      if LPL.is_error positionAfterContents
      then with_drop_if (not ar) inv input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input) positionAfterContents
      else if (LPL.uint64_to_uint32 positionAfterContents) <> LPL.slice_length input'
      then with_drop_if (not ar) inv input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.slice_length input) validator_error_unexpected_padding
      else with_drop_if (not ar) inv input (LPL.uint64_to_uint32 startPosition) (fun _ -> LPL.uint64_to_uint32 startPosition `U32.add` n) (startPosition `U64.add` Cast.uint32_to_uint64 n)
#pop-options

#pop-options

let validate_t_exact
  n v
= validate_drop (validate_t_exact' n v)

inline_for_extraction noextract
let validate_with_comment (c:string)
                          #nz #wk (#k:parser_kind nz wk) #t (#p:parser k t)
                          #inv #l #ar (v:validate_with_action_t p inv l ar)
  : validate_with_action_t p inv l ar
  = fun ctxt err input startPosition ->
    LowParse.Low.Base.comment c;
    v ctxt err input startPosition

inline_for_extraction noextract
let validate_weaken_inv_loc #nz #wk (#k:parser_kind nz wk) #t (#p:parser k t)
                            #inv (#l:eloc) #ar
                            (inv':slice_inv{inv' `inv_implies` inv}) (l':eloc{l' `eloc_includes` l})
                            (v:validate_with_action_t p inv l ar)
  : Tot (validate_with_action_t p inv' l' ar)
  = v

////////////////////////////////////////////////////////////////////////////////
//Base types
////////////////////////////////////////////////////////////////////////////////
inline_for_extraction noextract
let read_filter #nz
                (#k: parser_kind nz WeakKindStrongPrefix)
                (#t: Type)
                (#p: parser k t)
                (p32: leaf_reader p)
                (f: (t -> bool))
    : leaf_reader (parse_filter p f)
    = fun input startPosition ->
        let h = HST.get () in
        assert (LPL.valid #triv #triv #(filter_kind k) #(Prelude.refine t f) (parse_filter p f) h (LPL.slice_of input) startPosition);
        assert (parse_filter p f == LPC.parse_filter #k #t p f);
        assert (LPL.valid #triv #triv #(filter_kind k) #(Prelude.refine t f) (LPC.parse_filter #k #t p f) h (LPL.slice_of input) startPosition);
        assert (LPL.valid #triv #triv #(filter_kind k) #(x:t{f x}) (LPC.parse_filter #k #t p f) h (LPL.slice_of input) startPosition);
        assert (LPL.valid #triv #triv #(LPC.parse_filter_kind k) #(x:t{f x}) (LPC.parse_filter #k #t p f) h (LPL.slice_of input) startPosition);
        assert_norm (Prelude.refine t f == LPC.parse_filter_refine f);
        [@inline_let] let _ = LPLC.valid_filter h p f (LPL.slice_of input) startPosition in
        assert (LPL.valid p h (LPL.slice_of input) startPosition);
        p32 input startPosition

inline_for_extraction noextract
let validate____UINT8
  : validator parse____UINT8
  = fun ctxt err input startPosition ->
    LowStar.Comment.comment "Checking that we have enough space for a UINT8, i.e., 1 byte";
    LowParse.Low.Base.validate_total_constant_size_no_read parse____UINT8 1uL () (Ghost.elift1 LPL.slice_of (Ghost.hide input)) (LPL.slice_length input) startPosition

inline_for_extraction noextract
let read____UINT8
  : leaf_reader parse____UINT8
  = lift_constant_size_leaf_reader LowParse.Low.Int.read_u8 1ul

inline_for_extraction noextract
let validate____UINT16BE
  : validator parse____UINT16BE
  = fun ctxt err input startPosition ->
    LowStar.Comment.comment "Checking that we have enough space for a UINT16BE, i.e., 2 bytes";
    LowParse.Low.Base.validate_total_constant_size_no_read parse____UINT16BE 2uL () (Ghost.elift1 LPL.slice_of (Ghost.hide input)) (LPL.slice_length input) startPosition

inline_for_extraction noextract
let read____UINT16BE
  : leaf_reader parse____UINT16BE
  = lift_constant_size_leaf_reader LowParse.Low.Int.read_u16 2ul

inline_for_extraction noextract
let validate____UINT32BE
  : validator parse____UINT32BE
  = fun ctxt err input startPosition ->
    LowStar.Comment.comment "Checking that we have enough space for a ULONG, i.e., 4 bytes";
    LowParse.Low.Base.validate_total_constant_size_no_read parse____UINT32BE 4uL () (Ghost.elift1 LPL.slice_of (Ghost.hide input)) (LPL.slice_length input) startPosition

inline_for_extraction noextract
let read____UINT32BE
  : leaf_reader parse____UINT32BE
  = lift_constant_size_leaf_reader LowParse.Low.Int.read_u32 4ul

inline_for_extraction noextract
let validate____UINT64BE
  : validator parse____UINT64BE
  = fun ctxt err input startPosition ->
    LowStar.Comment.comment "Checking that we have enough space for a ULONG64BE, i.e., 8 bytes";
    LowParse.Low.Base.validate_total_constant_size_no_read parse____UINT64BE 8uL () (Ghost.elift1 LPL.slice_of (Ghost.hide input)) (LPL.slice_length input) startPosition

inline_for_extraction noextract
let read____UINT64BE
  : leaf_reader parse____UINT64BE
  = lift_constant_size_leaf_reader LowParse.Low.Int.read_u64 8ul

inline_for_extraction noextract
let validate____UINT16
  : validator parse____UINT16
  = fun ctxt err input startPosition ->
    LowStar.Comment.comment "Checking that we have enough space for a UINT16, i.e., 2 bytes";
    LowParse.Low.Base.validate_total_constant_size_no_read parse____UINT16 2uL () (Ghost.elift1 LPL.slice_of (Ghost.hide input)) (LPL.slice_length input) startPosition

inline_for_extraction noextract
let read____UINT16
  : leaf_reader parse____UINT16
  = lift_constant_size_leaf_reader LowParse.Low.BoundedInt.read_u16_le 2ul


inline_for_extraction noextract
let validate____UINT32
  : validator parse____UINT32
  = fun ctxt err input startPosition ->
    LowStar.Comment.comment "Checking that we have enough space for a ULONG, i.e., 4 bytes";
    LowParse.Low.Base.validate_total_constant_size_no_read parse____UINT32 4uL () (Ghost.elift1 LPL.slice_of (Ghost.hide input)) (LPL.slice_length input) startPosition

inline_for_extraction noextract
let read____UINT32
  : leaf_reader parse____UINT32
  = lift_constant_size_leaf_reader LowParse.Low.BoundedInt.read_u32_le 4ul

inline_for_extraction noextract
let validate____UINT64
  : validator parse____UINT64
  = fun ctxt err input startPosition ->
    LowStar.Comment.comment "Checking that we have enough space for a ULONG64, i.e., 8 bytes";
    LowParse.Low.Base.validate_total_constant_size_no_read parse____UINT64 8uL () (Ghost.elift1 LPL.slice_of (Ghost.hide input)) (LPL.slice_length input) startPosition

inline_for_extraction noextract
let read____UINT64
  : leaf_reader parse____UINT64
  = lift_constant_size_leaf_reader LowParse.Low.Int.read_u64_le 8ul

inline_for_extraction noextract
let validate_unit
  : validator parse_unit
  = validate_ret

inline_for_extraction noextract
let read_unit
  : leaf_reader (parse_ret ())
  = lift_constant_size_leaf_reader (LPLC.read_ret ()) 0ul

inline_for_extraction noextract
let validate_unit_refinement' (f:unit -> bool) (cf:string)
  : Tot (validate_with_action_t #false #WeakKindStrongPrefix (parse_unit `LPC.parse_filter` f) true_inv eloc_none true)
  = fun ctxt err input startPosition ->
      let h = HST.get () in
      [@inline_let] let _ = LPLC.valid_facts (parse_unit) h (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition) in
      [@inline_let] let _ = LPLC.valid_filter h parse_unit f (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition) in
      LowStar.Comment.comment cf;
      if f ()
      then
        startPosition
      else validator_error_constraint_failed

inline_for_extraction noextract
let validate_unit_refinement (f:unit -> bool) (cf:string)
  : Tot (validator (parse_unit `parse_filter` f))
  = validate_unit_refinement' f cf


(* Reimplement validate_list_up_to with readability (but no actions) *)

module LUT = LowParse.Low.ListUpTo

unfold
let validate_list_up_to_inv
  (#k: parser_kind true WeakKindStrongPrefix)
  (#t: eqtype)
  (p: parser k t)
  (terminator: t)
  (prf: LUT.consumes_if_not_cond (cond_string_up_to terminator) p)
  (ctxt: app_ctxt)
  (#len: U32.t)
  (sl: input_buffer_t len)
  (pos0: U32.t)
  (h0: HS.mem)
  (bpos: B.pointer U64.t)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
= let open LPL in
  let pos = B.deref h bpos in
  let q = LUT.parse_list_up_to (cond_string_up_to terminator) p prf in
  B.live h0 bpos /\
  live_input_buffer h0 sl /\
  live_input_buffer h sl /\
  B.loc_disjoint (B.loc_buffer (slice_of sl).LPL.base `B.loc_union` R.loc_perm (perm_of sl)) 
                 (B.loc_buffer bpos `B.loc_union` (app_loc ctxt loc_none)) /\
  B.loc_disjoint (B.loc_buffer bpos) (app_loc ctxt loc_none) /\
  B.live h0 ctxt /\
  B.live h ctxt /\  
  address_liveness_insensitive_locs `loc_includes` (app_loc ctxt loc_none) /\
  U32.v pos0 <= U64.v pos /\
  begin if is_success pos
  then
    let pos = uint64_to_uint32 pos in
    U32.v pos <= U32.v (slice_of sl).len /\
    B.modifies (app_loc ctxt loc_none `B.loc_union`
                B.loc_buffer bpos `B.loc_union`
                R.loc_perm_from_to (perm_of sl) pos0 pos) h0 h /\
    R.unreadable h (perm_of sl) pos0 pos /\
    R.readable h (perm_of sl) pos (slice_of sl).len /\
    begin if stop
    then
      valid_pos q h0 (slice_of sl) pos0 pos
    else
      (valid q h0 (slice_of sl) pos0 <==> valid q h0 (slice_of sl) pos) /\
      ((valid q h0 (slice_of sl) pos0 /\ valid q h0 (slice_of sl) pos) ==>
        get_valid_pos q h0 (slice_of sl) pos0 == get_valid_pos q h0 (slice_of sl) pos
      )
    end
  else
    U32.v pos0 <= U32.v (slice_of sl).len /\
    B.modifies (app_loc ctxt loc_none `B.loc_union`
                B.loc_buffer bpos `B.loc_union`
                R.loc_perm_from_to (perm_of sl) pos0 (slice_of sl).len) h0 h /\
    R.unreadable h (perm_of sl) pos0 (slice_of sl).len /\
    stop == true /\
    True // (~ (valid q h0 (slice_of sl) pos0)) // we lost completeness because of actions
  end

#push-options "--z3rlimit 32"

inline_for_extraction
let validate_list_up_to_body
  (#k: parser_kind true WeakKindStrongPrefix)
  (#t: eqtype)
  (#p: parser k t)
  (terminator: t)
  (prf: LUT.consumes_if_not_cond (cond_string_up_to terminator) p)
  (v: validator p)
  (r: leaf_reader p)
  (ctxt:app_ctxt)
  (err:error_handler)
  (#len: U32.t)
  (sl: input_buffer_t len)
  (pos0: U32.t)
  (h0: HS.mem)
  (bpos: B.pointer U64.t)
: HST.Stack bool
  (requires (fun h ->
    validate_list_up_to_inv p terminator prf ctxt sl pos0 h0 bpos h false
  ))
  (ensures (fun h stop h' ->
    validate_list_up_to_inv p terminator prf ctxt sl pos0 h0 bpos h false /\
    validate_list_up_to_inv p terminator prf ctxt sl pos0 h0 bpos h' stop
  ))
=
  let open LPL in
  let open LUT in
  let h = HST.get () in
  let pos = B.index bpos 0ul in
  valid_facts (parse_list_up_to (cond_string_up_to terminator) p prf) h0 (slice_of sl) (uint64_to_uint32 pos);
  parse_list_up_to_eq (cond_string_up_to terminator) p prf (bytes_of_slice_from h0 (slice_of sl) (uint64_to_uint32 pos));
  valid_facts p h0 (slice_of sl) (uint64_to_uint32 pos);
  let pos1 = v ctxt err sl pos in
  B.upd bpos 0ul pos1;
  if is_error pos1
  then begin
    drop sl (uint64_to_uint32 pos) (slice_length sl);
    let h = HST.get () in
    R.unreadable_split h (perm_of sl) pos0 (uint64_to_uint32 pos) (slice_length sl);
    true
  end else begin
    valid_facts (parse_list_up_to (cond_string_up_to terminator) p prf) h0 (slice_of sl) (uint64_to_uint32 pos1);
    let h = HST.get () in
    R.readable_split h (perm_of sl) (uint64_to_uint32 pos) (uint64_to_uint32 pos1) (slice_length sl);
    let x = r sl (uint64_to_uint32 pos) in
    let h = HST.get () in
    R.unreadable_split h (perm_of sl) pos0 (uint64_to_uint32 pos) (uint64_to_uint32 pos1);
    cond_string_up_to terminator x
  end

inline_for_extraction
noextract
let validate_list_up_to
  (#k: parser_kind true WeakKindStrongPrefix)
  (#t: eqtype)
  (#p: parser k t)
  (v: validator p)
  (r: leaf_reader p)
  (terminator: t)
  (prf: LUT.consumes_if_not_cond (cond_string_up_to terminator) p)
: Tot (validate_with_action_t #true #WeakKindStrongPrefix (LUT.parse_list_up_to (cond_string_up_to terminator) p prf) true_inv eloc_none false)
=
  fun ctxt err sl pos ->
  HST.push_frame ();
  let bpos = B.alloca pos 1ul in
  let h2 = HST.get () in
  R.unreadable_empty h2 (LPL.perm_of sl) (LPL.uint64_to_uint32 pos);
  C.Loops.do_while
    (validate_list_up_to_inv p terminator prf ctxt sl (LPL.uint64_to_uint32 pos) h2 bpos)
    (fun _ -> validate_list_up_to_body terminator prf v r ctxt err sl (LPL.uint64_to_uint32 pos) h2 bpos)
    ;
  let res = B.index bpos 0ul in
  HST.pop_frame ();
  res

#pop-options

let validate_string
  #k #t #p v r terminator
=
  LP.parser_kind_prop_equiv k p;
  validate_weaken (validate_list_up_to v r terminator (fun _ _ _ -> ())) _

#restart-solver

inline_for_extraction noextract
let validate_all_bytes2 : validate_with_action_t parse_all_bytes true_inv eloc_none true =
  fun ctxt err #inputLength input startPosition ->
    let h = HST.get () in
    LPL.valid_facts LowParse.Spec.Bytes.parse_all_bytes h (LPL.slice_of input) (LPL.uint64_to_uint32 startPosition);
    FStar.Int.Cast.uint32_to_uint64 inputLength

let validate_all_bytes = validate_drop validate_all_bytes2

let validate_all_zeros =
  validate_list (validate_filter "parse_zeros" validate____UINT8 read____UINT8 is_zero "check if zero" "")

////////////////////////////////////////////////////////////////////////////////

noextract
inline_for_extraction
let action_return
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#a:Type) (x:a)
  : action p true_inv eloc_none false a
  = fun _ input startPosition endPosition -> x

noextract
inline_for_extraction
let action_bind
      (name: string)
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#invf:slice_inv) (#lf:eloc)
      #bf (#a:Type) (f: action p invf lf bf a)
      (#invg:slice_inv) (#lg:eloc) #bg
      (#b:Type) (g: (a -> action p invg lg bg b))
  : Tot (action p (conj_inv invf invg) (eloc_union lf lg) (bf || bg) b)
  = fun ctxt input startPosition endPosition ->
    let h0 = HST.get () in
    [@(rename_let ("" ^ name))]
    let x = f ctxt input startPosition endPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    g x ctxt input startPosition endPosition

noextract
inline_for_extraction
let action_seq
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#invf:slice_inv) (#lf:eloc)
      #bf (#a:Type) (f: action p invf lf bf a)
      (#invg:slice_inv) (#lg:eloc) #bg
      (#b:Type) (g: action p invg lg bg b)
  : Tot (action p (conj_inv invf invg) (eloc_union lf lg) (bf || bg) b)
  = fun ctxt input startPosition endPosition ->
    let h0 = HST.get () in
    let _ = f ctxt input startPosition endPosition in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    g ctxt input startPosition endPosition

noextract
inline_for_extraction
let action_ite
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#invf:slice_inv) (#lf:eloc)
      (guard:bool)
      #bf (#a:Type) (then_: squash guard -> action p invf lf bf a)
      (#invg:slice_inv) (#lg:eloc) #bg
      (else_: squash (not guard) -> action p invg lg bg a)
  : action p (conj_inv invf invg) (eloc_union lf lg) (bf || bg) a
  = fun ctxt input startPosition endPosition ->
      if guard 
      then then_ () ctxt input startPosition endPosition 
      else else_ () ctxt input startPosition endPosition

noextract
inline_for_extraction
let action_abort
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
  : action p true_inv eloc_none false bool
  = fun _ input startPosition endPosition -> false

noextract
inline_for_extraction
let action_field_pos
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t) (u:unit)
   : action p true_inv eloc_none false U32.t
   = fun _ _ startPosition _ -> LPL.uint64_to_uint32 startPosition


noextract
inline_for_extraction
let action_field_ptr
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t) (u:unit)
   : action p true_inv eloc_none true LPL.puint8
   = fun _ input startPosition _ ->
       let open LowParse.Slice in
       LPL.offset input (LPL.uint64_to_uint32 startPosition)

noextract
inline_for_extraction
let action_deref
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#a:_) (x:B.pointer a)
   : action p (ptr_inv x) loc_none false a
   = fun _ _ _ _ -> !*x

noextract
inline_for_extraction
let action_assignment
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#a:_) (x:B.pointer a) (v:a)
   : action p (ptr_inv x) (ptr_loc x) false unit
   = fun _ _ _ _ -> x *= v

(* FIXME: This is now unsound.
noextract
inline_for_extraction
let action_read_value
      #nz (#k:parser_kind nz) (#t:Type) (#p:parser k t)
      (r:leaf_reader p)
   : action p true_inv eloc_none true t
   = fun input startPosition endPosition ->
     r input (LPL.uint64_to_uint32 startPosition)
*)

noextract
inline_for_extraction
let action_weaken
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#inv:slice_inv) (#l:eloc) (#b:_) (#a:_) (act:action p inv l b a)
      (#inv':slice_inv{inv' `inv_implies` inv}) (#l':eloc{l' `eloc_includes` l})
   : action p inv' l' b a
   = act
