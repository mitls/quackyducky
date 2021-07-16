module EverParse3d.Actions
friend Prelude

module LPE = LowParse.Low.ErrorCode
open FStar.Tactics.Typeclasses

(* TODO: use an interface, and implementations under subdirectories, and do the include dir trick *)
inline_for_extraction
noextract
let input_buffer_t = EverParse3d.InputStream.Buffer.t

let action
  p inv l on_success a
=
    sl: Ghost.erased input_buffer_t ->
    pos: U32.t -> // position before validation
    Stack a
      (requires fun h ->
        let sl = Ghost.reveal sl in
        I.live sl h /\
        inv (I.footprint sl) h /\
        loc_not_unused_in h `loc_includes` l /\
        address_liveness_insensitive_locs `loc_includes` l /\
        l `loc_disjoint` I.footprint sl /\
        U32.v pos <= Seq.length (I.get_read sl h)
      )
      (ensures fun h0 _ h1 ->
        let sl = Ghost.reveal sl in
        modifies l h0 h1 /\
        h1 `extends` h0 /\
        inv (I.footprint sl) h1)

module LP = LowParse.Spec.Base
module LPL = LowParse.Low.Base

unfold
let valid_consumed
  (#input_buffer_t: Type0)
  (# [tcresolve ()] inst : I.input_stream_inst input_buffer_t)
  (#k: LP.parser_kind)
  (#t: Type)
  (p: LP.parser k t)
  (h: HS.mem)
  (h': HS.mem)
  (sl: input_buffer_t)
: Tot prop
= I.live sl h /\
  I.live sl h' /\
  begin
    let s = I.get_remaining sl h in
    begin match LP.parse p s with
    | None -> False
    | Some (_, len) -> I.get_remaining sl h' `Seq.equal` Seq.slice s len (Seq.length s)
    end
  end

unfold
let valid_length
  (#input_buffer_t: Type0)
  (# [tcresolve ()] inst : I.input_stream_inst input_buffer_t)
  (#k: LP.parser_kind)
  (#t: Type)
  (p: LP.parser k t)
  (h: HS.mem)
  (sl: input_buffer_t)
  (len: int)
: Tot prop
= I.live sl h /\
  begin
    let s = I.get_remaining sl h in
    begin match LP.parse p s with
    | None -> False
    | Some (_, len') -> len == len'
    end
  end

let valid
  (#input_buffer_t: Type0)
  (# [tcresolve ()] inst : I.input_stream_inst input_buffer_t)
  (#k: LP.parser_kind)
  (#t: Type)
  (p: LP.parser k t)
  (h: HS.mem)
  (sl: input_buffer_t)
: Tot prop
= I.live sl h /\
  Some? (LP.parse p (I.get_remaining sl h))

inline_for_extraction noextract
let validate_with_action_t' (#k:LP.parser_kind) (#t:Type) (p:LP.parser k t) (inv:slice_inv) (l:eloc) (allow_reading:bool) =
  (sl: input_buffer_t) ->
  Stack U64.t
  (requires fun h ->
    I.live sl h /\
    inv (I.footprint sl) h /\
    loc_not_unused_in h `loc_includes` l /\
    address_liveness_insensitive_locs `loc_includes` l /\
    l `loc_disjoint` I.footprint sl
  )
  (ensures fun h res h' ->
    I.live sl h' /\
    modifies (l `loc_union` I.footprint sl) h h' /\
    h' `extends` h /\
    inv (I.footprint sl) h' /\
    begin let s = I.get_remaining sl h in
    if LPE.is_success res
    then
      begin if allow_reading
      then valid_length p h sl (U64.v res) /\ I.get_remaining sl h' == s
      else valid_consumed p h h' sl
      end
    else
      let s' = I.get_remaining sl h' in
      Seq.length s' <= Seq.length s /\
      s' `Seq.equal` Seq.slice s (Seq.length s - Seq.length s') (Seq.length s)
    end
    )

let validate_with_action_t p inv l allow_reading = validate_with_action_t' p inv l allow_reading

let validate_eta v =
  fun sl -> v sl

let act_with_comment
  s res a
=
  fun sl pos ->
  LPL.comment s;
  a sl pos

let leaf_reader
  #nz
  #k
  (#t: Type)
  (p: parser k t)
: Tot Type
=
  (sl: input_buffer_t) ->
  Stack t
  (requires (fun h ->
    valid p h sl
  ))
  (ensures (fun h res h' ->
    let s = I.get_remaining sl h in
    I.live sl h' /\
    modifies (I.footprint sl) h h' /\
    h' `extends` h /\
    begin match LP.parse p s with
    | None -> False
    | Some (y, len) ->
      res == y /\
      I.get_remaining sl h' == Seq.slice s len (Seq.length s)
    end
  ))

inline_for_extraction
noextract
let validate_with_success_action' (name: string) #nz #wk (#k1:parser_kind nz wk) #t1 (#p1:parser k1 t1) (#inv1:_) (#l1:eloc) (#ar:_)
                         (v1:validate_with_action_t p1 inv1 l1 ar)
                         (#inv2:_) (#l2:eloc) #b (a:action p1 inv2 l2 b bool)
  : validate_with_action_t p1 (conj_inv inv1 inv2) (l1 `eloc_union` l2) ar
  = fun input ->
    let h0 = HST.get () in
    [@(rename_let ("positionBefore" ^ name))]
    let pos0 = I.get_read_count input in
    let h05 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h05;
    assert (h05 `extends` h0);
    [@(rename_let ("resultAfter" ^ name))]
    let pos1 = v1 input in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    if LPL.is_success pos1
    then
         [@(rename_let ("action_success_" ^ name))]
         let b = a input pos0 in
         if not b
         then validator_error_action_failed
         else pos1
    else
         pos1

inline_for_extraction
noextract
let validate_drop_true
   (#k:LP.parser_kind) (#t:Type) (#p:LP.parser k t) (#inv:slice_inv) (#l:eloc) (v: validate_with_action_t' p inv l true)
: Tot (validate_with_action_t' p inv l false)
= fun input ->
  let res = v input in
  if LPE.is_success res
  then begin
    let h1 = HST.get () in
    I.skip input (LPE.uint64_to_uint32 res);
    let h2 = HST.get () in
    assert (h2 `extends` h1)
  end;
  res

inline_for_extraction
noextract
let validate_drop
   (#k:LP.parser_kind) (#t:Type) (#p:LP.parser k t) (#inv:slice_inv) (#l:eloc) #allow_reading (v: validate_with_action_t' p inv l allow_reading)
: Tot (validate_with_action_t' p inv l false)
= if allow_reading
  then validate_drop_true v
  else v

let validate_with_success_action
  name v1 a
= validate_drop (validate_with_success_action' name v1 a)

inline_for_extraction noextract
let validate_with_error_action' (name: string) #nz #wk (#k1:parser_kind nz wk) #t1 (#p1:parser k1 t1) (#inv1:_) (#l1:eloc) (#ar:_)
                         (v1:validate_with_action_t p1 inv1 l1 ar)
                         (#inv2:_) (#l2:eloc) (a:action p1 inv2 l2 false bool)
  : validate_with_action_t p1 (conj_inv inv1 inv2) (l1 `eloc_union` l2) ar
  = fun input ->
    let h0 = HST.get () in
    [@(rename_let ("positionBefore" ^ name))]
    let pos0 = I.get_read_count input in
    let h05 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h05;
    assert (h05 `extends` h0);
    [@(rename_let ("resultAfter" ^ name))]
    let pos1 = v1 input in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    if LPL.is_success pos1
    then pos1
    else
         [@(rename_let ("actionError" ^ name))]
         let b = a input pos0 in
         if not b then validator_error_action_failed else pos1

let validate_with_error_action
  name v1 a
= validate_drop (validate_with_error_action' name v1 a)

inline_for_extraction noextract
let validate_ret
  : validate_with_action_t (parse_ret ()) true_inv eloc_none true
  = fun input ->
    0uL

#push-options "--z3rlimit 16"

module LPC = LowParse.Spec.Combinators

inline_for_extraction noextract
let validate_pair
       (name1: string)
       #nz1 (#k1:parser_kind nz1 WeakKindStrongPrefix) #t1 (#p1:parser k1 t1)
       (#inv1:_) (#l1:eloc) (#ar1:_) (v1:validate_with_action_t p1 inv1 l1 ar1)
       #nz2 #wk2 (#k2:parser_kind nz2 wk2) #t2 (#p2:parser k2 t2)
       (#inv2:_) (#l2:eloc) (#ar2:_) (v2:validate_with_action_t p2 inv2 l2 ar2)
  : validate_with_action_t (p1 `parse_pair` p2) (conj_inv inv1 inv2) (l1 `eloc_union` l2) false
  = fun input ->
    let h = HST.get () in
    LPC.nondep_then_eq p1 p2 (I.get_remaining input h);
    [@(rename_let ("resultAfter" ^ name1))]
    let pos1 = validate_drop v1 input in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h1;
    if LPL.is_error pos1
    then
      pos1
    else
      validate_drop v2 input

inline_for_extraction noextract
let validate_dep_pair
      (name1: string)
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2:t1 -> Type) (#p2:(x:t1 -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:t1 -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t (p1 `parse_dep_pair` p2) (conj_inv inv1 inv2) (l1 `eloc_union` l2) false)
  = fun input ->
      let h = HST.get () in
      LPC.parse_dtuple2_eq p1 p2 (I.get_remaining input h);
      [@(rename_let ("resultAfter" ^ name1))]
      let pos1 = v1 input in
      let h1 = HST.get() in
      if LPL.is_error pos1
      then begin
        pos1
      end
      else
        [@(rename_let ("" ^ name1))]
        let x = r1 input in
        let h15 = HST.get () in
        let _ = modifies_address_liveness_insensitive_unused_in h h15 in
        validate_drop (v2 x) input

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action'
      (name1: string)
      (id1: field_id)
      (#nz1: _) (#k1:parser_kind nz1 _) (#t1: _) (#p1:parser k1 t1)
      (#inv1: _) (#l1: _) (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      (#inv1': _) (#l1': _) (#b: _) (a:t1 -> action p1 inv1' l1' b bool)
      (#nz2: _) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f) -> parser k2 (t2 x))
      (#inv2: _) (#l2: _) (#ar2: _) (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 (conj_inv inv1' inv2))
             (l1 `eloc_union` (l1' `eloc_union` l2))
             false)
  =
  fun input ->
      let h0 = HST.get () in
      let startPosition = I.get_read_count input in
      let h05 = HST.get () in
      assert (h05 `extends` h0);
      modifies_address_liveness_insensitive_unused_in h0 h05;
      LPC.parse_dtuple2_eq' #_ #_ (p1 `LPC.parse_filter` f) #_ #t2 p2 (I.get_remaining input h0);
      LPC.parse_filter_eq p1 f (I.get_remaining input h0);
      [@(rename_let ("resultAfter" ^ name1))]
      let res = v1 input in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPL.is_error res
      then begin
        res
      end
      else begin
        assert (I.get_remaining input h1 == I.get_remaining input h0);
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("resultAfter" ^ name1))]
        let res1 = check_constraint_ok_with_field_id ok (Cast.uint32_to_uint64 startPosition) res id1 in
        let h2 = HST.get() in
        if LPL.is_error res1
        then
          res1
        else begin
             modifies_address_liveness_insensitive_unused_in h1 h2;
             if not (a field_value input startPosition)
             then (LPL.set_validator_error_pos_and_code validator_error_action_failed (Cast.uint32_to_uint64 startPosition) id1) //action failed
             else begin
               let open LPL in
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               validate_drop (v2 field_value) input
             end
        end
      end

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action_total_zero_parser'
      (name1: string)
      (id1: field_id)
      (#nz1: _) (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1: _) (#p1:parser k1 t1) (r1: leaf_reader p1)
      (inv1: _) (l1: _)
      (f: t1 -> bool)
      (#inv1': _) (#l1': _) (#b: _) (a:t1 -> action p1 inv1' l1' b bool)
      (#nz2: _) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      (#inv2: _) (#l2: _) (#ar2: _) (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
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
  = fun input ->
      let h0 = HST.get () in
      let startPosition = I.get_read_count input in
      let h05 = HST.get () in
      assert (h05 `extends` h0);
      modifies_address_liveness_insensitive_unused_in h0 h05;
      LPC.parse_dtuple2_eq' #_ #_ (p1 `LPC.parse_filter` f) #_ #t2 p2 (I.get_remaining input h0);
      LPC.parse_filter_eq p1 f (I.get_remaining input h0);
      [@inline_let] let _ = LP.parser_kind_prop_equiv k1 p1 in
      begin
        LowStar.Comment.comment ("Validating field " ^ name1);
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("resultAfter" ^ name1))]
        let res1 = check_constraint_ok_with_field_id ok (Cast.uint32_to_uint64 startPosition) (Cast.uint32_to_uint64 startPosition) id1 in
        if LPL.is_error res1
        then
             res1
        else let h2 = HST.get() in
             modifies_address_liveness_insensitive_unused_in h0 h2;
             if not (a field_value input startPosition)
             then (LPL.set_validator_error_pos_and_code validator_error_action_failed (Cast.uint32_to_uint64 startPosition) id1) //action failed
             else begin
               let open LPL in
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               validate_drop (v2 field_value) input
             end
        end

inline_for_extraction noextract
let validate_dep_pair_with_refinement_and_action
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (id1: field_id)
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
      validate_dep_pair_with_refinement_and_action_total_zero_parser' name1 id1 r1 inv1 l1 f a v2
    else
      validate_dep_pair_with_refinement_and_action' name1 id1 v1 r1 f a v2


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
  = fun input ->
      let h0 = HST.get () in
      LPC.parse_dtuple2_eq' #_ #_ p1 #_ #t2 p2 (I.get_remaining input h0);
      let startPosition = I.get_read_count input in
      let h05 = HST.get () in
      modifies_address_liveness_insensitive_unused_in h0 h05;
      assert (h05 `extends` h0);
      let res = v1 input in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPL.is_error res
      then begin
        res
      end
      else begin
        let field_value = r1 input in
        let h2 = HST.get() in
        modifies_address_liveness_insensitive_unused_in h1 h2;
        let action_result = a field_value input startPosition in
        if not action_result
        then validator_error_action_failed //action failed
        else begin
               let open LPL in
               let h15 = HST.get () in
               let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
               validate_drop (v2 field_value) input
             end
      end

inline_for_extraction noextract
let validate_dep_pair_with_refinement'
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      #inv1 #l1 (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      #inv2 #l2 #ar2 (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 ar2))
  : Tot (validate_with_action_t
             ((p1 `LPC.parse_filter` f) `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 inv2)
             (l1 `eloc_union` l2)
             false)
  = fun input ->
      let h0 = HST.get () in
      let startPosition = I.get_read_count input in
      let startPosition = Cast.uint32_to_uint64 startPosition in
      let h05 = HST.get () in
      assert (h05 `extends` h0);
      modifies_address_liveness_insensitive_unused_in h0 h05;
      LPC.parse_dtuple2_eq' #_ #_ (p1 `LPC.parse_filter` f) #_ #t2 p2 (I.get_remaining input h0);
      LPC.parse_filter_eq p1 f (I.get_remaining input h0);
      [@(rename_let ("resultAfter" ^ name1))]
      let res = v1 input in
      let h1 = HST.get() in
      modifies_address_liveness_insensitive_unused_in h0 h1;
      if LPL.is_error res
      then begin
        res
      end
      else begin
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("resultAfter" ^ name1))]
        let res1 = check_constraint_ok_with_field_id ok startPosition res id1 in
        if LPL.is_error res1
        then
             res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h1 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             let open LPL in
             // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
             let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
             validate_drop (v2 field_value) input
        end

inline_for_extraction noextract
let validate_dep_pair_with_refinement_total_zero_parser'
      (name1: string)
      (id1: field_id)
      #nz1 (#k1:parser_kind nz1 _) #t1 (#p1:parser k1 t1)
      (inv1: _) (l1: _) (r1: leaf_reader p1)
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
  = fun input ->
      let h0 = HST.get () in
      let startPosition = I.get_read_count input in
      let startPosition = Cast.uint32_to_uint64 startPosition in
      let h05 = HST.get () in
      assert (h05 `extends` h0);
      modifies_address_liveness_insensitive_unused_in h0 h05;
      LPC.parse_dtuple2_eq' #_ #_ (p1 `LPC.parse_filter` f) #_ #t2 p2 (I.get_remaining input h0);
      LPC.parse_filter_eq p1 f (I.get_remaining input h0);
      [@inline_let] let _ = LP.parser_kind_prop_equiv k1 p1 in
      begin
        LowStar.Comment.comment ("Validating field " ^ name1);
        [@(rename_let ("" ^ name1))]
        let field_value = r1 input in
        [@(rename_let (name1 ^ "ConstraintIsOk"))]
        let ok = f field_value in
        [@(rename_let ("resultAfter" ^ name1))]
        let res1 = check_constraint_ok_with_field_id ok startPosition startPosition id1 in
        if LPL.is_error res1
        then res1
        else let h2 = HST.get() in
             // assert (B.modifies B.loc_none h1 h2);
             // assert (inv1' input.LPL.base h2);
             modifies_address_liveness_insensitive_unused_in h0 h2;
             // assert (loc_not_unused_in h2 `loc_includes` l1');
             let open LPL in
             // assert (valid_pos (p1 `(LPC.parse_filter #k1 #t1)` f) h0 input (uint64_to_uint32 pos) (uint64_to_uint32 res));
             let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h0 h15 in
             validate_drop (v2 field_value) input
        end

inline_for_extraction noextract
let validate_dep_pair_with_refinement
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (id1: field_id)
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
      validate_dep_pair_with_refinement_total_zero_parser' name1 id1 inv1 l1 r1 f v2
    else
      validate_dep_pair_with_refinement' name1 id1 v1 r1 f v2

inline_for_extraction noextract
let validate_filter (name: string) #nz (#k:parser_kind nz _) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
  : Tot (validate_with_action_t #nz #WeakKindStrongPrefix (p `LPC.parse_filter` f) inv l false)
  = fun input ->
    let h = HST.get () in
    LPC.parse_filter_eq p f (I.get_remaining input h);
    [@(rename_let ("resultAfter" ^ name))]
    let res = v input in
    let h1 = HST.get () in
    if LPL.is_error res
    then res
    else begin
      LowStar.Comment.comment cr;
      [@(rename_let ("" ^ name))]
      let field_value = r input in
      LowStar.Comment.comment (normalize_term ("start: " ^cf));
      [@(rename_let (name ^ "ConstraintIsOk"))]
      let ok = f field_value in
      LowStar.Comment.comment (normalize_term ("end: " ^ cf));
      check_constraint_ok ok res
    end

inline_for_extraction noextract
let validate_filter_with_action
                    (name: string) #nz (#k:parser_kind nz _) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
                    (#b:bool) #inva (#la:eloc) (a: t -> action #nz #WeakKindStrongPrefix #(filter_kind k) #_ (p `LPC.parse_filter` f) inva la b bool)
  : Tot (validate_with_action_t #nz #WeakKindStrongPrefix (p `LPC.parse_filter` f) (conj_inv inv inva) (eloc_union l la) false)
  = fun input ->
    let h = HST.get () in
    LPC.parse_filter_eq p f (I.get_remaining input h);
    [@(rename_let ("positionBefore" ^ name))]
    let pos0 = I.get_read_count input in
    let h05 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h05;
    assert (h05 `extends` h);
    [@(rename_let ("resultAfter" ^ name))]
    let res = v input in
    let h1 = HST.get () in
    if LPL.is_error res
    then res
    else begin
      LowStar.Comment.comment cr;
      [@(rename_let ("" ^ name))]
      let field_value = r input in
      LowStar.Comment.comment (normalize_term ("start: " ^cf));
      [@(rename_let (name ^ "ConstraintIsOk"))]
      let ok = f field_value in
      LowStar.Comment.comment (normalize_term ("end: " ^ cf));
      if ok
        then let h15 = HST.get () in
             let _ = modifies_address_liveness_insensitive_unused_in h h15 in
             if a field_value input pos0
             then res
             else validator_error_action_failed
      else validator_error_constraint_failed
    end

inline_for_extraction noextract
let validate_with_dep_action
                    (name: string) #nz (#k:parser_kind nz _) (#t:_) (#p:parser k t)
                    #inv #l (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p)
                    (#b:bool) #inva (#la:eloc) (a: t -> action p inva la b bool)
  : Tot (validate_with_action_t #nz p (conj_inv inv inva) (eloc_union l la) false)
  = fun input ->
    let h = HST.get () in
    [@(rename_let ("positionBefore" ^ name))]
    let pos0 = I.get_read_count input in
    let h05 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h05;
    assert (h05 `extends` h);
    [@(rename_let ("resultAfter" ^ name))]
    let res = v input in
    let h1 = HST.get () in
    if LPL.is_error res
    then res
    else begin
      [@(rename_let ("" ^ name))]
      let field_value = r input in
      let h15 = HST.get () in
      let _ = modifies_address_liveness_insensitive_unused_in h h15 in
      if a field_value input pos0
      then res
      else validator_error_action_failed
    end

inline_for_extraction noextract
let validate_weaken #nz #wk (#k:parser_kind nz wk) #t (#p:parser k t)
                    #inv #l #ar (v:validate_with_action_t p inv l ar)
                    #nz' #wk' (k':parser_kind nz' wk'{k' `is_weaker_than` k})
  : Tot (validate_with_action_t (parse_weaken p k') inv l ar)
  = fun input ->
    v input


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
  = fun _ -> validator_error_impossible

inline_for_extraction noextract
let validate_with_error
  c v
  = fun input ->
    let h = HST.get () in
    let startPosition = I.get_read_count input in
    let startPosition = Cast.uint32_to_uint64 startPosition in
    let h05 = HST.get () in
    assert (h05 `extends` h);
    modifies_address_liveness_insensitive_unused_in h h05;
    let result = v input in
    LPL.maybe_set_error_code result startPosition c

noextract inline_for_extraction
let validate_ite
  e p1 v1 p2 v2
  = fun input ->
      if e then validate_drop (v1 ()) input else validate_drop (v2 ()) input

module LPLL = LowParse.Spec.List

unfold
let validate_list_inv
  (#k: LPL.parser_kind)
  (#t: Type)
  (p: LPL.parser k t)
  (inv: slice_inv)
  (l: loc)
  (g0 g1: Ghost.erased HS.mem)
  (sl: input_buffer_t)
  (bres: pointer U64.t)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
= let h0 = Ghost.reveal g0 in
  let h1 = Ghost.reveal g1 in
  let res = Seq.index (as_seq h bres) 0 in
  inv (I.footprint sl) h0 /\
  h `extends` h0 /\
  loc_not_unused_in h0 `loc_includes` l /\
  l `loc_disjoint` I.footprint sl /\
  l `loc_disjoint` loc_buffer bres /\
  address_liveness_insensitive_locs `loc_includes` l /\
  B.loc_buffer bres `B.loc_disjoint` I.footprint sl /\
  I.live sl h0 /\
  I.live sl h /\
  live h1 bres /\
  begin
    let s = I.get_remaining sl h0 in
    let s' = I.get_remaining sl h in
    Seq.length s' <= Seq.length s /\
    s' `Seq.equal` Seq.slice s (Seq.length s - Seq.length s') (Seq.length s)
  end /\
  modifies loc_none h0 h1 /\ (
  if
    LPL.is_error res
  then
    // validation *or action* failed
    stop == true
  else
    (valid (LPLL.parse_list p) h0 sl <==>
     valid (LPLL.parse_list p) h sl) /\
    (stop == true ==> (valid (LPLL.parse_list p) h sl /\ Seq.length (I.get_remaining sl h) == 0))
  ) /\
  modifies (l `loc_union` loc_buffer bres `loc_union` I.footprint sl) h1 h

inline_for_extraction
noextract
let validate_list_body
  (#k:LP.parser_kind)
  #t
  (#p:LP.parser k t)
  #inv #l #ar
  (v: validate_with_action_t' p inv l ar)
  (g0 g1: Ghost.erased HS.mem)
  (sl: input_buffer_t)
  (bres: pointer U64.t)
: HST.Stack bool
  (requires (fun h -> validate_list_inv p inv l g0 g1 sl bres h false))
  (ensures (fun h res h' ->
    validate_list_inv p inv l g0 g1 sl bres h false /\
    validate_list_inv p inv l g0 g1 sl bres h' res
  ))
= let h = HST.get () in
  LPLL.parse_list_eq p (I.get_remaining sl h);
  if not (I.has sl 1ul)
  then true
  else begin
    let h1 = HST.get () in
    assert (h1 `extends` Ghost.reveal g0);
    modifies_address_liveness_insensitive_unused_in (Ghost.reveal g0) h1;
    let result = v sl in
    upd bres 0ul result;
    LPL.is_error result
  end

inline_for_extraction
noextract
let validate_list'
  (#k:LP.parser_kind)
  #t
  (#p:LP.parser k t)
  #inv #l #ar
  (v: validate_with_action_t' p inv l ar)
  (sl: input_buffer_t)
: HST.Stack U64.t
  (requires (fun h ->
    inv (I.footprint sl) h /\
    loc_not_unused_in h `loc_includes` l /\
    l `loc_disjoint` I.footprint sl /\
    address_liveness_insensitive_locs `loc_includes` l /\
    I.live sl h
  ))
  (ensures (fun h res h' ->
    let s = I.get_remaining sl h in
    inv (I.footprint sl) h' /\
    I.live sl h' /\
    begin
      let s' = I.get_remaining sl h' in
      Seq.length s' <= Seq.length s /\
      s' `Seq.equal` Seq.slice s (Seq.length s - Seq.length s') (Seq.length s)
    end /\
    (LPL.is_success res ==> begin match LP.parse (LPLL.parse_list p) s with
    | None -> False
    | Some (_, len) -> I.get_remaining sl h' `Seq.equal` Seq.slice s len (Seq.length s)
    end) /\
    modifies (l `B.loc_union` I.footprint sl) h h'
  ))
= let h0 = HST.get () in
  let g0 = Ghost.hide h0 in
  HST.push_frame ();
  let h02 = HST.get () in
  fresh_frame_modifies h0 h02;
  let result = alloca 0uL 1ul in
  let h1 = HST.get () in
  let g1 = Ghost.hide h1 in
  I.live_not_unused_in sl h0;
  C.Loops.do_while (validate_list_inv p inv l g0 g1 sl result) (fun _ -> validate_list_body v g0 g1 sl result);
  let finalResult = index result 0ul in
  let h2 = HST.get () in
  HST.pop_frame ();
  let h' = HST.get () in
  assert (h' `extends` h0);
  LP.parser_kind_prop_equiv LPLL.parse_list_kind (LPLL.parse_list p);
  finalResult

inline_for_extraction
noextract
let validate_list
  (#k:LP.parser_kind)
  #t
  (#p:LP.parser k t)
  #inv #l #ar
  (v: validate_with_action_t' p inv l ar)
: Tot (validate_with_action_t' (LowParse.Spec.List.parse_list p) inv l false)
= fun input ->
  validate_list' v input

#push-options "--z3rlimit 32"
#restart-solver

module LPLF = LowParse.Low.FLData

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
= fun input ->
  let h = HST.get () in
  LPLF.parse_fldata_consumes_all_correct p (U32.v n) (I.get_remaining input h);
  let hasEnoughBytes = I.has input n in
  let h1 = HST.get () in
  modifies_address_liveness_insensitive_unused_in h h1;
  assert (h1 `extends` h);
  if not hasEnoughBytes
  then LPL.validator_error_not_enough_data
  else begin
    let truncatedInput = I.truncate input n in
    let h2 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h2;
    assert (h2 `extends` h);
    I.is_prefix_of_prop truncatedInput input h2;
    assert (I.get_remaining truncatedInput h2 `Seq.equal` Seq.slice (I.get_remaining input h) 0 (U32.v n));
    let res = validate_drop v truncatedInput in
    let h3 = HST.get () in
    I.is_prefix_of_prop truncatedInput input h3;
    res
  end
#pop-options

noextract
inline_for_extraction
let validate_fldata
  (n:U32.t)
  (#k: LP.parser_kind)
  #t
  (#p: LP.parser k t)
  #inv #l #ar
  (v: validate_with_action_t' p inv l ar)
: Tot (validate_with_action_t' (LowParse.Spec.FLData.parse_fldata p (U32.v n)) inv l false)
= fun input ->
  let h = HST.get () in
  let hasEnoughBytes = I.has input n in
  let h1 = HST.get () in
  modifies_address_liveness_insensitive_unused_in h h1;
  assert (h1 `extends` h);
  if not hasEnoughBytes
  then LPL.validator_error_not_enough_data
  else begin
    let truncatedInput = I.truncate input n in
    let h2 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h2;
    assert (h2 `extends` h);
    I.is_prefix_of_prop truncatedInput input h2;
    assert (I.get_remaining truncatedInput h2 `Seq.equal` Seq.slice (I.get_remaining input h) 0 (U32.v n));
    let res = validate_drop v truncatedInput in
    let h3 = HST.get () in
    I.is_prefix_of_prop truncatedInput input h3;
    if LPE.is_error res
    then res
    else begin
      let stillHasBytes = I.has truncatedInput 1ul in
      let h4 = HST.get () in
      modifies_address_liveness_insensitive_unused_in h h4;
      assert (h4 `extends` h);
      if stillHasBytes
      then ResultOps.validator_error_unexpected_padding
      else res
    end
  end

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

inline_for_extraction
noextract
let validate_total_constant_size_no_read'
  (#k: LP.parser_kind)
  (#t: Type)
  (p: LP.parser k t)
  (sz: U32.t)
  (u: unit {
    k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
    k.LP.parser_kind_low == U32.v sz /\
    k.LP.parser_kind_metadata == Some LP.ParserKindMetadataTotal
  })
  inv l
: Tot (validate_with_action_t' p inv l true)
= fun input ->
  let h = HST.get () in
  LP.parser_kind_prop_equiv k p; 
  let hasBytes = I.has input sz in
  let h2 = HST.get () in
  modifies_address_liveness_insensitive_unused_in h h2;
  assert (h2 `extends` h);
  if hasBytes
  then Cast.uint32_to_uint64 sz
  else LPE.validator_error_not_enough_data

inline_for_extraction
noextract
let validate_total_constant_size_no_read
  #nz #wk
  (#k: parser_kind nz wk)
  (#t: Type)
  (p: parser k t)
  (sz: U32.t)
  (u: unit {
    k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
    k.LP.parser_kind_low == U32.v sz /\
    k.LP.parser_kind_metadata == Some LP.ParserKindMetadataTotal
  })
  inv l
: Tot (validate_with_action_t p inv l true)
= validate_total_constant_size_no_read' p sz u inv l

inline_for_extraction noextract
let validate_nlist_total_constant_size_mod_ok (n:U32.t) #wk (#k:parser_kind true wk) (#t: Type) (p:parser k t) inv l
  : Pure (validate_with_action_t (parse_nlist n p) inv l true)
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal /\
    k.parser_kind_low < 4294967296 /\
    U32.v n % k.LP.parser_kind_low == 0
  ))
  (ensures (fun _ -> True))
= [@inline_let]
  let _ =
    parse_nlist_total_fixed_size_kind_correct n p
  in
  validate_total_constant_size_no_read' (LP.strengthen (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n p)) n () inv l

inline_for_extraction noextract
let validate_nlist_constant_size_mod_ko (n:U32.t) (#wk: _) (#k:parser_kind true wk) #t (p:parser k t) inv l
  : Pure (validate_with_action_t (parse_nlist n p) inv l true)
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    U32.v n % k.LP.parser_kind_low <> 0
  ))
  (ensures (fun _ -> True))
= 
  (fun input ->
     let h = FStar.HyperStack.ST.get () in
     [@inline_let]
     let f () : Lemma
       (requires (Some? (LP.parse (parse_nlist n p) (I.get_remaining input h))))
       (ensures False)
     = let sq = I.get_remaining input h in
       let sq' = Seq.slice sq 0 (U32.v n) in
       LowParse.Spec.List.list_length_constant_size_parser_correct p sq' ;
       let Some (l, _) = LP.parse (parse_nlist n p) sq in
       assert (U32.v n == FStar.List.Tot.length l `Prims.op_Multiply` k.LP.parser_kind_low) ;
       FStar.Math.Lemmas.cancel_mul_mod (FStar.List.Tot.length l) k.LP.parser_kind_low ;
       assert (U32.v n % k.LP.parser_kind_low == 0)
     in
     [@inline_let]
     let _ = Classical.move_requires f () in
     validator_error_list_size_not_multiple
  )

inline_for_extraction noextract
let validate_nlist_total_constant_size' (n:U32.t) #wk (#k:parser_kind true wk) #t (p:parser k t) inv l
  : Pure (validate_with_action_t (parse_nlist n p) inv l true)
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal /\
    k.parser_kind_low < 4294967296
  ))
  (ensures (fun _ -> True))
= fun input -> // n is not an integer constant, so we need to eta-expand and swap fun and if
  if n `U32.rem` U32.uint_to_t k.LP.parser_kind_low = 0ul
  then validate_nlist_total_constant_size_mod_ok n p inv l input
  else validate_nlist_constant_size_mod_ko n p inv l input

inline_for_extraction noextract
let validate_nlist_total_constant_size (n_is_const: bool) (n:U32.t) #wk (#k:parser_kind true wk) (#t: Type) (p:parser k t) inv l
: Pure (validate_with_action_t (parse_nlist n p) inv l true)
  (requires (
    let open LP in
    k.parser_kind_subkind = Some ParserStrong /\
    k.parser_kind_high = Some k.parser_kind_low /\
    k.parser_kind_metadata = Some ParserKindMetadataTotal /\
    k.parser_kind_low < 4294967296
  ))
  (ensures (fun _ -> True))
=
  if
    if k.LP.parser_kind_low = 1
    then true
    else if n_is_const
    then U32.v n % k.LP.parser_kind_low = 0
    else false
  then
    validate_nlist_total_constant_size_mod_ok n p inv l
  else if
    if n_is_const
    then U32.v n % k.LP.parser_kind_low <> 0
    else false
  then
    validate_nlist_constant_size_mod_ko n p inv l
  else
    validate_nlist_total_constant_size' n p inv l

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
    validate_drop (validate_nlist_total_constant_size n_is_const n p inv l)
  else
    validate_nlist n v

noextract inline_for_extraction
let validate_t_at_most (n:U32.t) #nz #wk (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
                       (#inv:_) (#l:_) (#ar:_) (v:validate_with_action_t p inv l ar)
  : Tot (validate_with_action_t (parse_t_at_most n p) inv l false)
  = fun input ->
    let h = HST.get () in
    let hasBytes = I.has input n in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h1;
    assert (h1 `extends` h);
    if not hasBytes
    then
      LPL.validator_error_not_enough_data
    else
      let truncatedInput = I.truncate input n in
      let h2 = HST.get () in
      let _ = modifies_address_liveness_insensitive_unused_in h h2 in
      let _ = assert (h2 `extends` h) in
      let _ = I.is_prefix_of_prop truncatedInput input h2 in
      let _ = assert (I.get_remaining truncatedInput h2 `Seq.equal` Seq.slice (I.get_remaining input h) 0 (U32.v n)) in
      [@inline_let] let _ = LPC.nondep_then_eq p parse_all_bytes (I.get_remaining truncatedInput h2) in
      let result = validate_drop v truncatedInput in
      let h3 = HST.get () in
      let _ = I.is_prefix_of_prop truncatedInput input h3 in
      if LPE.is_error result
      then result
      else begin
        I.empty truncatedInput;
        let h4 = HST.get () in
        modifies_address_liveness_insensitive_unused_in h h4;
        let _ = I.is_prefix_of_prop truncatedInput input h4 in
        assert (h4 `extends` h);
        result
      end

#push-options "--z3rlimit 32"
#restart-solver

noextract inline_for_extraction
let validate_t_exact (n:U32.t) #nz #wk (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
                       (#inv:_) (#l:_) (#ar:_) (v:validate_with_action_t p inv l ar)
  : Tot (validate_with_action_t (parse_t_exact n p) inv l false)
  = fun input ->
    let h = HST.get () in
    let hasBytes = I.has input n in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h h1;
    assert (h1 `extends` h);
    if not hasBytes
    then
      LPL.validator_error_not_enough_data
    else
      let truncatedInput = I.truncate input n in
      let h2 = HST.get () in
      let _ = modifies_address_liveness_insensitive_unused_in h h2 in
      let _ = assert (h2 `extends` h) in
      let _ = I.is_prefix_of_prop truncatedInput input h2 in
      let _ = assert (I.get_remaining truncatedInput h2 `Seq.equal` Seq.slice (I.get_remaining input h) 0 (U32.v n)) in
      [@inline_let] let _ = LPC.nondep_then_eq p parse_all_bytes (I.get_remaining truncatedInput h2) in
      let result = validate_drop v truncatedInput in
      let h3 = HST.get () in
      let _ = I.is_prefix_of_prop truncatedInput input h3 in
      if LPE.is_error result
      then result
      else begin
        let stillHasBytes = I.has truncatedInput 1ul in
        let h4 = HST.get () in
        modifies_address_liveness_insensitive_unused_in h h4;
        assert (h4 `extends` h);
        I.is_prefix_of_prop truncatedInput input h4;
        if stillHasBytes
        then ResultOps.validator_error_unexpected_padding
        else result
      end

#pop-options

inline_for_extraction noextract
let validate_with_comment (c:string)
                          #nz #wk (#k:parser_kind nz wk) #t (#p:parser k t)
                          #inv #l #ar (v:validate_with_action_t p inv l ar)
  : validate_with_action_t p inv l ar
  = fun input ->
    LowParse.Low.Base.comment c;
    v input

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
    = fun input ->
        let h = HST.get () in
        assert (parse_filter p f == LPC.parse_filter #k #t p f);
        assert_norm (Prelude.refine t f == LPC.parse_filter_refine f);
        LPC.parse_filter_eq p f (I.get_remaining input h);
        p32 input

inline_for_extraction noextract
let validate____UINT8
  : validator parse____UINT8
  = validate_with_comment
      "Checking that we have enough space for a UINT8, i.e., 1 byte"
      (validate_total_constant_size_no_read parse____UINT8 1ul () _ _)

(* FIXME: Reading currently performs two copies, one from `read`, another from kremlib's implementations of load16_be, etc. *)

inline_for_extraction noextract
let lift_reader
  (#nz: _)
  (#k: parser_kind nz WeakKindStrongPrefix)
  (#t: _)
  (p: parser k t)
  (r: LPL.leaf_reader p)
  (sz: U32.t)
: Pure (leaf_reader p)
  (requires (
    k.LP.parser_kind_subkind == Some LP.ParserStrong /\
    k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
    k.LP.parser_kind_low = U32.v sz /\
    U32.v sz > 0
  ))
  (ensures (fun _ -> True))
= fun input ->
  LP.parser_kind_prop_equiv k p;
  let h0 = HST.get () in
  HST.push_frame ();
  let temp = B.alloca 0uy sz in
  let h1 = HST.get () in
  I.live_not_unused_in input h0;
  I.read input sz temp;
  let h2 = HST.get () in
  LP.parse_strong_prefix p (I.get_remaining input h0) (B.as_seq h2 temp);
  LPL.valid_facts p h2 (LPL.make_slice temp sz) 0ul;
  let res = r (LPL.make_slice temp sz) 0ul in
  HST.pop_frame ();
  res

inline_for_extraction noextract
let read____UINT8
  : leaf_reader parse____UINT8
= lift_reader _ LowParse.Low.Int.read_u8 1ul

inline_for_extraction noextract
let validate____UINT16BE
  : validator parse____UINT16BE
  = validate_with_comment
      "Checking that we have enough space for a UINT16BE, i.e., 2 bytes"
      (validate_total_constant_size_no_read parse____UINT16BE 2ul () _ _)

inline_for_extraction noextract
let read____UINT16BE
  : leaf_reader parse____UINT16BE
= lift_reader _ LowParse.Low.Int.read_u16 2ul

inline_for_extraction noextract
let validate____UINT32BE
  : validator parse____UINT32BE
  = validate_with_comment
      "Checking that we have enough space for a UINT32BE, i.e., 4 bytes"
      (validate_total_constant_size_no_read parse____UINT32BE 4ul () _ _)

inline_for_extraction noextract
let read____UINT32BE
  : leaf_reader parse____UINT32BE
= lift_reader _ LowParse.Low.Int.read_u32 4ul

inline_for_extraction noextract
let validate____UINT64BE
  : validator parse____UINT64BE
  = validate_with_comment
      "Checking that we have enough space for a UINT64BE, i.e., 8 bytes"
      (validate_total_constant_size_no_read parse____UINT64BE 8ul () _ _)

inline_for_extraction noextract
let read____UINT64BE
  : leaf_reader parse____UINT64BE
= lift_reader _ LowParse.Low.Int.read_u64 8ul

inline_for_extraction noextract
let validate____UINT16
  : validator parse____UINT16
  = validate_with_comment
      "Checking that we have enough space for a UINT16, i.e., 2 bytes"
      (validate_total_constant_size_no_read parse____UINT16 2ul () _ _)

inline_for_extraction noextract
let read____UINT16
  : leaf_reader parse____UINT16
= lift_reader _ LowParse.Low.BoundedInt.read_u16_le 2ul

inline_for_extraction noextract
let validate____UINT32
  : validator parse____UINT32
  = validate_with_comment
      "Checking that we have enough space for a UINT32, i.e., 4 bytes"
      (validate_total_constant_size_no_read parse____UINT32 4ul () _ _)

inline_for_extraction noextract
let read____UINT32
  : leaf_reader parse____UINT32
= lift_reader _ LowParse.Low.BoundedInt.read_u32_le 4ul

inline_for_extraction noextract
let validate____UINT64
  : validator parse____UINT64
  = validate_with_comment
      "Checking that we have enough space for a UINT64, i.e., 8 bytes"
      (validate_total_constant_size_no_read parse____UINT64 8ul () _ _)

inline_for_extraction noextract
let read____UINT64
  : leaf_reader parse____UINT64
= lift_reader _ LowParse.Low.Int.read_u64_le 8ul

inline_for_extraction noextract
let validate_unit
= fun input -> 0uL

inline_for_extraction noextract
let read_unit
= fun input -> ()

inline_for_extraction noextract
let validate_unit_refinement (f:unit -> bool) (cf:string)
  : validator (parse_unit `parse_filter` f)
= fun input ->
    let h = HST.get () in
    LPC.parse_filter_eq parse_unit f (I.get_remaining input h);
    LowStar.Comment.comment cf;
    if f ()
    then 0uL
    else ResultOps.validator_error_constraint_failed


(* Reimplement validate_list_up_to with readability (but no actions) *)

module LUT = LowParse.Low.ListUpTo

unfold
let validate_list_up_to_inv
  (#k: parser_kind true WeakKindStrongPrefix)
  (#t: eqtype)
  (p: parser k t)
  (terminator: t)
  (prf: LUT.consumes_if_not_cond (cond_string_up_to terminator) p)
  (sl: input_buffer_t)
  (h0: HS.mem)
  (bres: B.pointer U64.t)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
=
  let res = B.deref h bres in
  let q = LUT.parse_list_up_to (cond_string_up_to terminator) p prf in
  B.live h0 bres /\
  I.live sl h0 /\
  I.live sl h /\
  B.loc_disjoint (I.footprint sl) (B.loc_buffer bres) /\
  B.modifies (B.loc_buffer bres `B.loc_union` I.footprint sl) h0 h /\
  begin
    let s = I.get_remaining sl h0 in
    let s' = I.get_remaining sl h in
    Seq.length s' <= Seq.length s /\
    s' `Seq.equal` Seq.slice s (Seq.length s - Seq.length s') (Seq.length s) /\
    begin if LPL.is_error res
    then
      // validation *or action* failed
      stop == true
    else if stop
    then valid_consumed q h0 h sl
    else match LP.parse q s, LP.parse q s' with
    | None, None -> True
    | Some (_, consumed), Some (_, consumed') -> consumed' + Seq.length s - Seq.length s' == consumed
    | _ -> False
    end
  end

inline_for_extraction
let validate_list_up_to_body
  (#k: parser_kind true WeakKindStrongPrefix)
  (#t: eqtype)
  (#p: parser k t)
  (terminator: t)
  (prf: LUT.consumes_if_not_cond (cond_string_up_to terminator) p)
  (v: validator p)
  (r: leaf_reader p)
  (sl: input_buffer_t)
  (h0: HS.mem)
  (bres: B.pointer U64.t)
: HST.Stack bool
  (requires (fun h ->
    validate_list_up_to_inv p terminator prf sl h0 bres h false
  ))
  (ensures (fun h stop h' ->
    validate_list_up_to_inv p terminator prf sl h0 bres h false /\
    validate_list_up_to_inv p terminator prf sl h0 bres h' stop
  ))
=
  let h = HST.get () in
  LUT.parse_list_up_to_eq (cond_string_up_to terminator) p prf (I.get_remaining sl h);
  let result = v sl in
  B.upd bres 0ul result;
  if LPE.is_error result
  then begin
    true
  end else begin
    let value = r sl in
    cond_string_up_to terminator value
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
  fun sl ->
  let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  fresh_frame_modifies h0 h1;
  let bres = B.alloca 0uL 1ul in
  let h2 = HST.get () in
  I.live_not_unused_in sl h0;
  C.Loops.do_while
    (validate_list_up_to_inv p terminator prf sl h2 bres)
    (fun _ -> validate_list_up_to_body terminator prf v r sl h2 bres)
    ;
  let result = B.index bres 0ul in
  HST.pop_frame ();
  result

let validate_string
  #k #t #p v r terminator
=
  LP.parser_kind_prop_equiv k p;
  validate_weaken (validate_list_up_to v r terminator (fun _ _ _ -> ())) _

let validate_all_bytes = fun input -> I.empty input; 0uL

let validate_all_zeros =
  validate_list (validate_filter "parse_zeros" validate____UINT8 read____UINT8 is_zero "check if zero" "")


////////////////////////////////////////////////////////////////////////////////

noextract
inline_for_extraction
let action_return
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#a:Type) (x:a)
  : action p true_inv eloc_none false a
  = fun _ _ -> x

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
  = fun input pos ->
    let h0 = HST.get () in
    [@(rename_let ("" ^ name))]
    let x = f input pos in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    g x input pos

noextract
inline_for_extraction
let action_seq
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#invf:slice_inv) (#lf:eloc)
      #bf (#a:Type) (f: action p invf lf bf a)
      (#invg:slice_inv) (#lg:eloc) #bg
      (#b:Type) (g: action p invg lg bg b)
  : Tot (action p (conj_inv invf invg) (eloc_union lf lg) (bf || bg) b)
  = fun input pos ->
    let h0 = HST.get () in
    let _ = f input pos in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    g input pos

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
  = fun input pos ->
      if guard 
      then then_ () input pos
      else else_ () input pos

noextract
inline_for_extraction
let action_abort
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
  : action p true_inv eloc_none false bool
  = fun _ _ -> false

noextract
inline_for_extraction
let action_field_pos
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t) (u:unit)
   : action p true_inv eloc_none false U32.t
   = fun _ pos -> pos

(* FIXME: this is now unsound in general (only valid for flat buffer)
noextract
inline_for_extraction
let action_field_ptr
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t) (u:unit)
   : action p true_inv eloc_none true LPL.puint8
   = fun input startPosition _ ->
       let open LowParse.Slice in
       LPL.offset input (LPL.uint64_to_uint32 startPosition)
*)

noextract
inline_for_extraction
let action_deref
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#a:_) (x:B.pointer a)
   : action p (ptr_inv x) loc_none false a
   = fun _ _ -> !*x

noextract
inline_for_extraction
let action_assignment
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#a:_) (x:B.pointer a) (v:a)
   : action p (ptr_inv x) (ptr_loc x) false unit
   = fun _ _ -> x *= v

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


#pop-options
