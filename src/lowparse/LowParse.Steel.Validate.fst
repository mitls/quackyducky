module LowParse.Steel.Validate
include LowParse.Steel.VParse
include LowParse.Low.ErrorCode

module S = Steel.Memory
module SE = Steel.Effect
module SEA = Steel.Effect.Atomic
module A = Steel.Array
module AP = LowParse.Steel.ArrayPtr

module U32 = FStar.UInt32
module U64 = FStar.UInt64

(* A validator consuming the whole input buffer. Useful for all
   parsers that do not have the strong prefix property, in particular
   those marked ConsumesAll. *)

let tvalid_res_vprop
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (a: byte_array)
  (res: bool)
: Tot SE.vprop
= if res
  then vparse p a
  else AP.varrayptr a

unfold
let tvalid_res_vprop_true
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (a: byte_array)
  (res: bool)
  (x: SE.t_of (tvalid_res_vprop p a res))
: Pure (v k t)
  (requires (res == true))
  (ensures (fun _ -> True))
= x

unfold
let tvalid_res_vprop_false
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (a: byte_array)
  (res: bool)
  (x: SE.t_of (tvalid_res_vprop p a res))
: Pure (AP.v byte)
  (requires (res == false))
  (ensures (fun _ -> True))
= x

let tvalidator
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
: Tot Type
=
  (a: byte_array) ->
  (len: U32.t) ->
  SE.Steel bool
    (AP.varrayptr a)
    (tvalid_res_vprop p a)
    (fun h -> U32.v len == A.length (h (AP.varrayptr a)).AP.array)
    (fun h res h' ->
      let s = h (AP.varrayptr a) in
      let s' = h' (tvalid_res_vprop p a res) in
      (res == true <==> valid p s.AP.contents) /\
      begin if res
      then
        let s' = tvalid_res_vprop_true p a res s' in
        array_of s' == s.AP.array /\
        perm_of s' == s.AP.perm /\
        is_byte_repr p s'.contents s.AP.contents
      else
        let s' = tvalid_res_vprop_false p a res s' in
        s' == s
      end
    )

(* A validator that returns the number of bytes consumed. Contrary to
   LowParse.Low validators, this validator can be used only if the
   parser has the "weak prefix property" (TODO): if a parser does not
   consume all bytes from some input buffer, then it does not depend on
   any bytes past what it consumed.
 *)

let wvalidator
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
: Tot Type
=
  (a: byte_array) ->
  (len: U32.t) ->
  SE.Steel U64.t
    (AP.varrayptr a)
    (fun _ -> AP.varrayptr a)
    (fun h -> U32.v len == A.length (h (AP.varrayptr a)).AP.array)
    (fun h res h' ->
      let s = h (AP.varrayptr a) in
      h' (AP.varrayptr a) == s /\
      begin if is_error res
      then
        None? (parse p s.AP.contents)
      else
        U64.v res <= Seq.length s.AP.contents /\
        valid p (Seq.slice s.AP.contents 0 (U64.v res))
      end
    )

let wvalidate_post // FIXME: WHY WHY WHY do I need to define this postcondition separately? (if not, then dummy fails to verify)
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (a: byte_array)
  (len: U32.t)
  (res: byte_array)
  (s: AP.v byte)
  (s': SE.t_of (if AP.g_is_null res then AP.varrayptr a else vparse p a))
  (vres: option (AP.v byte))
: Tot prop
=
  if AP.g_is_null res
  then
    parse p s.AP.contents == None /\
    vres == None /\
    s' == s
  else begin
    let s' : v k t = s' in
    let consumed = A.length (array_of s') in
    Some? vres /\
    U32.v len == A.length s.AP.array /\
    perm_of s' == s.AP.perm /\
    (Some?.v vres).AP.perm == s.AP.perm /\
    A.merge_into (array_of s') (Some?.v vres).AP.array s.AP.array /\
    consumed <= A.length s.AP.array /\
    is_byte_repr p s'.contents (Seq.slice s.AP.contents 0 consumed) /\
    (Some?.v vres).AP.contents == Seq.slice s.AP.contents consumed (U32.v len)
  end

val wvalidate
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (w: wvalidator p)
  (a: byte_array)
  (len: U32.t)
: SE.Steel (byte_array)
    (AP.varrayptr a)
    (fun res -> (if AP.g_is_null res then AP.varrayptr a else vparse p a) `SE.star` AP.varrayptr_or_null res)
    (fun h -> U32.v len == A.length (h (AP.varrayptr a)).AP.array)
    (fun h res h' ->
      let s = h (AP.varrayptr a) in
      let s'  = h' (if AP.g_is_null res then AP.varrayptr a else vparse p a) in
      let vres = h' (AP.varrayptr_or_null res) in
      wvalidate_post p a len res s s' vres
    )

let wvalidate
  #t #k #p w a len
=
  let consumed = w a len in
  if is_success consumed
  then begin
    let ar : byte_array = AP.split a (uint64_to_uint32 consumed) in
    intro_vparse p a;
    AP.intro_varrayptr_or_null_some ar;
    SEA.change_equal_slprop
      (vparse p a)
      (if AP.g_is_null ar then AP.varrayptr a else vparse p a);
    SEA.return ar
  end else begin
    let res : byte_array = AP.null _ in
    AP.intro_varrayptr_or_null_none res;
    SEA.change_equal_slprop
      (AP.varrayptr a)
      (if AP.g_is_null res then AP.varrayptr a else vparse p a);
    SEA.return res
  end

let dummy
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (w: wvalidator p)
  (a: byte_array)
  (len: U32.t)
: SE.Steel unit
    (AP.varrayptr a)
    (fun _ -> AP.varrayptr a)
    (fun h -> U32.v len == A.length (h (AP.varrayptr a)).AP.array)
    (fun h _ h' ->
      h' (AP.varrayptr a) == h (AP.varrayptr a)
    )
=
  let g0 : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr a) in
  let res = wvalidate w a len in
  if AP.is_null res
  then begin
    SEA.change_equal_slprop
      (if AP.g_is_null res then AP.varrayptr a else vparse p a)
      (AP.varrayptr a);
    AP.elim_varrayptr_or_null_none res;
    SEA.return ()
  end else begin
    SEA.change_equal_slprop
      (if AP.g_is_null res then AP.varrayptr a else vparse p a)
      (vparse p a);
    AP.elim_varrayptr_or_null_some res;
    let g1 : Ghost.erased (v k t) = SEA.gget (vparse p a) in // FIXME: WHY WHY WHY is this type annotation needed?
    elim_vparse p a;
    let g2 = SEA.gget (AP.varrayptr a) in
    let glen = Ghost.hide (A.length (array_of (Ghost.reveal g1))) in
    is_byte_repr_injective p (Ghost.reveal g1).contents (Seq.slice (Ghost.reveal g0).AP.contents 0 (Ghost.reveal glen)) (Ghost.reveal g2).AP.contents;
    Seq.lemma_split (Ghost.reveal g0).AP.contents (Ghost.reveal glen);
    AP.join a res
  end

#set-options "--ide_id_info_off"

unfold
let parse_strong_prefix_pre
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input1: bytes)
  (input2: bytes)
: Tot prop
=   k.parser_kind_subkind == Some ParserStrong /\ (
    match parse p input1 with
    | Some (x, consumed) ->
      consumed <= Seq.length input2 /\
      Seq.slice input1 0 consumed `Seq.equal` Seq.slice input2 0 consumed
    | _ -> False
  )

let parse_strong_prefix2
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input1: bytes)
  (input2: bytes)
  (sq: parse_strong_prefix_pre p input1 input2)
: Lemma
  (
    match parse p input1 with
    | Some (x, consumed) ->
      consumed <= Seq.length input2 /\
      parse p input2 == Some (x, consumed)
    | _ -> False
  )
= parse_strong_prefix p input1 input2

let validate_total_constant_size
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (sz: U32.t)
: Pure (wvalidator p)
    (requires (
        k.parser_kind_subkind == Some ParserStrong /\
        k.parser_kind_metadata == Some ParserKindMetadataTotal /\
        k.parser_kind_high == Some k.parser_kind_low /\
        k.parser_kind_low == U32.v sz
    ))
    (ensures (fun _ -> True))
= fun (a: byte_array) (len: U32.t) ->
  let ga = SEA.gget (AP.varrayptr a) in
  let g = Ghost.hide (Ghost.reveal ga).AP.contents in
  parser_kind_prop_equiv k p;
  if len `U32.lt` sz
  then begin
    assert (None? (parse p g));
    SEA.return validator_error_not_enough_data
  end else begin
    parse_strong_prefix p g (Seq.slice g 0 (U32.v sz));
    SEA.return (FStar.Int.Cast.uint32_to_uint64 sz)
  end
