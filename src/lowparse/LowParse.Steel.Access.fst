module LowParse.Steel.Access
include LowParse.Steel.VParse

module S = Steel.Memory
module SP = Steel.FractionalPermission
module SE = Steel.Effect
module SEA = Steel.Effect.Atomic
module A = Steel.Array
module AP = LowParse.Steel.ArrayPtr

module U32 = FStar.UInt32

let parsed_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type0
= (a: byte_array) ->
  SE.Steel U32.t
    (AP.varrayptr a)
    (fun _ -> AP.varrayptr a)
    (fun h -> Some? (parse p (h (AP.varrayptr a)).AP.contents))
    (fun h res h' ->
      let s = h (AP.varrayptr a) in
      h' (AP.varrayptr a) == s /\
      begin match parse p s.AP.contents with
      | None -> False
      | Some (_, consumed) -> U32.v res == consumed
      end
    )

let parsed_size_constant_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: U32.t)
: Pure (parsed_size p)
    (requires (
      k.parser_kind_high == Some k.parser_kind_low /\
      U32.v sz == k.parser_kind_low
    ))
    (ensures (fun _ -> True))
=
  fun a ->
  parser_kind_prop_equiv k p;
  let g = SEA.gget (AP.varrayptr a) in
  assert (Some? (parse p g.AP.contents));
  SEA.return sz

let get_parsed_size
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: parsed_size p)
  (a: byte_array)
: SE.Steel U32.t
    (vparse p a)
    (fun _ -> vparse p a)
    (fun _ -> True)
    (fun h res h' ->
      h' (vparse p a) == h (vparse p a) /\
      U32.v res == A.length (array_of (h (vparse p a)))
    )
=
  elim_vparse p a;
  let _ = SEA.gget (AP.varrayptr a) in // FIXME: WHY WHY WHY is this needed?
  let res = j a in
  intro_vparse p a;
  SEA.return res

let peek_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: parsed_size p)
  (a: byte_array)
: SE.Steel byte_array
    (AP.varrayptr a)
    (fun res -> vparse p a `SE.star` AP.varrayptr res)
    (fun h ->
      k.parser_kind_subkind == Some ParserStrong /\
      Some? (parse p (h (AP.varrayptr a)).AP.contents)
    )
    (fun h res h' ->
      let c_a = h (AP.varrayptr a) in
      let c_a' = h' (vparse p a) in
      let c_res = h' (AP.varrayptr res) in
      let consumed = A.length (array_of c_a') in
      A.merge_into (array_of c_a') c_res.AP.array c_a.AP.array /\
      perm_of c_a' == c_a.AP.perm /\
      c_res.AP.perm == c_a.AP.perm /\
      is_byte_repr p c_a'.contents (Seq.slice c_a.AP.contents 0 consumed) /\
      consumed <= A.length c_a.AP.array /\
      c_res.AP.contents == Seq.slice c_a.AP.contents consumed (A.length c_a.AP.array)
    )
=
  let c_a = SEA.gget (AP.varrayptr a) in
  let n = j a in
  parse_strong_prefix p c_a.AP.contents (Seq.slice c_a.AP.contents 0 (U32.v n)); 
  let res = AP.split a n in
  intro_vparse p a;
  SEA.return res

val memcpy
  (dst: byte_array)
  (src: byte_array)
  (n: U32.t)
: SE.Steel byte_array
    (AP.varrayptr dst `SE.star` AP.varrayptr src)
    (fun _ -> AP.varrayptr dst `SE.star` AP.varrayptr src)
    (fun h ->
      (h (AP.varrayptr dst)).AP.perm == SP.full_perm /\
      U32.v n <= A.length (h (AP.varrayptr src)).AP.array /\
      U32.v n <= A.length (h (AP.varrayptr dst)).AP.array
    )
    (fun h res h' ->
      let s = h (AP.varrayptr src) in
      let d = h (AP.varrayptr dst) in
      let d' = h' (AP.varrayptr dst) in
      res == dst /\
      h' (AP.varrayptr src) == s /\
      d'.AP.perm == SP.full_perm /\
      d'.AP.array == d.AP.array /\
      U32.v n <= A.length d.AP.array /\
      U32.v n <= A.length s.AP.array /\
      d'.AP.contents `Seq.equal` (Seq.slice s.AP.contents 0 (U32.v n) `Seq.append` Seq.slice d.AP.contents (U32.v n) (A.length d.AP.array))
    )
    (decreases (U32.v n))

let rec memcpy dst src n =
  let g : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr dst) in
  assert (g.AP.perm == SP.full_perm);
  if n = 0ul
  then SEA.return dst
  else begin
    let j = n `U32.sub` 1ul in
    let c = AP.index src j in
    AP.upd dst j c;
    memcpy dst src j
  end

val copy_exact
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: byte_array)
  (dst: byte_array)
  (n: U32.t)
: SE.Steel unit
    (vparse p src `SE.star` AP.varrayptr dst)
    (fun _ -> vparse p src `SE.star` vparse p dst)
    (fun h ->
      (h (AP.varrayptr dst)).AP.perm == SP.full_perm /\
      U32.v n == A.length (array_of (h (vparse p src))) /\
      U32.v n == A.length (h (AP.varrayptr dst)).AP.array
    )
    (fun h _ h' ->
      let s = h (vparse p src) in
      let d = h (AP.varrayptr dst) in
      let d' = h' (vparse p dst) in
      U32.v n == A.length (array_of s) /\
      U32.v n == A.length d.AP.array /\
      h' (vparse p src) == s /\
      array_of d' == d.AP.array /\
      perm_of d' == SP.full_perm /\
      d'.contents == s.contents
    )

let copy_exact p src dst n =
  elim_vparse p src;
  let _ = memcpy dst src n in
  let gs : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr src) in
  assert (U32.v n == A.length gs.AP.array); // FIXME: WHY WHY WHY is this needed for the equality on n in the postcond
  let gd : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr dst) in
  assert (U32.v n == A.length gd.AP.array); // same here
  assert (gd.AP.contents `Seq.equal` gs.AP.contents); // ok, this is expected because of `equal`
  intro_vparse p src;
  intro_vparse p dst

val copy_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: parsed_size p)
  (src: byte_array)
  (dst: byte_array)
: SE.Steel byte_array
    (vparse p src `SE.star` AP.varrayptr dst)
    (fun res -> vparse p src `SE.star` vparse p dst `SE.star` AP.varrayptr res)
    (fun h ->
      (h (AP.varrayptr dst)).AP.perm == SP.full_perm /\
      A.length (array_of (h (vparse p src))) <= A.length (h (AP.varrayptr dst)).AP.array
    )
    (fun h res h' ->
      SE.can_be_split (vparse p src `SE.star` vparse p dst `SE.star` AP.varrayptr res) (vparse p src) /\ // FIXME: WHY WHY WHY?
      SE.can_be_split (vparse p src `SE.star` vparse p dst `SE.star` AP.varrayptr res) (vparse p dst) /\ // same here
      begin
        let s = h (vparse p src) in
        let d = h (AP.varrayptr dst) in
        let d' = h' (vparse p dst) in
        let r = h' (AP.varrayptr res) in
        h' (vparse p src) == s /\
        A.merge_into (array_of d') r.AP.array d.AP.array /\
        d'.contents == s.contents /\
        perm_of d' == SP.full_perm /\
        A.length (array_of s) == A.length (array_of d') /\ // TODO: this should be a consequence of the equality of the contents, via parser injectivity
        r.AP.perm == SP.full_perm /\
        r.AP.contents == Seq.slice d.AP.contents (A.length (array_of s)) (A.length d.AP.array)
      end
    )

let copy_strong #_ #_ #p j src dst =
  let n = get_parsed_size j src in
  let res = AP.split dst n in
  copy_exact p src dst n;
  SEA.reveal_star_3 (vparse p src) (vparse p dst) (AP.varrayptr res); // for can_be_split
  SEA.return res

let copy_weak_vprop
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: byte_array)
  (dst: byte_array)
  (res: option byte_array)
: Tot SE.vprop
= vparse p src `SE.star`
  begin if None? res
  then AP.varrayptr dst
  else vparse p dst `SE.star` AP.varrayptr (Some?.v res)
  end

unfold
let copy_weak_vprop_src
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: byte_array)
  (dst: byte_array)
  (res: option byte_array)
  (x: SE.t_of (copy_weak_vprop p src dst res))
: Tot (v k t)
= fst x

unfold
let copy_weak_vprop_dst_some
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: byte_array)
  (dst: byte_array)
  (res: option byte_array)
  (x: SE.t_of (copy_weak_vprop p src dst res))
: Pure (v k t)
  (requires (None? res == false))
  (ensures (fun _ -> True))
= fst #(SE.t_of (vparse p dst)) #(SE.t_of (AP.varrayptr (Some?.v res))) (snd x)

unfold
let copy_weak_vprop_dst_none
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: byte_array)
  (dst: byte_array)
  (res: option byte_array)
  (x: SE.t_of (copy_weak_vprop p src dst res))
: Pure (AP.v byte)
  (requires (None? res))
  (ensures (fun _ -> True))
= snd x

unfold
let copy_weak_vprop_res
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: byte_array)
  (dst: byte_array)
  (res: option byte_array)
  (x: SE.t_of (copy_weak_vprop p src dst res))
: Pure (AP.v byte)
  (requires (Some? res))
  (ensures (fun _ -> True))
= snd #(SE.t_of (vparse p dst)) #(SE.t_of (AP.varrayptr (Some?.v res))) (snd x)

let copy_weak_post
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: byte_array)
  (dst: byte_array)
  (h: SE.rmem (vparse p src `SE.star` AP.varrayptr dst))
  (res0: option byte_array)
  (h': SE.rmem (copy_weak_vprop p src dst res0))
: Tot prop
=
      let x = h' (copy_weak_vprop p src dst res0) in
      h (vparse p src) == copy_weak_vprop_src p src dst res0 x /\
      begin
        if None? res0
        then
          copy_weak_vprop_dst_none p src dst res0 x == h (AP.varrayptr dst)
        else
          let res = Some?.v res0 in
          let s = h (vparse p src) in
          let d' = copy_weak_vprop_dst_some p src dst res0 x in
          let d = h (AP.varrayptr dst) in
          let r = copy_weak_vprop_res p src dst res0 x in
          A.merge_into (array_of d') r.AP.array d.AP.array /\
          perm_of d' == SP.full_perm /\
          d'.contents == s.contents /\
          A.length (array_of s) == A.length (array_of d') /\ // TODO: this should be a consequence of the equality of the contents, via parser injectivity
          r.AP.perm == SP.full_perm /\
          r.AP.contents == Seq.slice d.AP.contents (A.length (array_of s)) (A.length d.AP.array)
      end

val copy_weak
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: parsed_size p)
  (src: byte_array)
  (dst: byte_array)
  (n: U32.t)
: SE.Steel (option byte_array)
    (vparse p src `SE.star` AP.varrayptr dst)
    (fun res -> copy_weak_vprop p src dst res)
    (fun h ->
      (h (AP.varrayptr dst)).AP.perm == SP.full_perm /\
      A.length (h (AP.varrayptr dst)).AP.array == U32.v n
    )
    (fun h res0 h' ->
      copy_weak_post p src dst h res0 h'
    )

let copy_weak #_ #_ #p j src dst n_dst =
  let n_src = get_parsed_size j src in
  if n_dst `U32.lt` n_src
  then begin
    SEA.reveal_star (vparse p src) (AP.varrayptr dst);
    let res0 : option byte_array = None in
    SEA.change_equal_slprop
      (vparse p src `SE.star` AP.varrayptr dst)
      (copy_weak_vprop p src dst res0);
    SEA.return res0
  end else begin
    let res = AP.split dst n_src in
    let _ = SEA.gget (AP.varrayptr dst) in // FIXME: WHY WHY WHY?
    copy_exact p src dst n_src;
    SEA.reveal_star (vparse p dst) (AP.varrayptr res);
    SEA.reveal_star (vparse p src) (vparse p dst `SE.star` AP.varrayptr res);
    let res0 = Some res in
    SEA.change_equal_slprop
      (vparse p src `SE.star` (vparse p dst `SE.star` AP.varrayptr res))
      (copy_weak_vprop p src dst res0);
    SEA.return res0
  end

module R2L = LowParse.Steel.R2LOutput

val copy_strong_r2l
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: parsed_size p)
  (src: byte_array)
  (dst: R2L.t)
: SE.Steel byte_array
    (vparse p src `SE.star` R2L.vp dst)
    (fun res -> vparse p src `SE.star` R2L.vp dst `SE.star` vparse p res)
    (fun h ->
      A.length (array_of (h (vparse p src))) <= A.length (h (R2L.vp dst))
    )
    (fun h res h' ->
      SE.can_be_split (vparse p src `SE.star` R2L.vp dst `SE.star` vparse p res) (vparse p src) /\ // FIXME: WHY WHY WHY?
      SE.can_be_split (vparse p src `SE.star` R2L.vp dst `SE.star` vparse p res) (R2L.vp dst) /\ // same here
      begin
        let s = h (vparse p src) in
        let d = h (R2L.vp dst) in
        let d' = h' (R2L.vp dst) in
        let r = h' (vparse p res) in
        h' (vparse p src) == s /\
        A.merge_into d' (array_of r) d /\
        (perm_of r) == SP.full_perm /\
        r.contents == s.contents /\
        A.length (array_of s) == A.length (array_of r) // TODO: this should be a consequence of the equality of the contents, via parser injectivity
      end
    )

let copy_strong_r2l #_ #_ #p j src dst =
  let n = get_parsed_size j src in
  let res = R2L.split dst n in
  copy_exact p src res n;
  SEA.reveal_star_3 (vparse p src) (R2L.vp dst) (vparse p res); // for can_be_split
  SEA.return res

(* TODO: generalize somehow to any vprop on option. *)

let copy_weak_r2l_vprop
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (res: option byte_array)
: Tot SE.vprop
= if None? res
  then SE.emp
  else vparse p (Some?.v res)

unfold
let copy_weak_r2l_vprop_res
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (res: option byte_array)
  (x: SE.t_of (copy_weak_r2l_vprop p res))
: Pure (v k t)
  (requires (Some? res))
  (ensures (fun _ -> True))
= x

let copy_weak_r2l_post
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: byte_array)
  (dst: R2L.t)
  (h: SE.rmem (vparse p src `SE.star` R2L.vp dst))
  (res0: option byte_array)
  (h': SE.rmem (vparse p src `SE.star` R2L.vp dst `SE.star` copy_weak_r2l_vprop p res0))
: Tot prop
=
  SE.can_be_split (vparse p src `SE.star` R2L.vp dst `SE.star` copy_weak_r2l_vprop p res0) (vparse p src) /\
  SE.can_be_split (vparse p src `SE.star` R2L.vp dst `SE.star` copy_weak_r2l_vprop p res0) (R2L.vp dst) /\
  begin
      let s = h (vparse p src) in
      let d = h (R2L.vp dst) in
      let d' = h' (R2L.vp dst) in
      h' (vparse p src) == s /\
      begin
        if None? res0
        then
           d' == d
        else
          let res = Some?.v res0 in
          let r = copy_weak_r2l_vprop_res p res0 (h' (copy_weak_r2l_vprop p res0)) in
          A.merge_into d' (array_of r) d /\
          perm_of r == SP.full_perm /\
          r.contents == s.contents /\
          A.length (array_of s) == A.length (array_of r) // TODO: this should be a consequence of the equality of the contents, via parser injectivity
      end
  end

val copy_weak_r2l
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: parsed_size p)
  (src: byte_array)
  (dst: R2L.t)
: SE.Steel (option byte_array)
    (vparse p src `SE.star` R2L.vp dst)
    (fun res -> vparse p src `SE.star` R2L.vp dst `SE.star` copy_weak_r2l_vprop p res)
    (fun _ -> True)
    (fun h res0 h' ->
      copy_weak_r2l_post p src dst h res0 h'
    )

let copy_weak_r2l #_ #_ #p j src dst =
  let n_dst = R2L.len dst in
  let n_src = get_parsed_size j src in
  if n_dst `U32.lt` n_src
  then begin
    let res0 : option byte_array = None in
    SEA.change_equal_slprop
      SE.emp
      (copy_weak_r2l_vprop p res0);
    SEA.reveal_star_3 (vparse p src) (R2L.vp dst) (copy_weak_r2l_vprop p res0);
    SEA.return res0
  end else begin
    let res = R2L.split dst n_src in
    copy_exact p src res n_src;
    let res0 = Some res in
    SEA.change_equal_slprop
      (vparse p res)
      (copy_weak_r2l_vprop p res0);
    SEA.reveal_star_3 (vparse p src) (R2L.vp dst) (copy_weak_r2l_vprop p res0);
    SEA.return res0
  end
