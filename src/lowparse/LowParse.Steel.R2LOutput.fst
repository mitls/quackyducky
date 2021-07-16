module LowParse.Steel.R2LOutput

module P = Steel.Pointer

noeq
type t = {
  ptr: AP.t byte;
  len: P.t U32.t;
  prf: squash (AP.g_is_null ptr == P.g_is_null len /\ (P.g_is_null len == false ==> (P.size_v (P.offset len) == 0 /\ P.size_v (P.base_array_len (P.base len)) == 1 /\ P.base_array_freeable (P.base len))));
}

let null = { ptr = AP.null _; len = P.null _; prf = (); }

let g_is_null x = AP.g_is_null x.ptr

let vp0_refine
  (x: t)
  (y: SE.normal (SE.t_of (AP.varrayptr x.ptr `SE.star`  P.vptr_range x.len P.malloc_range)))
: Tot prop
=
  (fst y).AP.perm == SP.full_perm /\
  A.length (fst y).AP.array == U32.v (Seq.index (snd y) 0)

let vp0_rewrite
  (x: t)
  (y: SE.normal (SE.t_of ((AP.varrayptr x.ptr `SE.star` P.vptr_range x.len P.malloc_range) `SE.vrefine` vp0_refine x)))
: GTot (A.array byte)
= (fst y).AP.array

let vp0
  (x: t)
: Tot SE.vprop
= ((AP.varrayptr x.ptr `SE.star` P.vptr_range x.len P.malloc_range)
    `SE.vrefine` vp0_refine x)
      `SE.vrewrite` vp0_rewrite x

let vp_hp x = SE.hp_of (vp0 x)

let vp_sel x = fun h -> SE.sel_of (vp0 x) h

val intro_vp
  (#opened: _)
  (x: t)
: SEA.SteelGhost unit opened
    (AP.varrayptr x.ptr `SE.star` P.vptr_range x.len P.malloc_range)
    (fun _ -> vp x)
    (fun h ->
      (h (AP.varrayptr x.ptr)).AP.perm == SP.full_perm /\
      A.length (h (AP.varrayptr x.ptr)).AP.array == U32.v (P.ptr_sel0 P.malloc_range x.len h)
    )
    (fun h _ h'  ->
      h' (vp x) == (h (AP.varrayptr x.ptr)).AP.array
    )

let intro_vp x =
  SEA.reveal_star (AP.varrayptr x.ptr) (P.vptr_range x.len P.malloc_range);
  SEA.intro_vrefine (AP.varrayptr x.ptr `SE.star` P.vptr_range x.len P.malloc_range) (vp0_refine x);
  SEA.intro_vrewrite ((AP.varrayptr x.ptr `SE.star` P.vptr_range x.len P.malloc_range) `SE.vrefine` vp0_refine x) (vp0_rewrite x);
  assert_norm 
    (
      ((AP.varrayptr x.ptr `SE.star` P.vptr_range x.len P.malloc_range) `SE.vrefine` vp0_refine x) `SEA.vrewrite` vp0_rewrite x ==
      vp0 x
    );
  SEA.change_equal_slprop
    (((AP.varrayptr x.ptr `SE.star` P.vptr_range x.len P.malloc_range) `SE.vrefine` vp0_refine x) `SEA.vrewrite` vp0_rewrite x)
    (vp0 x);
  SEA.change_slprop_rel
    (vp0 x)
    (vp x)
    (fun x y -> x == y)
    (fun _ -> ())

val elim_vp
  (#opened: _)
  (x: t)
: SEA.SteelGhost unit opened
    (vp x)
    (fun _ -> AP.varrayptr x.ptr `SE.star` P.vptr_range x.len P.malloc_range)
    (fun _ -> True)
    (fun h _ h' ->
      let ar = (h' (AP.varrayptr x.ptr)).AP.array in
      (h' (AP.varrayptr x.ptr)).AP.perm == SP.full_perm /\
      h (vp x) == ar /\
      A.length (h (vp x)) == U32.v (P.ptr_sel0 P.malloc_range x.len h')
    )

let elim_vp x =
  SEA.change_slprop_rel
    (vp x)
    (vp0 x)
    (fun x y -> x == y)
    (fun _ -> ());
  assert_norm 
    (
      vp0 x ==
      ((AP.varrayptr x.ptr `SE.star` P.vptr_range x.len P.malloc_range) `SE.vrefine` vp0_refine x) `SEA.vrewrite` vp0_rewrite x
    );
  SEA.change_equal_slprop
    (vp0 x)
    (((AP.varrayptr x.ptr `SE.star` P.vptr_range x.len P.malloc_range) `SE.vrefine` vp0_refine x) `SEA.vrewrite` vp0_rewrite x);
  SEA.elim_vrewrite ((AP.varrayptr x.ptr `SE.star` P.vptr_range x.len P.malloc_range) `SE.vrefine` vp0_refine x) (vp0_rewrite x);
  let g2 = SEA.gget ((AP.varrayptr x.ptr `SE.star` P.vptr_range x.len P.malloc_range) `SE.vrefine` vp0_refine x) in // FIXME: WHY WHY WHY?
  SEA.elim_vrefine (AP.varrayptr x.ptr `SE.star` P.vptr_range x.len P.malloc_range) (vp0_refine x);
  SEA.reveal_star (AP.varrayptr x.ptr) (P.vptr_range x.len P.malloc_range)

let vp_not_null x =
  elim_vp x;
  AP.varrayptr_not_null x.ptr;
  intro_vp x

[@@SE.__steel_reduce__]
let vp_or_null1
  (x: t)
: Tot SE.vprop
= if g_is_null x
  then SE.emp
  else vp x

let vp_or_null_rewrite
  (x: t)
  (r: SE.t_of (vp_or_null1 x))
: GTot (option (A.array byte))
= if g_is_null x
  then None
  else Some r

[@@SE.__steel_reduce__]
let vp_or_null0
  (x: t)
: Tot SE.vprop
= vp_or_null1 x `SE.vrewrite` vp_or_null_rewrite x

let vp_or_null_hp x = SE.hp_of (vp_or_null0 x)

let vp_or_null_sel x = fun h -> SE.sel_of (vp_or_null0 x) h

let intro_vp_or_null_none x =
  assert (g_is_null x == true);
  SEA.change_equal_slprop
    SE.emp
    (vp_or_null1 x);
  SEA.intro_vrewrite (vp_or_null1 x) (vp_or_null_rewrite x);
  SEA.change_slprop_rel
    (vp_or_null0 x)
    (vp_or_null x)
    (fun u v -> u == v)
    (fun _ -> ())

let intro_vp_or_null_some x =
  vp_not_null x;
  SEA.change_equal_slprop
    (vp x)
    (vp_or_null1 x);
  SEA.intro_vrewrite (vp_or_null1 x) (vp_or_null_rewrite x);
  SEA.change_slprop_rel
    (vp_or_null0 x)
    (vp_or_null x)
    (fun u v -> u == v)
    (fun _ -> ())

let elim_vp_or_null_some x =
  SEA.change_slprop_rel
    (vp_or_null x)
    (vp_or_null0 x)
    (fun u v -> u == v)
    (fun _ -> ());
  SEA.elim_vrewrite (vp_or_null1 x) (vp_or_null_rewrite x);
  assert (g_is_null x == false);
  SEA.change_equal_slprop
    (vp_or_null1 x)
    (vp x)

let elim_vp_or_null_none x =
  SEA.change_slprop_rel
    (vp_or_null x)
    (vp_or_null0 x)
    (fun u v -> u == v)
    (fun _ -> ());
  SEA.elim_vrewrite (vp_or_null1 x) (vp_or_null_rewrite x);
  assert (g_is_null x == true);
  SEA.change_equal_slprop
    (vp_or_null1 x)
    SE.emp

val intro_vp_or_null
  (#opened: _)
  (x: t)
: SEA.SteelGhost unit opened
    (AP.varrayptr_or_null x.ptr `SE.star` P.vptr_range_or_null x.len P.malloc_range)
    (fun _ -> vp_or_null x)
    (fun h ->
      match g_is_null x, h (AP.varrayptr_or_null x.ptr), P.ptr_or_null_sel0 P.malloc_range x.len h with
      | true, None, None -> True
      | false, Some s, Some l ->
        s.AP.perm == SP.full_perm /\
        A.length s.AP.array == U32.v l
      | _ -> False
    )
    (fun h _ h'  ->
      match g_is_null x, h (AP.varrayptr_or_null x.ptr), h' (vp_or_null x) with
      | true, None, None -> True
      | false, Some s, Some c ->
        c == s.AP.array
      | _ -> False
    )

let intro_vp_or_null x =
  if g_is_null x
  then begin
    AP.elim_varrayptr_or_null_none x.ptr;
    P.assert_null x.len _;
    intro_vp_or_null_none x
  end else begin
    AP.elim_varrayptr_or_null_some x.ptr;
    P.assert_not_null x.len _;
    intro_vp x;
    intro_vp_or_null_some x 
  end

val elim_vp_or_null
  (#opened: _)
  (x: t)
: SEA.SteelGhost unit opened
    (vp_or_null x)
    (fun _ -> AP.varrayptr_or_null x.ptr `SE.star` P.vptr_range_or_null x.len P.malloc_range)
    (fun _ -> True)
    (fun h _ h' ->
      match g_is_null x, h (vp_or_null x), h' (AP.varrayptr_or_null x.ptr), P.ptr_or_null_sel0 P.malloc_range x.len h' with
      | true, None, None, None -> True
      | false, Some c, Some s, Some l ->
        s.AP.perm == SP.full_perm /\
        c == s.AP.array /\
        U32.v l == A.length s.AP.array
      | _ -> False
    )

let elim_vp_or_null x =
  if g_is_null x
  then begin
    elim_vp_or_null_none x;
    AP.intro_varrayptr_or_null_none x.ptr;
    P.intro_vptr_range_or_null_none x.len P.malloc_range
  end else begin
    elim_vp_or_null_some x;
    elim_vp x;
    AP.intro_varrayptr_or_null_some x.ptr;
    P.intro_vptr_range_or_null_some x.len P.malloc_range
  end

let is_null x =
  elim_vp_or_null x;
  let res = AP.is_null x.ptr in
  intro_vp_or_null x;
  SEA.return res

let change_slprop_emp
 (#opened:_) (q:SE.vprop)
  (l:(m:S.mem) -> Lemma
    (requires S.interp (SE.hp_of SE.emp) m)
    (ensures S.interp (SE.hp_of q) m)
  ) : SEA.SteelGhostT unit opened SE.emp (fun _ -> q)
= SEA.change_slprop_rel SE.emp q (fun _ _ -> True) (fun m -> l m)

let make
  x len
=
  let plen = P.malloc len in
  if P.is_null plen _
  then begin
    P.assert_null plen _;
    intro_vp_or_null_none null;
    SEA.change_equal_slprop
      (AP.varrayptr x)
      (make_vprop_post x null);
    SEA.return null
  end else begin
    P.assert_not_null plen _;
    AP.varrayptr_not_null x;
    let res = {
      ptr = x;
      len = plen;
      prf = ();
    }
    in
    SEA.change_equal_slprop
      (AP.varrayptr x)
      (AP.varrayptr res.ptr);
    SEA.change_equal_slprop
      (P.vptr_range plen P.malloc_range)
      (P.vptr_range res.len P.malloc_range);
    intro_vp res;
    intro_vp_or_null_some res;
    SEA.change_equal_slprop
      SE.emp
      (make_vprop_post x res);
    SEA.return res
  end

let len
  x
=
  elim_vp x;
  let l = P.deref x.len _ in
  intro_vp x;
  SEA.return l

let split
  x l
=
  let xlen = len x in
  elim_vp x;
  let xlen' = xlen `U32.sub` l in
  let g = SEA.gget (AP.varrayptr x.ptr) in
  let res = AP.split x.ptr xlen' in
  let g = SEA.gget (AP.varrayptr x.ptr) in
  P.upd x.len _ xlen' ;
  intro_vp x;
  SEA.return res

let merge
  x y l
=
  let xlen = len x in
  elim_vp x;
  AP.join x.ptr y;
  let xlen' = xlen `U32.add` l in
  P.upd x.len _ xlen' ;
  intro_vp x

let free
  x
=
  elim_vp x;
  AP.free x.ptr;
  P.free x.len _
