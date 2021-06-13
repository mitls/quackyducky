module LowParse.Steel.R2LOutput

module SR = Steel.Reference

noeq
type t = {
  ptr: AP.t byte;
  len: SR.ref U32.t;
}

let vp0_refine
  (x: t)
  (y: SE.normal (SE.t_of (AP.varrayptr x.ptr `SE.star`  SR.vptr x.len)))
: Tot prop
=
  (fst y).AP.perm == SP.full_perm /\
  A.length (fst y).AP.array == U32.v (snd y)

let vp0_rewrite
  (x: t)
  (y: SE.normal (SE.t_of ((AP.varrayptr x.ptr `SE.star`  SR.vptr x.len) `SE.vrefine` vp0_refine x)))
: GTot (A.array byte)
= (fst y).AP.array

let vp0
  (x: t)
: Tot SE.vprop
= ((AP.varrayptr x.ptr `SE.star` SR.vptr x.len)
    `SE.vrefine` vp0_refine x)
      `SE.vrewrite` vp0_rewrite x

let vp_hp x = SE.hp_of (vp0 x)

let vp_sel x = fun h -> SE.sel_of (vp0 x) h

val intro_vp
  (#opened: _)
  (x: t)
: SEA.SteelGhost unit opened
    (AP.varrayptr x.ptr `SE.star` SR.vptr x.len)
    (fun _ -> vp x)
    (fun h ->
      (h (AP.varrayptr x.ptr)).AP.perm == SP.full_perm /\
      A.length (h (AP.varrayptr x.ptr)).AP.array == U32.v (h (SR.vptr x.len))
    )
    (fun h _ h'  ->
      h' (vp x) == (h (AP.varrayptr x.ptr)).AP.array
    )

let intro_vp x =
  SEA.reveal_star (AP.varrayptr x.ptr) (SR.vptr x.len);
  SEA.intro_vrefine (AP.varrayptr x.ptr `SE.star` SR.vptr x.len) (vp0_refine x);
  SEA.intro_vrewrite ((AP.varrayptr x.ptr `SE.star` SR.vptr x.len) `SE.vrefine` vp0_refine x) (vp0_rewrite x);
  assert_norm 
    (
      ((AP.varrayptr x.ptr `SE.star` SR.vptr x.len) `SE.vrefine` vp0_refine x) `SEA.vrewrite` vp0_rewrite x ==
      vp0 x
    );
  SEA.change_equal_slprop
    (((AP.varrayptr x.ptr `SE.star` SR.vptr x.len) `SE.vrefine` vp0_refine x) `SEA.vrewrite` vp0_rewrite x)
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
    (fun _ -> AP.varrayptr x.ptr `SE.star` SR.vptr x.len)
    (fun _ -> True)
    (fun h _ h' ->
      let ar = (h' (AP.varrayptr x.ptr)).AP.array in
      (h' (AP.varrayptr x.ptr)).AP.perm == SP.full_perm /\
      h (vp x) == ar /\
      A.length (h (vp x)) == U32.v (h' (SR.vptr x.len))
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
      ((AP.varrayptr x.ptr `SE.star` SR.vptr x.len) `SE.vrefine` vp0_refine x) `SEA.vrewrite` vp0_rewrite x
    );
  SEA.change_equal_slprop
    (vp0 x)
    (((AP.varrayptr x.ptr `SE.star` SR.vptr x.len) `SE.vrefine` vp0_refine x) `SEA.vrewrite` vp0_rewrite x);
  SEA.elim_vrewrite ((AP.varrayptr x.ptr `SE.star` SR.vptr x.len) `SE.vrefine` vp0_refine x) (vp0_rewrite x);
  let g2 = SEA.gget ((AP.varrayptr x.ptr `SE.star` SR.vptr x.len) `SE.vrefine` vp0_refine x) in // FIXME: WHY WHY WHY?
  SEA.elim_vrefine (AP.varrayptr x.ptr `SE.star` SR.vptr x.len) (vp0_refine x);
  SEA.reveal_star (AP.varrayptr x.ptr) (SR.vptr x.len)

let sr_alloc (#a:Type0) (x:a) : SE.Steel (SR.ref a)
  SE.emp (fun r -> SR.vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> h1 (SR.vptr r) == x /\ not (SR.is_null r))
= SR.malloc x

let make
  x len
=
  let plen = sr_alloc len in
  let res = {
    ptr = x;
    len = plen;
  }
  in
  SEA.change_equal_slprop
    (AP.varrayptr x)
    (AP.varrayptr res.ptr);
  SEA.change_equal_slprop
    (SR.vptr plen)
    (SR.vptr res.len);
  intro_vp res;
  SEA.return res

let len
  x
=
  elim_vp x;
  let l = SR.read x.len in
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
  SR.write x.len xlen' ;
  intro_vp x;
  SEA.return res

unfold // FIXME: WHY WHY WHY, in the definition of merge below, do I need squash instead of Ghost requires
let a_merge
  (#t: Type)
  (r1 r2: A.array t)
  (sq: squash (A.adjacent r1 r2))
: GTot (A.array t)
= A.merge r1 r2

let merge
  x y l
=
  let xlen = len x in
  elim_vp x;
  let gl = SEA.gget (AP.varrayptr x.ptr) in
  let gr : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr y) in
  let sq : squash (A.adjacent (Ghost.reveal gl).AP.array (Ghost.reveal gr).AP.array) = () in
  let z = Ghost.hide (a_merge (Ghost.reveal gl).AP.array (Ghost.reveal gr).AP.array sq) in // this will bring into context the fact that the U32 sum shall not overflow
  let xlen' = xlen `U32.add` l in
  AP.join x.ptr y;
  SR.write x.len xlen' ;
  intro_vp x

let free
  x
=
  elim_vp x;
  AP.free x.ptr;
  SR.free x.len
