module LowParse.Steel.ArrayPtr

module P = Steel.Pointer
module SR = Steel.Reference

let array_prop (#a: Type) (ptr: P.t a) (x: A.array a) : Tot prop =
  A.g_get_pointer x == ptr

let array (#a: Type) (ptr: P.t a) : Tot Type = (x: A.array a { array_prop ptr x })

let t_array_t
  (#a: Type)
  (t_ptr: P.t a)
: Tot Type0
= if P.g_is_null t_ptr then unit else SR.ghost_ref (array t_ptr)

let t_perm_t
  (#a: Type)
  (t_ptr: P.t a)
: Tot Type0
= if P.g_is_null t_ptr then unit else SR.ghost_ref perm

[@@erasable]
noeq
type tg (#a: Type) (t_ptr: P.t a) = {
  t_array: t_array_t t_ptr;
  t_perm: t_perm_t t_ptr;
}

noeq
type t a = {
  t_ptr: P.t a;
  t_g: tg t_ptr;
  t_prf: squash (P.g_is_null t_ptr == false ==> P.size_v (P.base_array_len (P.base t_ptr)) < 4294967296); // TODO: remove and switch to size_t
}

let null a = {
  t_ptr = P.null a;
  t_g = { t_array = (); t_perm = (); };
  t_prf = ();
}

let g_is_null x = P.g_is_null x.t_ptr

let varrayptr0_refine
  (#a: Type)
  (x: t a)
  (_: t_of emp)
: Tot prop
= g_is_null x == false

let varrayptr0_payload2
  (#a: Type)
  (x: t a)
  (_: t_of (emp `vrefine` varrayptr0_refine x))
  (arp: t_of (SR.ghost_vptr #(array x.t_ptr) x.t_g.t_array `star` SR.ghost_vptr #perm x.t_g.t_perm))
: Tot vprop
= let (ar, p) = arp in
  A.varrayp #a ar p

[@@__steel_reduce__] // to automatically reduce t_of, necessary for the call to normal below
let varrayptr0_payload1
  (#a: Type)
  (x: t a)
  (y: t_of (emp `vrefine` varrayptr0_refine x))
: Tot vprop
= (SR.ghost_vptr #(array x.t_ptr) x.t_g.t_array `star` SR.ghost_vptr #perm x.t_g.t_perm) `vdep` varrayptr0_payload2 x y

let varrayptr0_rewrite
  (#a: Type)
  (x: t a)
  (y: normal (t_of (emp `vrefine` varrayptr0_refine x `vdep` varrayptr0_payload1 x)))
: GTot (v a)
= let (| _, (| (ar, p), w |) |) = y in
  A.length_get_pointer ar;
  {
    array = ar;
    contents = w;
    perm = p;
    prf = ();
  }

let varrayptr0
  (#a: Type)
  (x: t a)
: Tot vprop
= emp `vrefine` varrayptr0_refine x `vdep` varrayptr0_payload1 x `vrewrite` varrayptr0_rewrite x

let is_arrayptr r = hp_of (varrayptr0 r)

let arrayptr_sel r = sel_of (varrayptr0 r)

val intro_varrayptr
  (#opened: _)
  (#a: Type)
  (x: t a)
  (ga: SR.ghost_ref (array x.t_ptr))
  (gp: SR.ghost_ref perm)
  (a: array x.t_ptr)
  (p: perm)
: SteelGhost unit opened
    (SR.ghost_vptr ga `star` SR.ghost_vptr gp `star` A.varrayp a p)
    (fun _ -> varrayptr x)
    (fun h ->
      P.g_is_null x.t_ptr == false /\
      x.t_g.t_array == ga /\
      x.t_g.t_perm == gp /\
      can_be_split (SR.ghost_vptr ga `star` SR.ghost_vptr gp `star` A.varrayp a p) (SR.ghost_vptr ga) /\
      can_be_split (SR.ghost_vptr ga `star` SR.ghost_vptr gp `star` A.varrayp a p) (SR.ghost_vptr gp) /\
      h (SR.ghost_vptr ga) == a /\
      h (SR.ghost_vptr gp) == p
    )
    (fun h _ h' ->
      let res = h' (varrayptr x) in
      res.array == a /\
      res.contents == h (A.varrayp a p) /\
      res.perm == p
    )

#push-options "--z3rlimit 32"
#restart-solver

let intro_varrayptr
  #_ #b x ga gp a p
=
  reveal_star_3 (SR.ghost_vptr ga) (SR.ghost_vptr gp) (A.varrayp a p);
  let pa : squash (t_array_t x.t_ptr == SR.ghost_ref (array x.t_ptr)) = () in
  let pp : squash (t_perm_t x.t_ptr == SR.ghost_ref perm) = () in
  let a' : Ghost.erased (array x.t_ptr) = gget (SR.ghost_vptr ga) in
  assert (Ghost.reveal a' == a);
  let p' : Ghost.erased perm = gget (SR.ghost_vptr gp) in
  assert (Ghost.reveal p' == p);
  intro_vrefine emp (varrayptr0_refine x);
  let y : Ghost.erased (t_of (emp `vrefine` varrayptr0_refine x)) = gget (emp `vrefine` varrayptr0_refine x) in
  change_equal_slprop
    (SR.ghost_vptr ga)
    (SR.ghost_vptr #(array x.t_ptr) x.t_g.t_array);
  change_equal_slprop
    (SR.ghost_vptr gp)
    (SR.ghost_vptr #perm x.t_g.t_perm);
  SR.ghost_vptr #(array x.t_ptr) x.t_g.t_array `reveal_star` SR.ghost_vptr #perm x.t_g.t_perm;
  intro_vdep
    (SR.ghost_vptr #(array x.t_ptr) x.t_g.t_array `star` SR.ghost_vptr #perm x.t_g.t_perm)
    (A.varrayp a p)
    (varrayptr0_payload2 x y);
  intro_vdep
    (emp `vrefine` varrayptr0_refine x)
    (SR.ghost_vptr #(array x.t_ptr) x.t_g.t_array `star` SR.ghost_vptr #perm x.t_g.t_perm `vdep` varrayptr0_payload2 x y)
    (varrayptr0_payload1 x);
  intro_vrewrite
    (emp `vrefine` varrayptr0_refine x `vdep` varrayptr0_payload1 x)
    (varrayptr0_rewrite x);
  assert_norm (
    emp `vrefine` varrayptr0_refine x `vdep` varrayptr0_payload1 x `vrewrite` varrayptr0_rewrite x ==
    varrayptr0 x
  );
  change_equal_slprop
    (emp `vrefine` varrayptr0_refine x `vdep` varrayptr0_payload1 x `vrewrite` varrayptr0_rewrite x)
    (varrayptr0 x);
  change_slprop_rel
    (varrayptr0 x)
    (varrayptr x)
    (fun u v -> u == v)
    (fun _ -> ())

#pop-options

let intro_varrayptr'
  (#opened: _)
  (#b: Type)
  (x: t b)
  (x_ptr: P.t b)
  (ga: SR.ghost_ref (array x_ptr))
  (gp: SR.ghost_ref perm)
  (a: array x_ptr)
  (p: perm)
: SteelGhost unit opened
    (SR.ghost_vptr ga `star` SR.ghost_vptr gp `star` A.varrayp a p)
    (fun _ -> varrayptr x)
    (fun h ->
      x_ptr == x.t_ptr /\
      P.g_is_null x.t_ptr == false /\
      x.t_g.t_array == ga /\
      x.t_g.t_perm == gp /\
      can_be_split (SR.ghost_vptr ga `star` SR.ghost_vptr gp `star` A.varrayp a p) (SR.ghost_vptr ga) /\
      can_be_split (SR.ghost_vptr ga `star` SR.ghost_vptr gp `star` A.varrayp a p) (SR.ghost_vptr gp) /\
      h (SR.ghost_vptr ga) == a /\
      h (SR.ghost_vptr gp) == p
    )
    (fun h _ h' ->
      let res = h' (varrayptr x) in
      res.array == a /\
      res.contents == h (A.varrayp a p) /\
      res.perm == p
    )
=
  let ga' : SR.ghost_ref (array x.t_ptr) = ga in
  change_equal_slprop
    (SR.ghost_vptr ga)
    (SR.ghost_vptr ga');
  intro_varrayptr x ga' gp a p

[@@erasable]
noeq
type elim_varrayptr_t
  (#a: Type)
  (ptr: P.t a)
= {
  e_g_array: SR.ghost_ref (array ptr);
  e_g_perm: SR.ghost_ref perm;
  e_array: array ptr;
  e_perm: perm;
}

val elim_varrayptr
  (#opened: _)
  (#a: Type)
  (x: t a)
: SteelGhost (elim_varrayptr_t x.t_ptr) opened
    (varrayptr x)
    (fun res -> SR.ghost_vptr res.e_g_array `star` SR.ghost_vptr res.e_g_perm `star` A.varrayp res.e_array res.e_perm)
    (fun _ -> True)
    (fun h res h' ->
      let s = h (varrayptr x) in
      P.g_is_null x.t_ptr == false /\
      x.t_g.t_array == res.e_g_array /\
      x.t_g.t_perm == res.e_g_perm /\
      can_be_split (SR.ghost_vptr res.e_g_array `star` SR.ghost_vptr res.e_g_perm `star` A.varrayp res.e_array res.e_perm) (SR.ghost_vptr res.e_g_array) /\
      can_be_split (SR.ghost_vptr res.e_g_array `star` SR.ghost_vptr res.e_g_perm `star` A.varrayp res.e_array res.e_perm) (SR.ghost_vptr res.e_g_perm) /\
      h' (SR.ghost_vptr res.e_g_array) == res.e_array /\
      h' (SR.ghost_vptr res.e_g_perm) == res.e_perm /\
      s.array == res.e_array /\
      s.perm == res.e_perm /\
      h' (A.varrayp res.e_array res.e_perm) == s.contents
    )

let elim_varrayptr
  #_ #b x
=
  change_slprop_rel
    (varrayptr x)
    (varrayptr0 x)
    (fun u v -> u == v)
    (fun _ -> ());
  assert_norm (
    emp `vrefine` varrayptr0_refine x `vdep` varrayptr0_payload1 x `vrewrite` varrayptr0_rewrite x ==
    varrayptr0 x
  );
  change_equal_slprop
    (varrayptr0 x)
    (emp `vrefine` varrayptr0_refine x `vdep` varrayptr0_payload1 x `vrewrite` varrayptr0_rewrite x);
  elim_vrewrite
    (emp `vrefine` varrayptr0_refine x `vdep` varrayptr0_payload1 x)
    (varrayptr0_rewrite x);
  let y : Ghost.erased (t_of (emp `vrefine` varrayptr0_refine x)) = elim_vdep
    (emp `vrefine` varrayptr0_refine x)
    (varrayptr0_payload1 x)
  in
  elim_vrefine emp (varrayptr0_refine x);
  let pa : squash (t_array_t x.t_ptr == SR.ghost_ref (array x.t_ptr)) = () in
  let pp : squash (t_perm_t x.t_ptr == SR.ghost_ref perm) = () in
  change_equal_slprop
    (varrayptr0_payload1 x y)
    (SR.ghost_vptr #(array x.t_ptr) x.t_g.t_array `star` SR.ghost_vptr #perm x.t_g.t_perm `vdep` varrayptr0_payload2 x y);
  let gap : Ghost.erased (t_of (SR.ghost_vptr #(array x.t_ptr) x.t_g.t_array `star` SR.ghost_vptr #perm x.t_g.t_perm)) = elim_vdep
    (SR.ghost_vptr #(array x.t_ptr) x.t_g.t_array `star` SR.ghost_vptr #perm x.t_g.t_perm)
    (varrayptr0_payload2 x y)
  in
  SR.ghost_vptr #(array x.t_ptr) x.t_g.t_array `reveal_star` SR.ghost_vptr #perm x.t_g.t_perm;
  let g_a : Ghost.erased (array x.t_ptr) = SR.ghost_read #(array x.t_ptr) x.t_g.t_array in
  let a : array x.t_ptr = Ghost.reveal g_a in
  let g_p : Ghost.erased perm = SR.ghost_read #perm x.t_g.t_perm in
  let p : perm = Ghost.reveal g_p in
  let res = {
    e_g_array = x.t_g.t_array;
    e_g_perm = x.t_g.t_perm;
    e_array = a;
    e_perm = p;
  } in
  change_equal_slprop
    (SR.ghost_vptr #(array x.t_ptr) x.t_g.t_array)
    (SR.ghost_vptr res.e_g_array);
  change_equal_slprop
    (SR.ghost_vptr #perm x.t_g.t_perm)
    (SR.ghost_vptr res.e_g_perm);
  change_equal_slprop
    (varrayptr0_payload2 x y gap)
    (A.varrayp res.e_array res.e_perm);
  reveal_star_3 (SR.ghost_vptr res.e_g_array) (SR.ghost_vptr res.e_g_perm) (A.varrayp res.e_array res.e_perm);
  res

let varrayptr_not_null
  x
= let res = elim_varrayptr x in
  intro_varrayptr x res.e_g_array res.e_g_perm res.e_array res.e_perm

[@@__steel_reduce__]
let varrayptr_ghost_refs
  (#a: Type)
  (x: t a)
: Tot vprop
= if P.g_is_null x.t_ptr
  then emp
  else SR.ghost_vptr #(array x.t_ptr) x.t_g.t_array `star` SR.ghost_vptr #perm x.t_g.t_perm

let varrayptr_ghost_refs_rewrite
  (#a: Type)
  (x: t a)
  (r: t_of (varrayptr_ghost_refs x))
: GTot (array x.t_ptr `P.gpair` perm)
=
  if P.g_is_null x.t_ptr
  then
    let _ = A.is_null_get_pointer (A.null a) in
    A.null a `P.GPair` full_perm
  else 
    let r : (array x.t_ptr & perm) = r in
    fst r `P.GPair` snd r

[@@__steel_reduce__]
let varrayptr_or_null_payload
  (#a: Type)
  (x: t a)
  (r: (array x.t_ptr `P.gpair` perm))
: Tot vprop
= A.varrayp_or_null (P.GPair?.fst r) (P.GPair?.snd r)

let varrayptr_or_null_rewrite
  (#a: Type)
  (x: t a)
  (r: normal (t_of (varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x `vdep` varrayptr_or_null_payload x)))
: GTot (option (v a))
= let (| P.GPair ar p, r |) = r in
  match P.g_is_null x.t_ptr, r with
  | false, Some r ->
    A.length_get_pointer ar;
    Some ({
      array = ar;
      contents = r;
      perm = p;
      prf = ();
    })
  | _ -> None

[@@__steel_reduce__]
let varrayptr_or_null0
  (#a: Type)
  (x: t a)
: Tot vprop
= varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x `vdep` varrayptr_or_null_payload x `vrewrite` varrayptr_or_null_rewrite x

let is_arrayptr_or_null r = hp_of (varrayptr_or_null0 r)

let arrayptr_or_null_sel r = fun h -> sel_of (varrayptr_or_null0 r) h

#set-options "--ide_id_info_off"

let intro_varrayptr_or_null_none #_ #a x =
  change_equal_slprop
    emp
    (varrayptr_ghost_refs x);
  intro_vrewrite (varrayptr_ghost_refs x) (varrayptr_ghost_refs_rewrite x);
  A.intro_varrayp_or_null_none (A.null a) full_perm;
  intro_vdep
    (varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x)
    (A.varrayp_or_null (A.null a) full_perm)
    (varrayptr_or_null_payload x);
  intro_vrewrite (varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x `vdep` varrayptr_or_null_payload x) (varrayptr_or_null_rewrite x);
  change_equal_slprop
    (varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x `vdep` varrayptr_or_null_payload x `vrewrite` varrayptr_or_null_rewrite x)
    (varrayptr_or_null0 x);
  change_slprop_rel
    (varrayptr_or_null0 x)
    (varrayptr_or_null x)
    (fun u v -> u == v)
    (fun h ->
      assert_norm (hp_of (varrayptr_or_null0 x) == hp_of (varrayptr_or_null x));
      assert_norm (sel_of (varrayptr_or_null0 x) h === sel_of (varrayptr_or_null x) h)
    )

let intro_varrayptr_or_null_some #_ #a x =
  let r = elim_varrayptr x in
  reveal_star (SR.ghost_vptr r.e_g_array) (SR.ghost_vptr r.e_g_perm);
  change_equal_slprop
    (SR.ghost_vptr r.e_g_array `star` SR.ghost_vptr r.e_g_perm)
    (varrayptr_ghost_refs x);
  intro_vrewrite (varrayptr_ghost_refs x) (varrayptr_ghost_refs_rewrite x);
  A.intro_varrayp_or_null_some r.e_array r.e_perm;
  intro_vdep
    (varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x)
    (A.varrayp_or_null r.e_array r.e_perm)
    (varrayptr_or_null_payload x);
  intro_vrewrite (varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x `vdep` varrayptr_or_null_payload x) (varrayptr_or_null_rewrite x);
  change_equal_slprop
    (varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x `vdep` varrayptr_or_null_payload x `vrewrite` varrayptr_or_null_rewrite x)
    (varrayptr_or_null0 x);
  change_slprop_rel
    (varrayptr_or_null0 x)
    (varrayptr_or_null x)
    (fun u v -> u == v)
    (fun h ->
      assert_norm (hp_of (varrayptr_or_null0 x) == hp_of (varrayptr_or_null x));
      assert_norm (sel_of (varrayptr_or_null0 x) h === sel_of (varrayptr_or_null x) h)
    )

val intro_varrayptr_or_null
  (#opened: _)
  (#b: Type)
  (x: P.t b)
  (a: array x)
  (p: perm)
: SteelGhost (Ghost.erased (t b)) opened
    (A.varrayp_or_null a p)
    (fun res -> varrayptr_or_null res)
    (fun _ -> 
      P.g_is_null x == false ==> P.size_v (P.base_array_len (P.base x)) < 4294967296 // TODO: remove and switch to size_t
    )
    (fun h res h' ->
      res.t_ptr == x /\
      begin match P.g_is_null x, h (A.varrayp_or_null a p), h' (varrayptr_or_null res) with
      | true, None, None -> True
      | false, Some s, Some r ->
        r.array == a /\
        r.perm == p /\
        r.contents == s
      | _ -> False    
      end
    )

let intro_varrayptr_or_null
  #_ #b x a p
=
  A.is_null_get_pointer a;
  if P.g_is_null x
  then begin
    A.assert_null a _;
    let res : Ghost.erased (t b) = Ghost.hide (null _) in
    intro_varrayptr_or_null_none res;
    res
  end else begin
    A.assert_not_null a _;
    let ga : SR.ghost_ref (array x) = SR.ghost_alloc a in
    let gp : SR.ghost_ref perm = SR.ghost_alloc p in
    let res : Ghost.erased (t b) = Ghost.hide ({
      t_ptr = x;
      t_g = {
        t_array = ga;
        t_perm = gp;
      };
      t_prf = ();
    }) in
    reveal_star_3 (SR.ghost_vptr ga) (SR.ghost_vptr gp) (A.varrayp a p);
    intro_varrayptr' res x ga gp a p;
    intro_varrayptr_or_null_some res;
    res
  end

unfold
let coerce (#a: Type) (x: a) (b: Type) : Pure b (requires (a == b)) (ensures (fun y -> a == b /\ x == y)) = x

unfold
let coerce2 (#a: Type) (x: a) (b: Type) (sq: squash (a == b)) : Tot b = x

let elim_varrayptr_or_null_some #_ #a x =
  change_slprop_rel
    (varrayptr_or_null x)
    (varrayptr_or_null0 x)
    (fun u v -> u == v)
    (fun h ->
      assert_norm (hp_of (varrayptr_or_null0 x) == hp_of (varrayptr_or_null x));
      assert_norm (sel_of (varrayptr_or_null0 x) h === sel_of (varrayptr_or_null x) h)
    );
  elim_vrewrite
    (varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x `vdep` varrayptr_or_null_payload x) (varrayptr_or_null_rewrite x);
  let _ : squash (P.g_is_null x.t_ptr == false) = () in
  let pa : squash (t_array_t x.t_ptr == SR.ghost_ref (array x.t_ptr)) = () in
  let pp : squash (t_perm_t x.t_ptr == SR.ghost_ref perm) = () in
  let ga : SR.ghost_ref (array x.t_ptr) = coerce2 x.t_g.t_array (SR.ghost_ref (array x.t_ptr)) pa in
  let gp : SR.ghost_ref perm = coerce2 x.t_g.t_perm (SR.ghost_ref perm) pp in
  let g : Ghost.erased (P.gpair (array x.t_ptr) perm) = elim_vdep
    (varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x)
    (varrayptr_or_null_payload x)
  in
  elim_vrewrite (varrayptr_ghost_refs x) (varrayptr_ghost_refs_rewrite x);
  change_equal_slprop
    (varrayptr_ghost_refs x)
    (SR.ghost_vptr ga `star` SR.ghost_vptr gp);
  SR.ghost_vptr ga `reveal_star` SR.ghost_vptr gp;
  A.is_null_get_pointer (P.GPair?.fst g);
  change_equal_slprop
    (varrayptr_or_null_payload x g)
    (A.varrayp_or_null (P.GPair?.fst g) (P.GPair?.snd g));
  A.assert_not_null (P.GPair?.fst g) (P.GPair?.snd g);
  reveal_star_3 (SR.ghost_vptr ga) (SR.ghost_vptr gp) (A.varrayp (P.GPair?.fst g) (P.GPair?.snd g));
  intro_varrayptr x ga gp (P.GPair?.fst g) (P.GPair?.snd g)

let elim_varrayptr_or_null_none #_ #a x =
  change_slprop_rel
    (varrayptr_or_null x)
    (varrayptr_or_null0 x)
    (fun u v -> u == v)
    (fun h ->
      assert_norm (hp_of (varrayptr_or_null0 x) == hp_of (varrayptr_or_null x));
      assert_norm (sel_of (varrayptr_or_null0 x) h === sel_of (varrayptr_or_null x) h)
    );
  elim_vrewrite
    (varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x `vdep` varrayptr_or_null_payload x) (varrayptr_or_null_rewrite x);
  let g : Ghost.erased (P.gpair (array x.t_ptr) perm) = elim_vdep
    (varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x)
    (varrayptr_or_null_payload x)
  in
  change_equal_slprop
    (varrayptr_or_null_payload x g)
    (A.varrayp_or_null (P.GPair?.fst g) (P.GPair?.snd g));
  A.is_null_get_pointer (P.GPair?.fst g);
  if P.g_is_null x.t_ptr
  then begin
    A.assert_null (P.GPair?.fst g) (P.GPair?.snd g);
    elim_vrewrite (varrayptr_ghost_refs x) (varrayptr_ghost_refs_rewrite x);
    change_equal_slprop
      (varrayptr_ghost_refs x)
      emp
  end else begin
    A.assert_not_null (P.GPair?.fst g) (P.GPair?.snd g);
    assert False;
    change_slprop_rel
      ((varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x) `star` A.varrayp (P.GPair?.fst g) (P.GPair?.snd g))
      emp
      (fun _ _ -> False)
      (fun _ -> ())
  end

let is_null_none
  (#opened: _)
  (#a: Type)
  (x: t a)
: SteelGhost unit opened
    (varrayptr_or_null x)
    (fun _ -> varrayptr_or_null x)
    (fun _ -> True)
    (fun h _ h' ->
      let s = h (varrayptr_or_null x) in
      h' (varrayptr_or_null x) == s /\
      g_is_null x == None? s
    )
=
  if g_is_null x
  then begin
    elim_varrayptr_or_null_none x;
    intro_varrayptr_or_null_none x
  end else begin
    elim_varrayptr_or_null_some x;
    intro_varrayptr_or_null_some x
  end

let is_null
  #_ #a x
=
  is_null_none x;
  change_slprop_rel
    (varrayptr_or_null x)
    (varrayptr_or_null0 x)
    (fun u v -> u == v)
    (fun h ->
      assert_norm (hp_of (varrayptr_or_null0 x) == hp_of (varrayptr_or_null x));
      assert_norm (sel_of (varrayptr_or_null0 x) h === sel_of (varrayptr_or_null x) h)
    );
  elim_vrewrite
    (varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x `vdep` varrayptr_or_null_payload x) (varrayptr_or_null_rewrite x);
  let g : Ghost.erased (P.gpair (array x.t_ptr) perm) = elim_vdep
    (varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x)
    (varrayptr_or_null_payload x)
  in
  change_equal_slprop
    (varrayptr_or_null_payload x g)
    (A.varrayp_or_null (Ghost.reveal (Ghost.hide (P.GPair?.fst g))) (P.GPair?.snd g));
  let ar = A.reveal x.t_ptr (Ghost.hide (P.GPair?.fst g)) (P.GPair?.snd g) in
  A.is_null_get_pointer ar;
  let res = A.is_null ar _ in
  intro_vdep
    (varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x)
    (A.varrayp_or_null ar (P.GPair?.snd g))
    (varrayptr_or_null_payload x);
  intro_vrewrite
    (varrayptr_ghost_refs x `vrewrite` varrayptr_ghost_refs_rewrite x `vdep` varrayptr_or_null_payload x) (varrayptr_or_null_rewrite x);
  change_slprop_rel
    (varrayptr_or_null0 x)
    (varrayptr_or_null x)
    (fun u v -> u == v)
    (fun h ->
      assert_norm (hp_of (varrayptr_or_null0 x) == hp_of (varrayptr_or_null x));
      assert_norm (sel_of (varrayptr_or_null0 x) h === sel_of (varrayptr_or_null x) h)
    );
  return res

let join al ar =
  let el = elim_varrayptr al in
  let er = elim_varrayptr ar in
  SR.ghost_free er.e_g_array;
  SR.ghost_free er.e_g_perm;
  change_equal_slprop
    (A.varrayp er.e_array er.e_perm)
    (A.varrayp er.e_array el.e_perm);
  let a' = A.join' el.e_array er.e_array _ in
  A.length_get_pointer a';
  A.get_pointer_merge el.e_array er.e_array;
  SR.ghost_write el.e_g_array (Ghost.reveal a');
  reveal_star_3 (SR.ghost_vptr el.e_g_array) (SR.ghost_vptr el.e_g_perm) (A.varrayp a' el.e_perm);
  intro_varrayptr al el.e_g_array el.e_g_perm a' el.e_perm

let split x i =
  varrayptr_not_null x;
  let e = elim_varrayptr x in
  change_equal_slprop
    (A.varrayp e.e_array e.e_perm)
    (A.varrayp (Ghost.hide e.e_array) e.e_perm);
  A.intro_varrayp_or_null_some (Ghost.hide e.e_array) e.e_perm;
  let a = A.reveal x.t_ptr (Ghost.hide e.e_array) _ in
  A.assert_not_null a e.e_perm;
  let j = P.mk_size_t i in
  let alar = A.splitp a _ j in
  A.get_pointer_gsplit a j;
  SR.ghost_write e.e_g_array (fst alar);
  reveal_star_3 (SR.ghost_vptr e.e_g_array) (SR.ghost_vptr e.e_g_perm) (A.varrayp (fst alar) e.e_perm);
  intro_varrayptr x e.e_g_array e.e_g_perm (fst alar) e.e_perm;
  let ar = snd alar in
  change_equal_slprop
    (A.varrayp (snd alar) e.e_perm)
    (A.varrayp ar e.e_perm);
  A.intro_varrayp_or_null_some ar _;
  let pr = A.get_pointer ar _ in
  A.assert_not_null ar _;
  let ga : SR.ghost_ref (array pr) = SR.ghost_alloc ar in
  let gp : SR.ghost_ref perm = SR.ghost_alloc e.e_perm in
  let res = ({
    t_ptr = pr;
    t_g = {
      t_array = ga;
      t_perm = gp;
    };
    t_prf = ();
  }) in
  reveal_star_3 (SR.ghost_vptr ga) (SR.ghost_vptr gp) (A.varrayp ar e.e_perm);
  intro_varrayptr' res pr ga gp ar e.e_perm;
  return res

let alloc x n =
  let ar = A.malloc x (P.mk_size_t n) in
  let p = A.get_pointer ar _ in
  A.is_null_get_pointer ar;
  A.length_get_pointer ar;
  let g = intro_varrayptr_or_null p ar _ in
  let res = {
    t_ptr = p;
    t_g = g.t_g;
    t_prf = g.t_prf;
  } in
  change_equal_slprop
    (varrayptr_or_null g)
    (varrayptr_or_null res);
  return res

let index #b r i =
  let e = elim_varrayptr r in
  let g : Ghost.erased (A.array b) = Ghost.hide e.e_array in
  change_equal_slprop
    (A.varrayp e.e_array e.e_perm)
    (A.varrayp g e.e_perm);
  A.intro_varrayp_or_null_some g _;
  let a = A.reveal r.t_ptr g _ in
  A.assert_not_null a _;
  let res = A.indexp a _ (P.mk_size_t i) in
  intro_varrayptr r e.e_g_array e.e_g_perm a _;
  return res

let upd #b r i v =
  let e = elim_varrayptr r in
  let g : Ghost.erased (A.array b) = Ghost.hide e.e_array in
  change_equal_slprop
    (A.varrayp e.e_array e.e_perm)
    (A.varray g);
  A.intro_varrayp_or_null_some g _;
  let a = A.reveal r.t_ptr g _ in
  A.assert_not_null a _;
  A.upd a (P.mk_size_t i) v;
  intro_varrayptr r e.e_g_array e.e_g_perm a _

let free r =
  let e = elim_varrayptr r in
  SR.ghost_free e.e_g_array;
  SR.ghost_free e.e_g_perm;
  let g : Ghost.erased (A.array _) = Ghost.hide e.e_array in
  change_equal_slprop
    (A.varrayp e.e_array e.e_perm)
    (A.varray g);
  A.intro_varrayp_or_null_some g _;
  let a = A.reveal r.t_ptr g _ in
  A.assert_not_null a _;
  A.free a

let share r =
  let e = elim_varrayptr r in
  let p = A.share e.e_array _ in
  SR.ghost_write e.e_g_perm p;
  reveal_star_3 (SR.ghost_vptr e.e_g_array) (SR.ghost_vptr e.e_g_perm) (A.varrayp e.e_array p);
  intro_varrayptr r e.e_g_array e.e_g_perm e.e_array p;
  let ga : SR.ghost_ref (array r.t_ptr) = SR.ghost_alloc e.e_array in
  let gp : SR.ghost_ref perm = SR.ghost_alloc p in
  let res = {
    t_ptr = r.t_ptr;
    t_g = {
      t_array = ga;
      t_perm = gp;
    };
    t_prf = ();
  } in
  reveal_star_3 (SR.ghost_vptr ga) (SR.ghost_vptr gp) (A.varrayp e.e_array p);
  intro_varrayptr' res r.t_ptr ga gp e.e_array p;
  return res

let gather r1 r2 =
  let e1 = elim_varrayptr r1 in
  let e2 = elim_varrayptr r2 in
  SR.ghost_free e2.e_g_array;
  SR.ghost_free e2.e_g_perm;
  assert (e2.e_array == e1.e_array);
  change_equal_slprop
    (A.varrayp e2.e_array e2.e_perm)
    (A.varrayp e1.e_array e2.e_perm);
  let p = A.gather e1.e_array e1.e_perm e2.e_perm in
  SR.ghost_write e1.e_g_perm p;
  reveal_star_3 (SR.ghost_vptr e1.e_g_array) (SR.ghost_vptr e1.e_g_perm) (A.varrayp e1.e_array p);
  intro_varrayptr r1 e1.e_g_array e1.e_g_perm e1.e_array p

let enter x p =
  A.intro_varrayp_or_null_some x _;
  let pt = A.get_pointer x _ in
  A.assert_not_null x _;
  A.is_null_get_pointer x;
  A.length_get_pointer x;
  let ga : SR.ghost_ref (array pt) = SR.ghost_alloc x in
  let gp : SR.ghost_ref perm = SR.ghost_alloc p in
  let res = {
    t_ptr = pt;
    t_g = {
      t_array = ga;
      t_perm = gp;
    };
    t_prf = ();
  } in
  reveal_star_3 (SR.ghost_vptr ga) (SR.ghost_vptr gp) (A.varrayp x p);
  intro_varrayptr' res pt ga gp x p;
  return res

let exit x =
  let e = elim_varrayptr x in
  reveal_star_3 (SR.ghost_vptr e.e_g_array) (SR.ghost_vptr e.e_g_perm) (A.varrayp e.e_array e.e_perm);
  SR.ghost_free e.e_g_array;
  SR.ghost_free e.e_g_perm;
  change_equal_slprop
    (A.varrayp e.e_array e.e_perm)
    (A.varrayp (Ghost.hide e.e_array) e.e_perm);
  A.intro_varrayp_or_null_some (Ghost.hide e.e_array) e.e_perm;
  let a = A.reveal x.t_ptr (Ghost.hide e.e_array) _ in
  A.assert_not_null a e.e_perm;
  let res = (a, e.e_perm) in
  change_equal_slprop
    (A.varrayp a e.e_perm)
    (A.varrayp (fst res) (snd res));
  return res
