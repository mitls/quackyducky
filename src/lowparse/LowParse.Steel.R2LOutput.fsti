module LowParse.Steel.R2LOutput
include LowParse.Bytes

module S = Steel.Memory
module SP = Steel.FractionalPermission
module SE = Steel.Effect
module SEA = Steel.Effect.Atomic
module A = Steel.Array
module AP = LowParse.Steel.ArrayPtr
module U32 = FStar.UInt32

(* Right-to-left output buffer *)

val t: Type0

val null : t

val g_is_null (x: t) : Ghost bool
  (requires True)
  (ensures (fun y -> y == true <==> x == null))

val vp_hp
  (x: t)
: Tot (S.slprop u#1)

val vp_sel
  (x: t)
: Tot (SE.selector (A.array byte) (vp_hp x))

[@SE.__steel_reduce__]
let vp' 
  (x: t)
: Tot SE.vprop'
= {
  SE.hp = vp_hp x;
  SE.t = A.array byte;
  SE.sel = vp_sel x;
}

[@SE.__steel_reduce__]
let vp
  (x: t)
: Tot SE.vprop
= SE.VUnit (vp' x)

val vp_not_null
  (#opened: _)
  (x: t)
: SEA.SteelGhost unit opened
    (vp x)
    (fun _ -> vp x)
    (fun _ -> True)
    (fun h _ h' ->
      h' (vp x) == h (vp x) /\
      g_is_null x == false
    )

val vp_or_null_hp
  (x: t)
: Tot (S.slprop u#1)

val vp_or_null_sel
  (x: t)
: Tot (SE.selector (option (A.array byte)) (vp_or_null_hp x))

[@SE.__steel_reduce__]
let vp_or_null' 
  (x: t)
: Tot SE.vprop'
= {
  SE.hp = vp_or_null_hp x;
  SE.t = option (A.array byte);
  SE.sel = vp_or_null_sel x;
}

[@SE.__steel_reduce__]
let vp_or_null
  (x: t)
: Tot SE.vprop
= SE.VUnit (vp_or_null' x)

val intro_vp_or_null_none
  (#opened: _)
  (x: t)
: SEA.SteelGhost unit opened
    SE.emp
    (fun _ -> vp_or_null x)
    (fun _ -> g_is_null x == true)
    (fun _ _ h' -> h' (vp_or_null x) == None)

val intro_vp_or_null_some
  (#opened: _)
  (x: t)
: SEA.SteelGhost unit opened
    (vp x)
    (fun _ -> vp_or_null x)
    (fun _ -> True)
    (fun h _ h' ->
      g_is_null x == false /\
      h' (vp_or_null x) == Some (h (vp x)
    ))

val elim_vp_or_null_some
  (#opened: _)
  (x: t)
: SEA.SteelGhost unit opened
    (vp_or_null x)
    (fun _ -> vp x)
    (fun h -> g_is_null x == false \/ Some? (h (vp_or_null x)))
    (fun h _ h' ->
      g_is_null x == false /\
      h (vp_or_null x) == Some (h' (vp x))
    )

val elim_vp_or_null_none
  (#opened: _)
  (x: t)
: SEA.SteelGhost unit opened
    (vp_or_null x)
    (fun _ -> SE.emp)
    (fun h -> g_is_null x == true \/ None? (h (vp_or_null x)))
    (fun h _ _ ->
      g_is_null x == true /\
      h (vp_or_null x) == None
    )

val is_null
  (#opened: _)
  (x: t)
: SEA.SteelAtomicBase bool false opened SEA.Unobservable
    (vp_or_null x)
    (fun _ -> vp_or_null x)
    (fun _ -> True)
    (fun h res h' ->
      let s = h (vp_or_null x) in
      h' (vp_or_null x) == s /\
      res == None? s /\
      res == g_is_null x
    )

let make_vprop_post
  (x: AP.t byte)
  (res: t)
: Tot SE.vprop
= 
  if g_is_null res then AP.varrayptr x else SE.emp

val make
  (x: AP.t byte)
  (len: U32.t)
: SE.Steel t
    (AP.varrayptr x)
    (fun res -> vp_or_null res `SE.star` make_vprop_post x res)
    (fun h ->
      (h (AP.varrayptr x)).AP.perm == SP.full_perm /\
      A.length (h (AP.varrayptr x)).AP.array == U32.v len
    )
    (fun h res h' ->
      let s = h' (vp_or_null res) in
      g_is_null res == None? s /\
      (g_is_null res == true ==> h' (AP.varrayptr x) == h (AP.varrayptr x)) /\
      (g_is_null res == false ==> (
        Some? s /\
        (Some?.v s) == (h (AP.varrayptr x)).AP.array /\
        A.length (Some?.v s) == U32.v len
      ))
    )

let alloc
  (len: U32.t)
: SE.Steel t
    SE.emp
    (fun res -> vp_or_null res)
    (fun _ -> U32.v len > 0)
    (fun _ res h' ->
      match g_is_null res, h' (vp_or_null res) with
      | true, None -> True
      | false, Some a ->
        A.length a == U32.v len /\
        A.freeable a
      | _ -> False
    )
=
  let x = AP.alloc 0uy len in
  if AP.is_null x
  then begin
    AP.elim_varrayptr_or_null_none x;
    intro_vp_or_null_none null;
    SEA.return null
  end else begin
    AP.elim_varrayptr_or_null_some x;
    let g : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr x) in
    assert (g.AP.perm == Steel.FractionalPermission.full_perm);
    let res = make x len in
    if is_null res
    then begin
      SEA.change_equal_slprop
        (if g_is_null res then AP.varrayptr x else SE.emp)
        (AP.varrayptr x);
      AP.free x
    end else begin
      SEA.noop ();
      SEA.change_equal_slprop
        (if g_is_null res then AP.varrayptr x else SE.emp)
        SE.emp
    end;
    SEA.return res
  end

val len
  (x: t)
: SE.Steel U32.t
    (vp x)
    (fun _ -> vp x)
    (fun _ -> True)
    (fun h len h' ->
      h (vp x) == h' (vp x) /\
      A.length (h' (vp x)) == U32.v len
    )

val split
  (x: t)
  (len: U32.t)
: SE.Steel (AP.t byte)
    (vp x)
    (fun res -> vp x `SE.star` AP.varrayptr res)
    (fun h -> U32.v len <= A.length (h (vp x)))
    (fun h res h' ->
      let ar = (h' (AP.varrayptr res)).AP.array in
      (h' (AP.varrayptr res)).AP.perm == SP.full_perm /\
      A.merge_into (h' (vp x)) ar (h (vp x)) /\
      A.length ar == U32.v len
    )

val merge
  (x: t)
  (y: AP.t byte)
  (len: U32.t)
: SE.Steel unit
    (vp x `SE.star` AP.varrayptr y)
    (fun res -> vp x)
    (fun h ->
      let ar = (h (AP.varrayptr y)).AP.array in
      (h (AP.varrayptr y)).AP.perm == SP.full_perm /\
      U32.v len == A.length ar /\
      A.adjacent (h (vp x)) ar
    )
    (fun h _ h' ->
      A.merge_into (h (vp x)) (h (AP.varrayptr y)).AP.array (h' (vp x))
    )

val free
  (x: t)
: SE.Steel unit
    (vp x)
    (fun _ -> SE.emp)
    (fun h -> A.freeable (h (vp x)))
    (fun _ _ _ -> True)
