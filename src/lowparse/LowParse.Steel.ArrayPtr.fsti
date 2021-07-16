(*
   Copyright 2021 Microsoft Research

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

(* A partial model for C array pointers. Given a type t, we model type
   t* with the following operations:

   * null

   * alloc, free

   * read at some offset p[i]
   
   * additive pointer arithmetic: if p is an array pointer, then the
     user has permission to access n cells to its right-hand-side (no
     subtractions.) So if i <= n, then operation q = p+i splits the
     permission into two parts, p for cells from 0 to i-1, and q for
     cells from i to n-1. User needs to explicitly return the
     permission by "merging" back q into p.
*)

module LowParse.Steel.ArrayPtr
open Steel.Memory
open Steel.Effect
open Steel.FractionalPermission
open Steel.Effect.Atomic
module U32 = FStar.UInt32
module A = Steel.Array

val t (t:Type u#0) : Type u#0

val null (a: Type) : Tot (t a)

val g_is_null (#a: Type) (x: t a) : Ghost bool
  (requires True)
  (ensures (fun y -> y == true <==> x == null a))

[@@erasable]
noeq type v (t: Type u#0) = {
  array: A.array t;                      (* spatial permission range *)
  contents: Seq.lseq t (A.length array); (* actual contents *)
  perm: perm;                            (* temporal permission *)
  prf: squash (A.length array < 4294967296); (* TODO: remove and switch to size_t *)
}

val is_arrayptr (#a:Type0) (r:t a) : slprop u#1
val arrayptr_sel (#a:Type0) (r:t a) : selector (v a) (is_arrayptr r)

[@@ __steel_reduce__]
let varrayptr' #a r : vprop' =
  {hp = is_arrayptr r;
   t = v a;
   sel = arrayptr_sel r}

[@@ __steel_reduce__]
let varrayptr r = VUnit (varrayptr' r)

[@@ __steel_reduce__]
let sel (#a:Type) (#p:vprop) (r:t a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (varrayptr r) /\ True)})
: GTot (v a)
  = h (varrayptr r)

val varrayptr_not_null
  (#opened: _)
  (#a: Type)
  (x: t a)
: SteelGhost unit opened
    (varrayptr x)
    (fun _ -> varrayptr x)
    (fun _ -> True)
    (fun h _ h' ->
      h' (varrayptr x) == h (varrayptr x) /\
      g_is_null x == false
    )


val is_arrayptr_or_null (#a:Type0) (r:t a) : slprop u#1
val arrayptr_or_null_sel (#a:Type0) (r:t a) : selector (option (v a)) (is_arrayptr_or_null r)

[@@ __steel_reduce__]
let varrayptr_or_null' #a r : vprop' =
  {hp = is_arrayptr_or_null r;
   t = option (v a);
   sel = arrayptr_or_null_sel r}

[@@ __steel_reduce__]
let varrayptr_or_null r = VUnit (varrayptr_or_null' r)

val intro_varrayptr_or_null_none
  (#opened: _)
  (#a: Type)
  (x: t a)
: SteelGhost unit opened
    emp
    (fun _ -> varrayptr_or_null x)
    (fun _ -> g_is_null x == true)
    (fun _ _ h' -> h' (varrayptr_or_null x) == None)

val intro_varrayptr_or_null_some
  (#opened: _)
  (#a: Type)
  (x: t a)
: SteelGhost unit opened
    (varrayptr x)
    (fun _ -> varrayptr_or_null x)
    (fun _ -> True)
    (fun h _ h' ->
      g_is_null x == false /\
      h' (varrayptr_or_null x) == Some (h (varrayptr x)
    ))

val elim_varrayptr_or_null_some
  (#opened: _)
  (#a: Type)
  (x: t a)
: SteelGhost unit opened
    (varrayptr_or_null x)
    (fun _ -> varrayptr x)
    (fun h -> g_is_null x == false \/ Some? (h (varrayptr_or_null x)))
    (fun h _ h' ->
      g_is_null x == false /\
      h (varrayptr_or_null x) == Some (h' (varrayptr x))
    )

val elim_varrayptr_or_null_none
  (#opened: _)
  (#a: Type)
  (x: t a)
: SteelGhost unit opened
    (varrayptr_or_null x)
    (fun _ -> emp)
    (fun h -> g_is_null x == true \/ None? (h (varrayptr_or_null x)))
    (fun h _ _ ->
      g_is_null x == true /\
      h (varrayptr_or_null x) == None
    )

val is_null
  (#opened: _)
  (#a: Type)
  (x: t a)
: SteelAtomicBase bool false opened Unobservable
    (varrayptr_or_null x)
    (fun _ -> varrayptr_or_null x)
    (fun _ -> True)
    (fun h res h' ->
      let s = h (varrayptr_or_null x) in
      h' (varrayptr_or_null x) == s /\
      res == None? s /\
      res == g_is_null x
    )

(* Splitting an array (inspired from Steel.Array) *)

val join (#opened: _) (#a:Type) (al ar:t a)
  : SteelGhost unit opened
          (varrayptr al `star` varrayptr ar)
          (fun _ -> varrayptr al)
          (fun h ->
            A.adjacent (h (varrayptr al)).array (h (varrayptr ar)).array /\
            (h (varrayptr al)).perm == (h (varrayptr ar)).perm
          )
          (fun h _ h' ->
            let cl = h (varrayptr al) in
            let cr = h (varrayptr ar) in
            let c' = h' (varrayptr al) in
            A.merge_into cl.array cr.array c'.array /\
            c'.perm == cl.perm /\
            c'.contents == cl.contents `Seq.append` cr.contents
          )

val split (#opened: _) (#a:Type) (x: t a) (i:U32.t)
  : SteelAtomicBase (t a) false opened Unobservable
          (varrayptr x)
          (fun res -> varrayptr x `star` varrayptr res)
          (fun h -> U32.v i <= A.length (h (varrayptr x)).array)
          (fun h res h' ->
            let s = h (varrayptr x) in
            let sl = h' (varrayptr x) in
            let sr = h' (varrayptr res) in
            U32.v i <= A.length s.array /\
            A.merge_into sl.array sr.array s.array /\
            sl.perm == s.perm /\
            sr.perm == s.perm /\
            sl.contents == Seq.slice s.contents 0 (U32.v i) /\
            A.length sl.array == U32.v i /\
            A.length sr.array == A.length s.array - U32.v i /\
            sr.contents == Seq.slice s.contents (U32.v i) (A.length s.array) /\
            s.contents == sl.contents `Seq.append` sr.contents
          )

val alloc (#a:Type) (x:a) (n:U32.t)
  : Steel (t a)
             emp
             (fun r -> varrayptr_or_null r)
             (requires fun _ -> U32.v n > 0)
             (ensures fun _ r h1 ->
               match g_is_null r, h1 (varrayptr_or_null r) with
               | true, None -> True
               | false, Some s ->
                 A.length s.array == U32.v n /\
                 s.contents == Seq.create (U32.v n) x /\
                 s.perm == full_perm /\
                 A.freeable s.array
               | _ -> False
             )

val index (#a:Type) (r: t a) (i:U32.t)
  : Steel a
             (varrayptr r)
             (fun _ -> varrayptr r)
             (requires fun h -> U32.v i < A.length (h (varrayptr r)).array)
             (ensures fun h0 y h1 ->
               let s = h0 (varrayptr r) in
               h1 (varrayptr r) == s /\
               U32.v i < A.length s.array /\
               y == Seq.index s.contents (U32.v i))

val upd (#a:Type) (r: t a) (i:U32.t) (x:a)
  : Steel unit
             (varrayptr r)
             (fun _ -> varrayptr r)
             (requires fun h ->
               (h (varrayptr r)).perm == full_perm /\
               U32.v i < A.length (h (varrayptr r)).array
             )
             (ensures fun h0 _ h1 ->
               let s = h0 (varrayptr r) in
               let s' = h1 (varrayptr r) in
               s'.array == s.array /\
               s'.perm == full_perm /\
               U32.v i < A.length s.array /\
               s'.contents == Seq.upd s.contents (U32.v i) x)

val free (#a:Type) (r:t a)
  : Steel unit
             (varrayptr r)
             (fun _ -> emp)
             (requires fun h ->
               (h (varrayptr r)).perm == full_perm /\
               A.freeable (h (varrayptr r)).array
             )
             (ensures fun _ _ _ -> True)

val share (#opened: _) (#a: Type) (r: t a)
  : SteelAtomicBase (t a) false opened Unobservable
    (varrayptr r)
    (fun res -> varrayptr r `star` varrayptr res)
    (fun _ -> True)
    (fun h res h' ->
      let s = h (varrayptr r) in
      let d = h' (varrayptr res) in
      let s' = h' (varrayptr r) in
      s'.perm == half_perm s.perm /\
      s'.array == s.array /\
      s'.contents == s.contents /\
      d.array == s.array /\
      d.perm == half_perm s.perm /\
      d.contents == s.contents
    )

val gather
  (#opened: _)
  (#a: Type)
  (r1 r2: t a)
: SteelGhost unit opened
    (varrayptr r1 `star` varrayptr r2)
    (fun _ -> varrayptr r1)
    (fun h ->
      (h (varrayptr r1)).array == (h (varrayptr r2)).array
    )
    (fun h res h' ->
      let s1 = h (varrayptr r1) in
      let s2 = h (varrayptr r2) in
      let s' = h' (varrayptr r1) in
      s'.array == s1.array /\
      s'.array == s2.array /\
      s'.contents == s1.contents /\
      s'.contents == s2.contents /\
      s'.perm == s1.perm `sum_perm` s2.perm
    )

(* Entering and exiting the abstraction *)

module P = Steel.Pointer

val enter
  (#opened: _)
  (#a: Type)
  (x: A.array a)
  (p: perm)
: SteelAtomicBase (t a) false opened Unobservable
    (A.varrayp x p)
    (fun res -> varrayptr res)
    (fun _ ->
      let p = A.g_get_pointer x in
      (P.g_is_null p == false ==> P.size_v (P.base_array_len (P.base p)) < 4294967296) // TODO: remove and use size_t instead
    )
    (fun h res h' ->
      let s = h' (varrayptr res) in
      s.array == x /\
      s.perm == p /\
      s.contents == h (A.varrayp x p)
    )

val exit
  (#opened: _)
  (#a: Type)
  (x: t a)
: SteelAtomicBase (A.array a & perm) false opened Unobservable
    (varrayptr x)
    (fun res -> A.varrayp (fst res) (snd res))
    (fun _ -> True)
    (fun h res h' ->
      let s = h (varrayptr x) in
      fst res == s.array /\
      snd res == s.perm /\
      h' (A.varrayp (fst res) (snd res)) == s.contents
    )
