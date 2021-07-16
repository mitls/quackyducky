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
module EverParse3d.Actions
module I = EverParse3d.InputStream
module Cast = FStar.Int.Cast
module HS = FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer
open LowStar.BufferOps
open Prelude
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HST = FStar.HyperStack.ST

// inline_for_extraction
// let ___PUINT8 = LPL.puint8

let hinv = HS.mem -> Type
let extends h1 h0 = forall #a #r #s (b:mbuffer a r s). {:pattern live h1 b} live h0 b ==> live h1 b
let modifies_none_extends (h0 h1:HS.mem)
  : Lemma (modifies loc_none h0 h1 ==> h1 `extends` h0) = ()
let liveness_inv = i:hinv {
  forall h0 h1. {:pattern (i h1); (h1 `extends` h0)}  i h0 /\ h1 `extends` h0 ==> i h1
}
let mem_inv  = liveness_inv
let slice_inv = loc -> mem_inv
let inv_implies (inv0 inv1:slice_inv) =
  forall i h.
    inv0 i h ==> inv1 i h
let true_inv : slice_inv = fun _ _ -> True
let conj_inv (i0 i1:slice_inv) : slice_inv = fun sl h -> i0 sl h /\ i1 sl h
let eloc = FStar.Ghost.erased B.loc
let eloc_union (l1 l2:eloc) : Tot eloc = B.loc_union l1 l2
let eloc_none : eloc = B.loc_none
let eloc_includes (l1 l2:eloc) = B.loc_includes l1 l2
let ptr_loc #a (x:B.pointer a) : Tot eloc = B.loc_buffer x
let ptr_inv #a (x:B.pointer a) : slice_inv = fun (sl:_) h -> B.live h x

inline_for_extraction noextract
val action
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (p:parser k t)
      (inv:slice_inv)
      (l:eloc)
      (on_success:bool)
      (a:Type)
    : Type u#0

inline_for_extraction noextract
val validate_with_action_t
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (p:parser k t)
      (inv:slice_inv)
      (l:eloc)
      (allow_reading:bool)
    : Type u#0

inline_for_extraction noextract
val validate_eta
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#inv:slice_inv)
      (#l:eloc)
      (#allow_reading:bool)
      (v: validate_with_action_t p inv l allow_reading)
: Tot (validate_with_action_t p inv l allow_reading)

inline_for_extraction noextract
val act_with_comment
      (s: string)
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#inv:slice_inv)
      (#l:eloc)
      (#b:_)
      (res:Type)
      (a: action p inv l b res)
: Tot (action p inv l b res)

inline_for_extraction noextract
val leaf_reader
      (#nz:bool)
      (#k: parser_kind nz WeakKindStrongPrefix)
      (#t: Type)
      (p: parser k t)
 : Type u#0

inline_for_extraction noextract
val validate_with_success_action
      (name: string)
      (#nz:bool)
      (#wk: _)
      (#k1:parser_kind nz wk)
      (#t1:Type)
      (#p1:parser k1 t1)
      (#inv1:_)
      (#l1:eloc)
      (#allow_reading:bool)
      (v1:validate_with_action_t p1 inv1 l1 allow_reading)
      (#inv2:_)
      (#l2:eloc)
      (#b:bool)
      (a:action p1 inv2 l2 b bool)
  : validate_with_action_t p1 (conj_inv inv1 inv2) (l1 `eloc_union` l2) false

inline_for_extraction noextract
val validate_with_error_action
      (name: string)
      (#nz:bool)
      (#wk: _)
      (#k1:parser_kind nz wk)
      (#t1:Type)
      (#p1:parser k1 t1)
      (#inv1:_)
      (#l1:eloc)
      (#allow_reading:bool)
      (v1:validate_with_action_t p1 inv1 l1 allow_reading)
      (#inv2:_)
      (#l2:eloc)
      (a:action p1 inv2 l2 false bool)
  : validate_with_action_t p1 (conj_inv inv1 inv2) (l1 `eloc_union` l2) false

inline_for_extraction noextract
val validate_ret
  : validate_with_action_t (parse_ret ()) true_inv eloc_none true

inline_for_extraction noextract
val validate_pair
       (name1: string)
       (#nz1:_) (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1:_) (#p1:parser k1 t1)
       (#inv1:_) (#l1:eloc) (#allow_reading1:bool) (v1:validate_with_action_t p1 inv1 l1 allow_reading1)
       (#nz2:_) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2:_) (#p2:parser k2 t2)
       (#inv2:_) (#l2:eloc) (#allow_reading2:bool) (v2:validate_with_action_t p2 inv2 l2 allow_reading2)
  : validate_with_action_t (p1 `parse_pair` p2) (conj_inv inv1 inv2) (l1 `eloc_union` l2) false

inline_for_extraction noextract
val validate_dep_pair
      (name1: string)
      (#nz1:_) (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1:_) (#p1:parser k1 t1)
      (#inv1:_) (#l1:_) (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (#nz2:_) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2:t1 -> Type) (#p2:(x:t1 -> parser k2 (t2 x)))
      (#inv2:_) (#l2:_) (#allow_reading2:bool) (v2:(x:t1 -> validate_with_action_t (p2 x) inv2 l2 allow_reading2))
  : validate_with_action_t (p1 `parse_dep_pair` p2) (conj_inv inv1 inv2) (l1 `eloc_union` l2) false

inline_for_extraction noextract
val validate_dep_pair_with_refinement_and_action
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (id1: field_id)
      (#nz1:_) (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1:_) (#p1:parser k1 t1)
      (#inv1:_) (#l1:_) (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      (#inv1':_) (#l1':_) (#b:_) (a:t1 -> action p1 inv1' l1' b bool)
      (#nz2:_) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      (#inv2:_) (#l2:_) (#allow_reading2:bool) (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 allow_reading2))
  : validate_with_action_t ((p1 `parse_filter` f) `parse_dep_pair` p2)
                           (conj_inv inv1 (conj_inv inv1' inv2))
                           (l1 `eloc_union` (l1' `eloc_union` l2))
                           false

inline_for_extraction noextract
val validate_dep_pair_with_action
      (#nz1:_) (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1:_) (#p1:parser k1 t1)
      (#inv1:_) (#l1:_) (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (#inv1':_) (#l1':_) (#b:_) (a:t1 -> action p1 inv1' l1' b bool)
      (#nz2:_) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2:t1 -> Type) (#p2:(x:t1 -> parser k2 (t2 x)))
      (#inv2:_) (#l2:_) (#allow_reading2:_) (v2:(x:t1 -> validate_with_action_t (p2 x) inv2 l2 allow_reading2))
  : validate_with_action_t
             (p1 `(parse_dep_pair #nz1)` p2)
             (conj_inv inv1 (conj_inv inv1' inv2))
             (l1 `eloc_union` (l1' `eloc_union` l2))
             false

inline_for_extraction noextract
val validate_dep_pair_with_refinement
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (id1: field_id)
      (#nz1:_) (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1:_) (#p1:parser k1 t1)
      (#inv1:_) (#l1:_) (v1:validate_with_action_t p1 inv1 l1 true) (r1: leaf_reader p1)
      (f: t1 -> bool)
      (#nz2:_) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2:refine _ f -> Type) (#p2:(x:refine _ f -> parser k2 (t2 x)))
      (#inv2:_) (#l2:_) (#allow_reading2:bool) (v2:(x:refine _ f -> validate_with_action_t (p2 x) inv2 l2 allow_reading2))
  : validate_with_action_t ((p1 `parse_filter` f) `parse_dep_pair` p2)
                           (conj_inv inv1 inv2)
                           (l1 `eloc_union` l2)
                           false

inline_for_extraction noextract
val validate_filter (name: string) (#nz:_) (#k:parser_kind nz WeakKindStrongPrefix) (#t:_) (#p:parser k t)
                    (#inv:_) (#l:_) (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
  : validate_with_action_t (p `parse_filter` f) inv l false

inline_for_extraction noextract
val validate_filter_with_action
                    (name: string) (#nz:_) (#k:parser_kind nz WeakKindStrongPrefix) (#t:_) (#p:parser k t)
                    (#inv:_) (#l:_) (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p) (f:t -> bool) (cr:string) (cf:string)
                    (#b:bool) (#inva:_) (#la:eloc) (a: t -> action (p `parse_filter` f) inva la b bool)
  : validate_with_action_t #nz (p `parse_filter` f) (conj_inv inv inva) (eloc_union l la) false

inline_for_extraction noextract
val validate_with_dep_action
                    (name: string) (#nz:_) (#k:parser_kind nz WeakKindStrongPrefix) (#t:_) (#p:parser k t)
                    (#inv:_) (#l:_) (v:validate_with_action_t p inv l true)
                    (r:leaf_reader p)
                    (#b:bool) (#inva:_) (#la:eloc) (a: t -> action p inva la b bool)
  : validate_with_action_t #nz p (conj_inv inv inva) (eloc_union l la) false

inline_for_extraction noextract
val validate_weaken_left (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
                         (#inv:_) (#l:_) (#allow_reading:bool) (v:validate_with_action_t p inv l allow_reading)
                         (#nz':_) (#wk': _) (k':parser_kind nz' wk')
  : validate_with_action_t (parse_weaken_left p k') inv l allow_reading

inline_for_extraction noextract
val validate_weaken_right (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
                         (#inv:_) (#l:_) (#allow_reading:bool) (v:validate_with_action_t p inv l allow_reading)
                         (#nz':_) (#wk': _) (k':parser_kind nz' wk')
  : validate_with_action_t (parse_weaken_right p k') inv l allow_reading

inline_for_extraction noextract
val validate_impos (_:unit)
  : validate_with_action_t (parse_impos ()) true_inv eloc_none true

inline_for_extraction noextract
val validate_with_error (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
                        (#inv:_) (#l:_) (#allow_reading:bool) (c:field_id) (v:validate_with_action_t p inv l allow_reading)
  : validate_with_action_t p inv l allow_reading

noextract inline_for_extraction
val validate_ite (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#a:Type) (#b:Type)
                 (#inv1:_) (#l1:_) (#ar1:_)
                 (#inv2:_) (#l2:_) (#ar2:_)
                 (e:bool)
                 (p1:squash e -> parser k a) (v1:(squash e -> validate_with_action_t (p1()) inv1 l1 ar1))
                 (p2:squash (not e) -> parser k b) (v2:(squash (not e) -> validate_with_action_t (p2()) inv2 l2 ar2))
  : validate_with_action_t (parse_ite e p1 p2) (conj_inv inv1 inv2) (l1 `eloc_union` l2) false

noextract inline_for_extraction
val validate_nlist
  (n:U32.t)
  (#wk: _)
  (#k:parser_kind true wk)
  (#t:_)
  (#p:parser k t)
  (#inv:_) (#l:_) (#allow_reading:bool)
  (v: validate_with_action_t p inv l allow_reading)
: validate_with_action_t (parse_nlist n p) inv l false

noextract inline_for_extraction
val validate_nlist_constant_size_without_actions
  (n_is_const: bool)
  (n:U32.t)
  (#wk: _)
  (#k:parser_kind true wk)
  (#t:_)
  (#p:parser k t)
  (#inv:_) (#l:_) (#allow_reading:bool)
  (v: validate_with_action_t p inv l allow_reading)
: Tot (validate_with_action_t (parse_nlist n p) inv l false)

noextract inline_for_extraction
val validate_t_at_most (n:U32.t) (#nz: _) (#wk: _) (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
                       (#inv:_) (#l:_) (#ar:_) (v:validate_with_action_t p inv l ar)
  : Tot (validate_with_action_t (parse_t_at_most n p) inv l false)

noextract inline_for_extraction
val validate_t_exact (n:U32.t) (#nz:bool) (#wk: _) (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
                     (#inv:_) (#l:_) (#ar:_) (v:validate_with_action_t p inv l ar)
  : Tot (validate_with_action_t (parse_t_exact n p) inv l false)

inline_for_extraction noextract
val validate_with_comment (c:string)
                          (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
                          (#inv:_) (#l:_) (#allow_reading:bool) (v:validate_with_action_t p inv l allow_reading)
  : validate_with_action_t p inv l allow_reading

inline_for_extraction noextract
val validate_weaken_inv_loc (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:_) (#p:parser k t)
                            (#inv:_) (#l:eloc) (#allow_reading:bool)
                            (inv':slice_inv{inv' `inv_implies` inv}) (l':eloc{l' `eloc_includes` l})
                            (v:validate_with_action_t p inv l allow_reading)
  : Tot (validate_with_action_t p inv' l' allow_reading)

inline_for_extraction noextract
val read_filter (#nz:_)
                (#k: parser_kind nz WeakKindStrongPrefix)
                (#t: Type)
                (#p: parser k t)
                (p32: leaf_reader p)
                (f: (t -> bool))
    : leaf_reader (parse_filter p f)

inline_for_extraction
let validator #nz #wk (#k:parser_kind nz wk) (#t:Type) (p:parser k t)
  = validate_with_action_t p true_inv eloc_none true

inline_for_extraction noextract
val validate____UINT8
  : validator parse____UINT8

inline_for_extraction noextract
val read____UINT8
  : leaf_reader parse____UINT8

inline_for_extraction noextract
val validate____UINT16BE
  : validator parse____UINT16BE

inline_for_extraction noextract
val read____UINT16BE
  : leaf_reader parse____UINT16BE

inline_for_extraction noextract
val validate____UINT32BE
  : validator parse____UINT32BE

inline_for_extraction noextract
val read____UINT32BE
  : leaf_reader parse____UINT32BE

inline_for_extraction noextract
val validate____UINT64BE
  : validator parse____UINT64BE

inline_for_extraction noextract
val read____UINT64BE
  : leaf_reader parse____UINT64BE

inline_for_extraction noextract
val validate____UINT16
  : validator parse____UINT16

inline_for_extraction noextract
val read____UINT16
  : leaf_reader parse____UINT16

inline_for_extraction noextract
val validate____UINT32
  : validator parse____UINT32

inline_for_extraction noextract
val read____UINT32
  : leaf_reader parse____UINT32

inline_for_extraction noextract
val validate____UINT64
  : validator parse____UINT64

inline_for_extraction noextract
val read____UINT64
  : leaf_reader parse____UINT64

inline_for_extraction noextract
val validate_unit
  : validator parse_unit

inline_for_extraction noextract
val read_unit
  : leaf_reader (parse_ret ())

inline_for_extraction noextract
val validate_unit_refinement (f:unit -> bool) (cf:string)
  : validator (parse_unit `parse_filter` f)

inline_for_extraction noextract
val validate_string
  (#k: parser_kind true WeakKindStrongPrefix)
  (#t: eqtype)
  (#p: parser k t)
  (v: validator p)
  (r: leaf_reader p)
  (terminator: t)
: Tot (validate_with_action_t (parse_string p terminator) true_inv eloc_none false)

inline_for_extraction noextract
val validate_all_bytes
: validate_with_action_t parse_all_bytes true_inv eloc_none false // could be true

inline_for_extraction noextract
val validate_all_zeros
: validate_with_action_t parse_all_zeros true_inv eloc_none false

////////////////////////////////////////////////////////////////////////////////

noextract
inline_for_extraction
val action_return
      (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#a:Type) (x:a)
  : action p true_inv eloc_none false a

noextract
inline_for_extraction
val action_bind
      (name: string)
      (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#invf:slice_inv) (#lf:eloc)
      (#bf:_) (#a:Type) (f: action p invf lf bf a)
      (#invg:slice_inv) (#lg:eloc) (#bg:_)
      (#b:Type) (g: (a -> action p invg lg bg b))
  : Tot (action p (conj_inv invf invg) (eloc_union lf lg) (bf || bg) b)

noextract
inline_for_extraction
val action_seq
      (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#invf:slice_inv) (#lf:eloc)
      (#bf:_) (#a:Type) (f: action p invf lf bf a)
      (#invg:slice_inv) (#lg:eloc) (#bg:_)
      (#b:Type) (g: action p invg lg bg b)
  : Tot (action p (conj_inv invf invg) (eloc_union lf lg) (bf || bg) b)

noextract
inline_for_extraction
val action_ite
      (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#invf:slice_inv) (#lf:eloc)
      (guard:bool)
      (#bf:_) (#a:Type) (then_: squash guard -> action p invf lf bf a)
      (#invg:slice_inv) (#lg:eloc) (#bg:_)
      (else_: squash (not guard) -> action p invg lg bg a)
  : action p (conj_inv invf invg) (eloc_union lf lg) (bf || bg) a

noextract
inline_for_extraction
val action_abort
      (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
  : action p true_inv eloc_none false bool

noextract
inline_for_extraction
val action_field_pos
      (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:Type) (#p:parser k t) (u:unit)
   : action p true_inv eloc_none false U32.t

noextract
inline_for_extraction
val action_deref
      (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#a:_) (x:B.pointer a)
   : action p (ptr_inv x) loc_none false a

noextract
inline_for_extraction
val action_assignment
      (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#a:_) (x:B.pointer a) (v:a)
   : action p (ptr_inv x) (ptr_loc x) false unit

noextract
inline_for_extraction
val action_weaken
      (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:Type) (#p:parser k t)
      (#inv:slice_inv) (#l:eloc) (#b:_) (#a:_) (act:action p inv l b a)
      (#inv':slice_inv{inv' `inv_implies` inv}) (#l':eloc{l' `eloc_includes` l})
   : action p inv' l' b a
