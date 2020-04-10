module LowParse.Spec.BitSum
include LowParse.Spec.Enum
include LowParse.BitFields

module L = FStar.List.Tot

noeq
type bitsum'
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
=
| BitStop of (squash (bitsum'_size == 0))
| BitField :
    (sz: nat { sz > 0 /\ sz <= bitsum'_size /\ bitsum'_size <= tot }) ->
    (rest: bitsum' cl (bitsum'_size - sz)) ->
    bitsum' cl bitsum'_size
| BitSum' :
    (key: eqtype) ->
    (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot }) -> // key_size made positive because F* cannot prove that (payload _) is a smaller term wrt. << without FStar.WellFounded.axiom1_dep
    (e: enum key (bitfield cl key_size)) ->
    (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size)))) ->
    bitsum' cl bitsum'_size

noextract
let rec bitsum'_type'
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
: Tot Type0
  (decreases (bitsum'_size))
= match b with
  | BitStop _ -> unit
  | BitField sz rest -> (bitfield cl sz & bitsum'_type' rest)
  | BitSum' key key_size e payload ->
    (key: enum_key e & bitsum'_type' (payload key))

noextract
let bitsum'_type
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
: Tot Type0
= bitsum'_type' b

inline_for_extraction
let bitsum'_type_bitfield
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (bitsum'_size: nat)
  (sz: nat { sz > 0 /\ sz <= bitsum'_size /\ bitsum'_size  <= tot })
  (rest: bitsum' cl (bitsum'_size - sz))
: Tot Type0
= bitfield cl sz & bitsum'_type rest

let bitsum'_type_bitsum'
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
: Tot Type0
= (k': enum_key e & bitsum'_type (payload k'))

noextract
noeq
type filter_bitsum'_t_attr =

[@filter_bitsum'_t_attr]
inline_for_extraction
let bitsum'_type_elim_BitSum'
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (x: bitsum'_type (BitSum' key key_size e payload))
: Tot (bitsum'_type_bitsum' cl bitsum'_size key key_size e payload)
= x

[@filter_bitsum'_t_attr]
inline_for_extraction
let bitsum'_type_intro_BitSum'
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (x: bitsum'_type_bitsum' cl bitsum'_size key key_size e payload)
: Tot (bitsum'_type (BitSum' key key_size e payload))
= x

[@filter_bitsum'_t_attr]
inline_for_extraction
let bitsum'_type_elim_BitField
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (sz: nat { sz > 0 /\ sz <= bitsum'_size /\ bitsum'_size <= tot })
  (rest: bitsum' cl (bitsum'_size - sz))
  (x: bitsum'_type (BitField sz rest))
: Tot (bitsum'_type_bitfield bitsum'_size sz rest)
= x

[@filter_bitsum'_t_attr]
inline_for_extraction
let bitsum'_type_intro_BitField
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (sz: nat { sz > 0 /\ sz <= bitsum'_size /\ bitsum'_size <= tot })
  (rest: bitsum' cl (bitsum'_size - sz))
  (x: bitsum'_type_bitfield bitsum'_size sz rest)
: Tot (bitsum'_type (BitField sz rest))
= x

noextract
let rec bitsum'_key_type
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
: Tot eqtype
  (decreases (bitsum'_size))
= match b with
  | BitStop _ -> unit
  | BitField sz rest -> bitsum'_key_type rest
  | BitSum' key key_size e payload ->
    (key: enum_key e & bitsum'_key_type (payload key))

[@filter_bitsum'_t_attr]
inline_for_extraction
let bitsum'_key_type_elim_BitSum'
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (x: bitsum'_key_type (BitSum' key key_size e payload))
: Tot (k': enum_key e & bitsum'_key_type (payload k'))
= x

[@filter_bitsum'_t_attr]
inline_for_extraction
let bitsum'_key_type_intro_BitSum'
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size)))) 
  (x: (k': enum_key e & bitsum'_key_type (payload k')))
: Tot (bitsum'_key_type (BitSum' key key_size e payload))
= x

[@filter_bitsum'_t_attr]
unfold
inline_for_extraction
let coerce
  (t2: Type)
  (#t1: Type)
  (x: t1)
: Pure t2
  (requires (t1 == t2))
  (ensures (fun _ -> True))
= (x <: t2)

[@filter_bitsum'_t_attr]
inline_for_extraction
let bitsum'_key_type_intro_BitField
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (sz: nat { sz > 0 /\ sz <= bitsum'_size /\ bitsum'_size <= tot })
  (rest: bitsum' cl (bitsum'_size - sz))
  (x: bitsum'_key_type rest)
: Tot (bitsum'_key_type (BitField sz rest))
= coerce (bitsum'_key_type (BitField sz rest)) x

[@filter_bitsum'_t_attr]
inline_for_extraction
let bitsum'_key_type_elim_BitField
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (sz: nat { sz > 0 /\ sz <= bitsum'_size /\ bitsum'_size <= tot })
  (rest: bitsum' cl (bitsum'_size - sz))
  (x: bitsum'_key_type (BitField sz rest))
: Tot (bitsum'_key_type rest)
= coerce (bitsum'_key_type rest) x

let rec filter_bitsum'
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
  (x: t)
: Tot bool
  (decreases (bitsum'_size))
= match b with
  | BitStop _ -> true
  | BitField _ rest -> filter_bitsum' rest x
  | BitSum' key key_size e payload ->
    let f : bitfield cl key_size = cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size in
    if list_mem f (list_map snd e)
    then
      let k = enum_key_of_repr e f in
      filter_bitsum' (payload k) x
    else
      false

let rec synth_bitsum'
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
  (x: parse_filter_refine (filter_bitsum' b))
: Tot (bitsum'_type b)
  (decreases (bitsum'_size))
= match b with
  | BitStop _ -> ()
  | BitField sz rest ->
    bitsum'_type_intro_BitField cl bitsum'_size sz rest (cl.get_bitfield x (bitsum'_size - sz) bitsum'_size, synth_bitsum' rest x)
  | BitSum' key key_size e payload ->
    let f : bitfield cl key_size = cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size in
    let k : enum_key e = enum_key_of_repr e f in
    let z : bitsum'_type (payload k) = synth_bitsum' (payload k) x in
    let p : (k' : enum_key e & bitsum'_type (payload k')) = (| k, z |) in
    bitsum'_type_intro_BitSum' cl bitsum'_size key key_size e payload p
  
module BF = LowParse.BitFields

#push-options "--z3rlimit 16"

let rec synth_bitsum'_injective'
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
  (x y: parse_filter_refine (filter_bitsum' b))
: Lemma
  (requires (synth_bitsum' b x == synth_bitsum' b y))
  (ensures (cl.get_bitfield x 0 bitsum'_size == cl.get_bitfield y 0 bitsum'_size))
  (decreases (bitsum'_size))
= match b with
  | BitStop h ->
    BF.get_bitfield_empty (cl.v x) 0;
    BF.get_bitfield_empty (cl.v y) 0;
    assert (cl.uint_to_t (cl.v (cl.get_bitfield x 0 bitsum'_size)) == cl.uint_to_t (cl.v (cl.get_bitfield y 0 bitsum'_size)))
  | BitField sz rest ->
    assert (cl.v (cl.get_bitfield x (bitsum'_size - sz) (bitsum'_size)) == cl.v (cl.get_bitfield y (bitsum'_size - sz) (bitsum'_size)));
    synth_bitsum'_injective' rest x y;
    assert (cl.v (cl.get_bitfield x 0 (bitsum'_size - sz)) == cl.v (cl.get_bitfield y 0 (bitsum'_size - sz)));
    BF.get_bitfield_partition (cl.v x) (cl.v y) 0 bitsum'_size [bitsum'_size - sz];
    assert (cl.uint_to_t (cl.v (cl.get_bitfield x 0 bitsum'_size)) == cl.uint_to_t (cl.v (cl.get_bitfield y 0 bitsum'_size)))
  | BitSum' key key_size e payload ->
    let f : bitfield cl key_size = cl.get_bitfield x (bitsum'_size - key_size) (bitsum'_size) in
    let g : bitfield cl key_size = cl.get_bitfield y (bitsum'_size - key_size) (bitsum'_size) in
    let k = enum_key_of_repr e f in
    enum_repr_of_key_of_repr e f;
    enum_repr_of_key_of_repr e g;
    assert (cl.v f == cl.v g);
    synth_bitsum'_injective' (payload k) x y;
    BF.get_bitfield_partition (cl.v x) (cl.v y) 0 bitsum'_size [bitsum'_size - key_size];
    assert (cl.uint_to_t (cl.v (cl.get_bitfield x 0 bitsum'_size)) == cl.uint_to_t (cl.v (cl.get_bitfield y 0 bitsum'_size)))

#pop-options

let synth_bitsum'_injective
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
: Lemma
  (synth_injective (synth_bitsum' b))
//  [SMTPat (synth_injective (synth_bitsum' b))]
= synth_injective_intro' (synth_bitsum' b) (fun x y ->
    synth_bitsum'_injective' b x y;
    BF.get_bitfield_full (cl.v x);
    BF.get_bitfield_full (cl.v y);
    assert (cl.uint_to_t (cl.v x) == cl.uint_to_t (cl.v y))
  )

// #push-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false"

#push-options "--z3rlimit 64"

let rec synth_bitsum'_ext
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
  (x y: parse_filter_refine (filter_bitsum' b))
: Lemma
  (requires (BF.get_bitfield (cl.v x) 0 bitsum'_size == BF.get_bitfield (cl.v y) 0 bitsum'_size))
  (ensures (synth_bitsum' b x == synth_bitsum' b y))
  (decreases (bitsum'_size))
= match b with
  | BitStop _ -> ()
  | BitField sz rest ->
    let f : bitfield cl sz = cl.get_bitfield x (bitsum'_size - sz) (bitsum'_size) in
    let g : bitfield cl sz = cl.get_bitfield y (bitsum'_size - sz) (bitsum'_size) in
    BF.get_bitfield_get_bitfield (cl.v x) 0 bitsum'_size (bitsum'_size - sz) bitsum'_size;
    BF.get_bitfield_get_bitfield (cl.v y) 0 bitsum'_size (bitsum'_size - sz) bitsum'_size;
    assert (cl.uint_to_t (cl.v f) == cl.uint_to_t (cl.v g));
    assert (f == g);
    BF.get_bitfield_get_bitfield (cl.v x) 0 bitsum'_size 0 (bitsum'_size - sz);
    BF.get_bitfield_get_bitfield (cl.v y) 0 bitsum'_size 0 (bitsum'_size - sz);
    synth_bitsum'_ext rest x y
  | BitSum' key key_size e payload ->
    let f : bitfield cl key_size = cl.get_bitfield x (bitsum'_size - key_size) (bitsum'_size) in
    let g : bitfield cl key_size = cl.get_bitfield y (bitsum'_size - key_size) (bitsum'_size) in
    BF.get_bitfield_get_bitfield (cl.v x) 0 bitsum'_size (bitsum'_size - key_size) bitsum'_size;
    BF.get_bitfield_get_bitfield (cl.v y) 0 bitsum'_size (bitsum'_size - key_size) bitsum'_size;
    assert (cl.uint_to_t (cl.v f) == cl.uint_to_t (cl.v g));
    assert (f == g);
    let k = enum_key_of_repr e f in
    let u = synth_bitsum' (payload k) x in
    let v = synth_bitsum' (payload k) y in
    assert (synth_bitsum' (BitSum' key key_size e payload) x == bitsum'_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, u |));
    assert (synth_bitsum' (BitSum' key key_size e payload) y == bitsum'_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, v |));
    BF.get_bitfield_get_bitfield (cl.v x) 0 bitsum'_size 0 (bitsum'_size - key_size);
    assert (BF.get_bitfield (cl.v x) 0 (bitsum'_size - key_size) == BF.get_bitfield (BF.get_bitfield (cl.v x) 0 bitsum'_size) (0) (bitsum'_size - key_size));
    BF.get_bitfield_get_bitfield (cl.v y) 0 bitsum'_size 0 (bitsum'_size - key_size);
    assert (BF.get_bitfield (cl.v y) 0 (bitsum'_size - key_size) == BF.get_bitfield (BF.get_bitfield (cl.v y) 0 bitsum'_size) (0) (bitsum'_size - key_size));
    synth_bitsum'_ext (payload k) x y;
    assert (u == v)

#pop-options

let parse_bitsum'
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#k: parser_kind)
  (p: parser k t)
: Tot (parser (parse_filter_kind k) (bitsum'_type b))
= synth_bitsum'_injective b;
  (p `parse_filter` filter_bitsum' b) `parse_synth` synth_bitsum' b

let rec synth_bitsum'_recip'
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
  (x: bitsum'_type b)
: Tot t
  (decreases (bitsum'_size))
= match b with
  | BitStop _ -> cl.uint_to_t 0
  | BitField sz rest ->
    let (hd, tl) = bitsum'_type_elim_BitField cl bitsum'_size sz rest x in
    cl.set_bitfield (synth_bitsum'_recip' rest tl) (bitsum'_size - sz) (bitsum'_size) hd
  | BitSum' key key_size e payload ->
    let (| k, tl |) = bitsum'_type_elim_BitSum' cl bitsum'_size key key_size e payload x in
    let y1 = synth_bitsum'_recip' (payload k) tl in
    let y2 = cl.set_bitfield y1 (bitsum'_size - key_size) bitsum'_size (enum_repr_of_key e k) in
    y2

#push-options "--z3rlimit 16"

let rec get_bitfield_synth_bitsum'_recip'_other
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
  (x: bitsum'_type b)
  (lo: nat)
  (hi: nat { bitsum'_size <= lo /\ lo <= hi /\ hi <= tot })
: Lemma
  (ensures (cl.v (cl.get_bitfield (synth_bitsum'_recip' b x) lo hi) == 0))
  (decreases (bitsum'_size))
= match b with
  | BitStop h ->
    BF.get_bitfield_zero tot lo hi
  | BitField sz rest ->
    let (hd, tl) = bitsum'_type_elim_BitField cl bitsum'_size sz rest x in
    BF.get_bitfield_set_bitfield_other (cl.v (synth_bitsum'_recip' rest tl)) (bitsum'_size - sz) bitsum'_size (cl.v hd) lo hi;
    get_bitfield_synth_bitsum'_recip'_other rest tl lo hi
  | BitSum' key key_size e payload ->
    let (| k, tl |) = bitsum'_type_elim_BitSum' cl bitsum'_size key key_size e payload x in
    BF.get_bitfield_set_bitfield_other (cl.v (synth_bitsum'_recip' (payload k) tl)) (bitsum'_size - key_size) bitsum'_size (cl.v (enum_repr_of_key e k)) lo hi;
    get_bitfield_synth_bitsum'_recip'_other (payload k) tl lo hi

#pop-options

#push-options "--z3rlimit 64"

let rec filter_bitsum'_ext
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
  (x y: t)
: Lemma
  (requires (BF.get_bitfield (cl.v x) 0 bitsum'_size == BF.get_bitfield (cl.v y) 0 bitsum'_size))
  (ensures (filter_bitsum' b x == filter_bitsum' b y))
  (decreases (bitsum'_size))
= match b with
  | BitStop _ -> ()
  | BitField sz rest ->
    BF.get_bitfield_get_bitfield (cl.v x) 0 bitsum'_size 0 (bitsum'_size - sz);
    BF.get_bitfield_get_bitfield (cl.v y) 0 bitsum'_size 0 (bitsum'_size - sz);
    filter_bitsum'_ext rest x y
  | BitSum' key key_size e payload ->
    let f : bitfield cl key_size = cl.get_bitfield x (bitsum'_size - key_size) (bitsum'_size) in
    let g : bitfield cl key_size = cl.get_bitfield y (bitsum'_size - key_size) (bitsum'_size) in
    BF.get_bitfield_get_bitfield (cl.v x) 0 bitsum'_size (bitsum'_size - key_size) bitsum'_size;
    BF.get_bitfield_get_bitfield (cl.v y) 0 bitsum'_size (bitsum'_size - key_size) bitsum'_size;
    assert (BF.get_bitfield (cl.v x) (bitsum'_size - key_size) (bitsum'_size) == BF.get_bitfield (cl.v y) (bitsum'_size - key_size) (bitsum'_size));
    assert (cl.v f == BF.get_bitfield (cl.v x) (bitsum'_size - key_size) (bitsum'_size));
    assert (cl.v g == BF.get_bitfield (cl.v y) (bitsum'_size - key_size) (bitsum'_size));
    assert (cl.uint_to_t (cl.v f) == cl.uint_to_t (cl.v g));
    assert (f == g);
    if list_mem f (list_map snd e)
    then begin
      let k = enum_key_of_repr e f in
      BF.get_bitfield_get_bitfield (cl.v x) 0 bitsum'_size 0 (bitsum'_size - key_size);
      BF.get_bitfield_get_bitfield (cl.v y) 0 bitsum'_size 0 (bitsum'_size - key_size);
      filter_bitsum'_ext (payload k) x y
    end else ()

#pop-options

let rec synth_bitsum'_recip'_prop
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
  (x: bitsum'_type b)
: Lemma
  (ensures (filter_bitsum' b (synth_bitsum'_recip' b x) == true))
  (decreases (bitsum'_size))
= match b with
  | BitStop _ -> ()
  | BitField sz rest ->
    let (hd, tl) = bitsum'_type_elim_BitField cl bitsum'_size sz rest x in
    BF.get_bitfield_set_bitfield_other (cl.v (synth_bitsum'_recip' rest tl)) (bitsum'_size - sz) (bitsum'_size) (cl.v hd) 0 (bitsum'_size - sz);
    filter_bitsum'_ext rest (synth_bitsum'_recip' b x) (synth_bitsum'_recip' rest tl);
    synth_bitsum'_recip'_prop rest tl
  | BitSum' key key_size e payload ->
    let (| k, tl |) = bitsum'_type_elim_BitSum' cl bitsum'_size key key_size e payload x in
    BF.get_bitfield_set_bitfield_same (cl.v (synth_bitsum'_recip' (payload k) tl)) (bitsum'_size - key_size) (bitsum'_size) (cl.v (enum_repr_of_key e k));
    BF.get_bitfield_set_bitfield_other (cl.v (synth_bitsum'_recip' (payload k) tl)) (bitsum'_size - key_size) (bitsum'_size) (cl.v (enum_repr_of_key e k)) 0 (bitsum'_size - key_size);
    assert (cl.uint_to_t (cl.v (cl.get_bitfield (synth_bitsum'_recip' b x) (bitsum'_size - key_size) (bitsum'_size))) == cl.uint_to_t (cl.v (enum_repr_of_key e k <: t)));
    enum_key_of_repr_of_key e k;
    filter_bitsum'_ext (payload k) (synth_bitsum'_recip' b x) (synth_bitsum'_recip' (payload k) tl);
    synth_bitsum'_recip'_prop (payload k) tl

inline_for_extraction
let synth_bitsum'_recip
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
  (x: bitsum'_type b)
: Tot (parse_filter_refine (filter_bitsum' b))
= synth_bitsum'_recip'_prop b x;
  synth_bitsum'_recip' b x

#push-options "--z3rlimit 16"

let rec synth_bitsum'_recip_inverse'
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
  (x: bitsum'_type b)
: Lemma
  (ensures (synth_bitsum' b (synth_bitsum'_recip b x) == x))
  (decreases bitsum'_size)
= match b with
  | BitStop _ -> ()
  | BitField sz rest ->
    let (hd, tl) = bitsum'_type_elim_BitField cl bitsum'_size sz rest x in
    let y = synth_bitsum'_recip b x in
    let y1 = synth_bitsum'_recip rest tl in
    (* Part 1/2: synth_bitfield cl 0 header_size header y == hd *)
    BF.get_bitfield_set_bitfield_same (cl.v y1) (bitsum'_size - sz) (bitsum'_size) (cl.v hd);
    assert (cl.uint_to_t (cl.v (cl.get_bitfield y (bitsum'_size - sz) (bitsum'_size))) == cl.uint_to_t (cl.v hd));
    (* Part 2/2: synth_bitfield cl (header_size + key_size) tot (payload k) y == tl *)
    BF.get_bitfield_set_bitfield_other (cl.v y1) (bitsum'_size - sz) (bitsum'_size) (cl.v hd) 0 (bitsum'_size - sz);
    filter_bitsum'_ext rest y y1;
    synth_bitsum'_ext rest y y1 ;
    synth_bitsum'_recip_inverse' rest tl
  | BitSum' key key_size e payload ->
    let (| k, tl |) = bitsum'_type_elim_BitSum' cl bitsum'_size key key_size e payload x in
    let y = synth_bitsum'_recip b x in
    let y1 = synth_bitsum'_recip (payload k) tl in
    (* Part 1/2: k == enum_key_of_repr e f *)
    BF.get_bitfield_set_bitfield_same (cl.v y1) (bitsum'_size - key_size) (bitsum'_size) (cl.v (enum_repr_of_key e k));
    assert (cl.uint_to_t (cl.v (cl.get_bitfield y (bitsum'_size - key_size) bitsum'_size)) == cl.uint_to_t (cl.v (enum_repr_of_key e k)));
    enum_key_of_repr_of_key e k;
    (* Part 2/2: synth_bitfield cl (header_size + key_size) tot (payload k) y == tl *)
    BF.get_bitfield_set_bitfield_other (cl.v y1) (bitsum'_size - key_size) bitsum'_size (cl.v (enum_repr_of_key e k)) 0 (bitsum'_size - key_size);
    filter_bitsum'_ext (payload k) y y1;
    synth_bitsum'_ext (payload k) y y1 ;
    synth_bitsum'_recip_inverse' (payload k) tl

#pop-options

let synth_bitsum'_recip_inverse
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
: Lemma
  (synth_inverse (synth_bitsum' b) (synth_bitsum'_recip b))
//  [SMTPat (synth_inverse (synth_bitsum' b) (synth_bitsum'_recip b))]
= synth_inverse_intro' (synth_bitsum' b) (synth_bitsum'_recip b) (fun x ->
    synth_bitsum'_recip_inverse' b x
  )

let serialize_bitsum'
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
: Tot (serializer (parse_bitsum' b p))
= synth_bitsum'_injective b;
  synth_bitsum'_recip_inverse b;
  serialize_synth
    (p `parse_filter` filter_bitsum' b)
    (synth_bitsum' b)
    (s `serialize_filter` filter_bitsum' b)
    (synth_bitsum'_recip b)
    ()

let serialize_bitsum'_eq
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (x: bitsum'_type b)
: Lemma
  (serialize (serialize_bitsum' b s) x == serialize s (synth_bitsum'_recip b x))
= synth_bitsum'_injective b;
  synth_bitsum'_recip_inverse b;
  serialize_synth_eq
    (p `parse_filter` filter_bitsum' b)
    (synth_bitsum' b)
    (s `serialize_filter` filter_bitsum' b)
    (synth_bitsum'_recip b)
    ()
    x

let rec bitsum'_key_of_t
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
  (x: bitsum'_type b)
: Tot (bitsum'_key_type b)
  (decreases (bitsum'_size))
= match b with
  | BitStop _ -> ()
  | BitField sz rest ->
    begin match bitsum'_type_elim_BitField cl bitsum'_size sz rest x with
    | (_, tl) ->
      bitsum'_key_type_intro_BitField cl bitsum'_size sz rest (bitsum'_key_of_t rest tl)
    end
  | BitSum' key key_size e payload ->
    begin match bitsum'_type_elim_BitSum' cl bitsum'_size key key_size e payload x with
    | (| k, pl |) ->
      bitsum'_key_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, bitsum'_key_of_t (payload k) pl |)
    end

inline_for_extraction
noextract
let id
  (#t: Type)
  (x: t)
: Tot t
= x

inline_for_extraction
noextract
noeq
type synth_case_t
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (data: Type0)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
: Type0
= | SynthCase:
    (f: (
      (k' : bitsum'_type b) ->
      type_of_tag (bitsum'_key_of_t b k') ->
      Tot (refine_with_tag (tag_of_data) k')
    )) ->
    (f_inj: (
      (k' : bitsum'_type b) ->
      (pl1: type_of_tag (bitsum'_key_of_t b k')) ->
      (pl2: type_of_tag (bitsum'_key_of_t b k')) ->
      Lemma
      (requires (f k' pl1 == f k' pl2))
      (ensures (pl1 == pl2))
    )) ->
    (g: (
      (k' : bitsum'_type b) ->
      refine_with_tag (tag_of_data) k' ->
      Tot (type_of_tag (bitsum'_key_of_t b k'))
    )) ->
    (f_g_eq: (
      (k: bitsum'_type b) ->
      (x: refine_with_tag (tag_of_data) k) ->
      Lemma
      (f k (g k x) == x)
    ))
    -> synth_case_t b data tag_of_data type_of_tag

let synth_case_g_f_eq
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#b: bitsum' cl tot)
  (#data: Type0)
  (#tag_of_data: (data -> Tot (bitsum'_type b)))
  (#type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (s: synth_case_t b data tag_of_data type_of_tag)
  (k: bitsum'_type b)
  (x: type_of_tag (bitsum'_key_of_t b k))
: Lemma
  (s.g k (s.f k x) == x)
= s.f_g_eq k (s.f k x);
  s.f_inj k (s.g k (s.f k x)) x

#push-options "--z3rlimit 16 --max_ifuel 3 --initial_ifuel 3"

let rec weaken_parse_bitsum_cases_kind'
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
  (f: (x: bitsum'_key_type b) -> Tot parser_kind)
: Tot (k' : parser_kind & ((x: bitsum'_key_type b) -> Lemma (k' `is_weaker_than` f x)))
  (decreases (bitsum'_size))
= match b with
  | BitStop _ -> (| f (), (fun y -> ()) |)
  | BitField sz rest ->
    let (| g, phi |) = weaken_parse_bitsum_cases_kind' rest (fun x -> f (bitsum'_key_type_intro_BitField cl bitsum'_size sz rest x)) in
    (| g, (fun x -> phi (bitsum'_key_type_elim_BitField cl bitsum'_size sz rest x)) |)
  | BitSum' key key_size e payload ->
    let keys : list key = List.Tot.map fst e in
    let phi (x: key) : Tot (k: parser_kind & ((y: bitsum'_key_type b) -> Lemma
      (requires (dfst (bitsum'_key_type_elim_BitSum' cl bitsum'_size key key_size e payload y) == x))
      (ensures (k `is_weaker_than` f y)))) =
      if List.Tot.mem x keys
      then
        let (| k, g |) = weaken_parse_bitsum_cases_kind' (payload x) (fun z -> f (bitsum'_key_type_intro_BitSum' cl bitsum'_size key key_size e payload (| x, z |))) in
        (| k, (fun y ->
          let (| y1, y2 |) = bitsum'_key_type_elim_BitSum' cl bitsum'_size key key_size e payload y in
          assert (y1 == x);
          g y2
        ) |)
      else (| default_parser_kind, (fun y -> ()) |)
    in
    let k = glb_list_of #key (fun x -> dfst (phi x)) keys in
    (| k, (fun y ->
      let (| y1, y2 |) = bitsum'_key_type_elim_BitSum' cl bitsum'_size key key_size e payload y in
      dsnd (phi y1) y
    ) |)

let weaken_parse_bitsum_cases_kind
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
: Tot (k: parser_kind { forall (x: bitsum'_key_type b) . k `is_weaker_than` dfst (f x) })
= let (| k, phi |) = weaken_parse_bitsum_cases_kind' b (fun k -> dfst (f k)) in
  Classical.forall_intro phi;
  k

let synth_bitsum_case_injective
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type0)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (x: bitsum'_type b)
: Lemma
  (synth_injective (synth_case.f x))
  [SMTPat (synth_injective (synth_case.f x))]
= synth_injective_intro' (synth_case.f x) (fun y z ->
    synth_case.f_inj x y z
  )

let parse_bitsum_cases
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type0)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (x: bitsum'_type b)
: Tot (parser (weaken_parse_bitsum_cases_kind b type_of_tag f) (refine_with_tag (tag_of_data) x))
= let tg : bitsum'_key_type b = bitsum'_key_of_t b x in
  let (| k_, p |) = f tg in
  weaken (weaken_parse_bitsum_cases_kind b type_of_tag f) (p `parse_synth` synth_case.f x)

inline_for_extraction
let parse_bitsum_kind
  (kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
: Tot parser_kind
= and_then_kind (parse_filter_kind kt) (weaken_parse_bitsum_cases_kind b type_of_tag f)

let parse_bitsum
  (#kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type0)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (p: parser kt t)
  (f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
: Tot (parser (parse_bitsum_kind kt b type_of_tag f) data)
= parse_tagged_union
    #(parse_filter_kind kt)
    #(bitsum'_type b)
    (parse_bitsum' b p)
    #(data)
    (tag_of_data)
    #(weaken_parse_bitsum_cases_kind b type_of_tag f)
    (parse_bitsum_cases b tag_of_data type_of_tag synth_case f)

module Seq = FStar.Seq

#push-options "--z3rlimit 16"

let parse_bitsum_eq
  (#kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type0)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (p: parser kt t)
  (f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (x: bytes)
: Lemma
  (parse (parse_bitsum b tag_of_data type_of_tag synth_case p f) x == (match parse (parse_bitsum' b p) x with
  | None -> None
  | Some (tg, consumed1) ->
    let k = bitsum'_key_of_t b tg in
    begin match parse (dsnd (f k)) (Seq.slice x consumed1 (Seq.length x)) with
    | None -> None
    | Some (y, consumed2) ->
      Some ((synth_case.f tg y <: data), consumed1 + consumed2)
    end
  ))
= parse_tagged_union_eq
    #(parse_filter_kind kt)
    #(bitsum'_type b)
    (parse_bitsum' b p)
    #(data)
    (tag_of_data)
    #(weaken_parse_bitsum_cases_kind b type_of_tag f)
    (parse_bitsum_cases b tag_of_data type_of_tag synth_case f)
    x;
  match parse (parse_bitsum' b p) x with
  | None -> ()
  | Some (tg, consumed1) ->
    let k = bitsum'_key_of_t b tg in
    synth_bitsum_case_injective b tag_of_data type_of_tag synth_case tg;
    parse_synth_eq
      (dsnd (f k))
      (synth_case.f tg)
      (Seq.slice x consumed1 (Seq.length x))

#pop-options

let synth_bitsum_case_recip_inverse
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type0)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (x: bitsum'_type b)
: Lemma
  (synth_inverse (synth_case.f x) (synth_case.g x))
  [SMTPat (synth_inverse (synth_case.f x) (synth_case.g x))] // FIXME: does not trigger. WHY WHY WHY?
= synth_inverse_intro' (synth_case.f x) (synth_case.g x) (fun y ->
    synth_case.f_g_eq x y
  )

let serialize_bitsum_cases
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type0)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (#f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (g: (x: bitsum'_key_type b) -> Tot (serializer (dsnd (f x))))
  (x: bitsum'_type b)
: Tot (serializer (parse_bitsum_cases b tag_of_data type_of_tag synth_case f x))
= let tg = bitsum'_key_of_t b x in
  let (| _, p |) = f tg in
  synth_bitsum_case_injective b tag_of_data type_of_tag synth_case x; // FIXME: WHY WHY WHY does the pattern not trigger?
  synth_bitsum_case_recip_inverse b tag_of_data type_of_tag synth_case x; // FIXME: WHY WHY WHY does the pattern not trigger?
  serialize_weaken (weaken_parse_bitsum_cases_kind b type_of_tag f)
    (serialize_synth
      p
      (synth_case.f x)
      (g tg)
      (synth_case.g x)
      ())

let serialize_bitsum
  (#kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type0)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (#p: parser kt t)
  (s: serializer p { kt.parser_kind_subkind == Some ParserStrong } )
  (#f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (g: (x: bitsum'_key_type b) -> Tot (serializer (dsnd (f x))))
: Tot (serializer (parse_bitsum b tag_of_data type_of_tag synth_case p f))
= serialize_tagged_union
    #(parse_filter_kind kt)
    #(bitsum'_type b)
    #(parse_bitsum' b p)
    (serialize_bitsum' b s)
    #(data)
    (tag_of_data)
    #(weaken_parse_bitsum_cases_kind b type_of_tag f)
    #(parse_bitsum_cases b tag_of_data type_of_tag synth_case f)
    (serialize_bitsum_cases b tag_of_data type_of_tag synth_case #f g)

let serialize_bitsum_alt
  (#kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type0)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (#p: parser kt t)
  (s: serializer p { kt.parser_kind_subkind == Some ParserStrong } )
  (#f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (g: (x: bitsum'_key_type b) -> Tot (serializer (dsnd (f x))))
  (x: data)
: GTot bytes
= 
    let tg = tag_of_data x in
    let k = bitsum'_key_of_t b tg in
    let payload = synth_case.g tg x in
    serialize s (synth_bitsum'_recip b tg) `Seq.append` serialize (g k) payload

let serialize_bitsum_eq
  (#kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type0)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (#p: parser kt t)
  (s: serializer p { kt.parser_kind_subkind == Some ParserStrong } )
  (#f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (g: (x: bitsum'_key_type b) -> Tot (serializer (dsnd (f x))))
  (x: data)
: Lemma
  (serialize (serialize_bitsum b tag_of_data type_of_tag synth_case s g) x == serialize_bitsum_alt b tag_of_data type_of_tag synth_case s g x)
= serialize_tagged_union_eq
    #(parse_filter_kind kt)
    #(bitsum'_type b)
    #(parse_bitsum' b p)
    (serialize_bitsum' b s)
    #(data)
    (tag_of_data)
    #(weaken_parse_bitsum_cases_kind b type_of_tag f)
    #(parse_bitsum_cases b tag_of_data type_of_tag synth_case f)
    (serialize_bitsum_cases b tag_of_data type_of_tag synth_case #f g)
    x;
  let tg = tag_of_data x in
  let k = bitsum'_key_of_t b tg in
  serialize_bitsum'_eq b s tg;
  let (| _, p |) = f k in
  serialize_synth_eq
    #_
    #(type_of_tag k)
    p
    (synth_case.f tg)
    (g k)
    (synth_case.g tg)
    ()
    x

let serialize_bitsum_eq'
  (#kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type0)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (#p: parser kt t)
  (s: serializer p { kt.parser_kind_subkind == Some ParserStrong } )
  (#f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (g: (x: bitsum'_key_type b) -> Tot (serializer (dsnd (f x))))
  (x: data)
: Lemma
  (serialize_bitsum #kt #tot #t #cl b #data tag_of_data type_of_tag synth_case #p s #f g x == serialize_bitsum_alt #kt #tot #t #cl b #data tag_of_data type_of_tag synth_case #p s #f g x)
= serialize_bitsum_eq b tag_of_data type_of_tag synth_case s g x

let serialize_bitsum_alt_2
  (#kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type0)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (#p: parser kt t)
  (s: serializer p { kt.parser_kind_subkind == Some ParserStrong } )
  (#f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (g: (x: bitsum'_key_type b) -> Tot (serializer (dsnd (f x))))
  (tg: bitsum'_type b)
  (payload: type_of_tag (bitsum'_key_of_t b tg))
: GTot bytes
= let k = bitsum'_key_of_t b tg in
  serialize s (synth_bitsum'_recip b tg) `Seq.append` serialize (g k) payload

let serialize_bitsum_eq_2
  (#kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type0)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (#p: parser kt t)
  (s: serializer p { kt.parser_kind_subkind == Some ParserStrong } )
  (#f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (g: (x: bitsum'_key_type b) -> Tot (serializer (dsnd (f x))))
  (tg: bitsum'_type b)
  (payload: type_of_tag (bitsum'_key_of_t b tg))
: Lemma
  (serialize_bitsum #kt #tot #t #cl b #data tag_of_data type_of_tag synth_case #p s #f g (synth_case.f tg payload) == serialize_bitsum_alt_2 #kt #tot #t #cl b #data tag_of_data type_of_tag synth_case #p s #f g tg payload)
= serialize_bitsum_eq b tag_of_data type_of_tag synth_case s g (synth_case.f tg payload);
  synth_case_g_f_eq synth_case tg payload

(* Implementation of filter_bitsum' *)

inline_for_extraction
noextract
let filter_bitsum'_t
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
: Tot Type0
= (x: t) ->
  Tot (y: bool { y == filter_bitsum' b x })

inline_for_extraction
let filter_bitsum'_bitstop
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
: Tot (filter_bitsum'_t #tot #t #cl #0 (BitStop ()))
= fun _ -> true

inline_for_extraction
let filter_bitsum'_bitfield
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (sz: nat { sz > 0 /\ sz <= bitsum'_size /\ bitsum'_size <= tot })
  (rest: bitsum' cl (bitsum'_size - sz))
  (phi: filter_bitsum'_t rest)
: Tot (filter_bitsum'_t (BitField sz rest))
= fun x -> phi x

inline_for_extraction
let filter_bitsum'_bitsum_gen
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (is_valid_repr: ((x: bitfield cl key_size) -> Tot (y: bool { y == list_mem x (list_map snd e) })))
  (key_of: ((x: enum_repr e) -> Tot (y: enum_key e { y == enum_key_of_repr e x })))
  (destr_payload: ((k: enum_key e) -> filter_bitsum'_t (payload k)))
: Tot (filter_bitsum'_t (BitSum' key key_size e payload))
= fun x ->
    let r : bitfield cl key_size = cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size in
    if not (is_valid_repr r)
    then
      false
    else
      destr_payload (key_of r) x

inline_for_extraction
noextract
let filter_bitsum'_bitsum'_t
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (l2: list (key & bitfield cl key_size) { e == l1 `L.append` l2 } )
: Tot Type0
= (x: t { ~ (list_mem (cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size <: bitfield cl key_size) (list_map snd l1)) }) ->
  (xr: t { xr == cl.bitfield_eq_lhs x (bitsum'_size - key_size) bitsum'_size }) ->
  Tot (y: bool { y == filter_bitsum' (BitSum' key key_size e payload) x })

inline_for_extraction
let filter_bitsum'_bitsum'_intro
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (phi: filter_bitsum'_bitsum'_t cl bitsum'_size key key_size e payload [] e)
: Tot (filter_bitsum'_t (BitSum' key key_size e payload))
= fun x ->
    let xr = cl.bitfield_eq_lhs x (bitsum'_size - key_size) bitsum'_size in
    phi x xr

inline_for_extraction
let filter_bitsum'_bitsum'_nil
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (h: squash (e == e `L.append` []))
: Tot (filter_bitsum'_bitsum'_t  cl bitsum'_size key key_size e payload e [])
= (fun x xr -> false)

inline_for_extraction
let filter_bitsum'_bitsum'_cons
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (k: key)
  (r: bitfield cl key_size)
  (l2: list (key & bitfield cl key_size) { 
    e == l1 `L.append` ((k, r) :: l2) /\
    list_mem k (list_map fst e) /\
    enum_repr_of_key e k == r /\
    e == (l1 `L.append` [(k, r)]) `L.append` l2
  })
  (destr_payload: filter_bitsum'_t (payload k))
  (destr_tail: filter_bitsum'_bitsum'_t cl bitsum'_size key key_size e payload (l1 `L.append` [(k, r)]) l2)
: Tot (filter_bitsum'_bitsum'_t cl bitsum'_size key key_size e payload l1 ((k, r) :: l2))
= fun x xr ->
    [@inline_let] let _ =
      enum_repr_of_key_append_cons e l1 (k, r) l2
    in
    [@inline_let] let yr = cl.bitfield_eq_rhs x (bitsum'_size - key_size) bitsum'_size r in
    [@inline_let] let cond = (xr <: t) = yr in
    [@inline_let] let _ = 
      assert (cond == true <==> (cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size <: bitfield cl key_size) == r)
    in
    if cond
    then
      destr_payload x
    else
      [@inline_let] let _ =
        L.append_assoc l1 [(k, r)] l2;
        L.map_append snd l1 [(k, r)];
        L.append_mem (L.map snd l1) (L.map snd [(k, r)]) (cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size <: bitfield cl key_size)
      in
      destr_tail (x <: t) xr

module WF = FStar.WellFounded (* for axiom1_dep *)
    
[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let wf_apply // because WF.apply is not marked inline_for_extraction
  (#a:Type) (#b:a -> Type) (f: (x:a -> Tot (b x))) (x:a)
  : Pure (b x) (requires True) (ensures (fun r -> r == f x /\ f x << f))
=
  [@inline_let] let _ = WF.axiom1_dep #a #b f x in
  f x

[@filter_bitsum'_t_attr]
noextract
let rec mk_filter_bitsum'_t'
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
: Tot (filter_bitsum'_t b)
  (decreases (LexCons b (LexCons () LexTop)))
= match b with
  | BitStop _ -> filter_bitsum'_bitstop cl
  | BitField sz rest -> filter_bitsum'_bitfield cl bitsum'_size sz rest (mk_filter_bitsum'_t' rest)
  | BitSum' key key_size e payload ->
    filter_bitsum'_bitsum'_intro cl bitsum'_size key key_size e payload (mk_filter_bitsum'_bitsum'_t' cl bitsum'_size key key_size e payload [] e)
and mk_filter_bitsum'_bitsum'_t'
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (l2: list (key & bitfield cl key_size) { e == l1 `L.append` l2 } )
: Tot (filter_bitsum'_bitsum'_t cl bitsum'_size key key_size e payload l1 l2)
  (decreases (LexCons payload (LexCons l2 LexTop)))
= match l2 with
  | [] ->
    [@inline_let] let _ =
      L.append_l_nil l1
    in
    filter_bitsum'_bitsum'_nil cl bitsum'_size key key_size e payload ()
  | (k, r) :: q ->
    [@inline_let] let _ =
      enum_repr_of_key_append_cons e l1 (k, r) q;
      L.append_assoc l1 [(k, r)] q
    in  
    filter_bitsum'_bitsum'_cons cl bitsum'_size key key_size e payload l1 k r q (mk_filter_bitsum'_t' (wf_apply #(enum_key e) #(fun _ -> bitsum' cl (bitsum'_size - key_size)) payload k)) (mk_filter_bitsum'_bitsum'_t' cl bitsum'_size key key_size e payload (l1 `L.append` [(k, r)]) q)

(* Universal destructor *)

inline_for_extraction
let if_combinator_weak
  (t: Type)
: Tot Type
= (cond: bool) ->
  (sv_true: (cond_true cond -> Tot t)) ->
  (sv_false: (cond_false cond -> Tot t)) ->
  Tot t

inline_for_extraction
noextract
let destr_bitsum'_t
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#from: nat)
  (b: bitsum' cl from)
: Tot (Type u#(a + 1))
= (u: (bitsum'_type b -> Tot (Type u#a))) ->
  (u_if: ((k: Ghost.erased (bitsum'_type b)) -> Tot (if_combinator_weak (u (Ghost.reveal k))))) ->
  (f: ((k: bitsum'_type b) -> Tot (u k))) ->
  (x: parse_filter_refine (filter_bitsum' b)) ->
  Tot (u (synth_bitsum' b x))

inline_for_extraction
let destr_bitsum'_bitstop
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
: Tot (destr_bitsum'_t #tot #t #cl #0 (BitStop ()))
= fun u u_if f x ->
  f ()

inline_for_extraction
let destr_bitsum'_bitfield
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (sz: nat { sz > 0 /\ sz <= bitsum'_size /\ bitsum'_size <= tot })
  (rest: bitsum' cl (bitsum'_size - sz))
  (phi: destr_bitsum'_t rest)
: Tot (destr_bitsum'_t (BitField sz rest))
= fun u u_if f x ->
  phi
    (fun z -> u (cl.get_bitfield x (bitsum'_size - sz) bitsum'_size, z))
    (fun z -> u_if (Ghost.hide (cl.get_bitfield x (bitsum'_size - sz) bitsum'_size, Ghost.reveal z)))
    (fun z -> f (cl.get_bitfield x (bitsum'_size - sz) bitsum'_size, z))
    x

inline_for_extraction
let destr_bitsum'_bitsum_gen
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (key_of: (
    (x: enum_repr e) ->
    Tot (y: enum_key e {
      y == enum_key_of_repr e x
  })))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (destr_payload: ((k: enum_key e) -> Tot (destr_bitsum'_t (payload k))))
: Tot (destr_bitsum'_t (BitSum' key key_size e payload))
= fun u u_if f x ->
    [@inline_let]
    let r : enum_repr e = cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size in
    [@inline_let]
    let k : enum_key e = key_of r in
    destr_payload
      k
      (fun z -> u (bitsum'_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, z |)))
      (fun z -> u_if (Ghost.hide (bitsum'_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, Ghost.reveal z |))))
      (fun z -> f (bitsum'_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, z |)))
      x

module L = FStar.List.Tot

inline_for_extraction
noextract
let destr_bitsum'_bitsum_t
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (l2: list (key & bitfield cl key_size) { e == l1 `L.append` l2 } )
: Tot (Type u#(a + 1))
= (u: (bitsum'_type (BitSum' key key_size e payload) -> Tot (Type u#a))) ->
  (u_if: ((x: Ghost.erased (bitsum'_type (BitSum' key key_size e payload))) -> Tot (if_combinator_weak (u (Ghost.reveal x))))) ->
  (f: ((x: bitsum'_type (BitSum' key key_size e payload)) -> Tot (u x))) ->
  (x: parse_filter_refine (filter_bitsum' (BitSum' key key_size e payload)) { ~ (list_mem (cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size <: bitfield cl key_size) (list_map snd l1)) }) ->
  Tot (u (synth_bitsum' (BitSum' key key_size e payload) x))

inline_for_extraction
let destr_bitsum'_bitsum_intro
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (phi: destr_bitsum'_bitsum_t cl bitsum'_size key key_size e payload [] e)
: Tot (destr_bitsum'_t (BitSum' key key_size e payload))
= fun u u_if f x ->
    phi u u_if f x

inline_for_extraction
let destr_bitsum'_bitsum_nil
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (h: squash (e == e `L.append` []))
: Tot (destr_bitsum'_bitsum_t cl bitsum'_size key key_size e payload e [])
= (fun u u_if f x ->
    assert False;
    false_elim ())

#push-options "--z3rlimit 32"

inline_for_extraction
let destr_bitsum'_bitsum_cons
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (k: key)
  (r: bitfield cl key_size)
  (l2: list (key & bitfield cl key_size) { 
    e == l1 `L.append` ((k, r) :: l2) /\
    list_mem k (list_map fst e) /\
    enum_repr_of_key e k == r /\
    e == (l1 `L.append` [(k, r)]) `L.append` l2
  })
  (destr_payload: destr_bitsum'_t (payload k))
  (destr_tail: destr_bitsum'_bitsum_t cl bitsum'_size key key_size e payload (l1 `L.append` [(k, r)]) l2)
: Tot (destr_bitsum'_bitsum_t cl bitsum'_size key key_size e payload l1 ((k, r) :: l2))
= fun u u_if f x ->
    // [@inline_let]
    let _ =
      enum_repr_of_key_append_cons e l1 (k, r) l2
    in
    [@inline_let] let cond = ((cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size <: bitfield cl key_size) = r) in    
    u_if
      (Ghost.hide (synth_bitsum' (BitSum' key key_size e payload) x))
      cond
      (fun cond_true ->
        destr_payload 
          (fun x -> u (bitsum'_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, x |)))
          (fun x -> u_if (Ghost.hide (bitsum'_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, Ghost.reveal x |))))
          (fun x -> f (bitsum'_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, x |)))
        x
      )
      (fun cond_false ->
        [@inline_let] let _ =
          L.append_assoc l1 [(k, r)] l2;
          L.map_append snd l1 [(k, r)];
          L.append_mem (L.map snd l1) (L.map snd [(k, r)]) (cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size <: bitfield cl key_size)
        in
        destr_tail u u_if f (x <: t)
      )

inline_for_extraction
let destr_bitsum'_bitsum_cons_nil
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (k: key)
  (r: bitfield cl key_size {
    e == l1 `L.append` [(k, r)] /\
    list_mem k (list_map fst e) /\
    enum_repr_of_key e k == r
  })
  (destr_payload: destr_bitsum'_t (payload k))
: Tot (destr_bitsum'_bitsum_t cl bitsum'_size key key_size e payload l1 [(k, r)])
= fun u u_if f x ->
    // [@inline_let]
    let _ =
      enum_repr_of_key_append_cons e l1 (k, r) []
    in
    [@inline_let] let _ : squash ((cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size <: bitfield cl key_size) == r) =
      if (cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size <: bitfield cl key_size) = r
      then ()
      else begin
        L.append_assoc l1 [(k, r)] [];
        L.map_append snd l1 [(k, r)];
        L.append_mem (L.map snd l1) (L.map snd [(k, r)]) (cl.get_bitfield x (bitsum'_size - key_size) bitsum'_size <: bitfield cl key_size)
      end
    in
    destr_payload 
          (fun x -> u (bitsum'_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, x |)))
          (fun x -> u_if (Ghost.hide (bitsum'_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, Ghost.reveal x |))))
          (fun x -> f (bitsum'_type_intro_BitSum' cl bitsum'_size key key_size e payload (| k, x |)))
        x

[@filter_bitsum'_t_attr]
noextract
let rec mk_destr_bitsum'_t
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
: Tot (destr_bitsum'_t b <: Type u#1)
  (decreases (LexCons b (LexCons () LexTop)))
= match b with
  | BitStop _ -> destr_bitsum'_bitstop cl
  | BitField sz rest -> destr_bitsum'_bitfield cl bitsum'_size sz rest (mk_destr_bitsum'_t rest)
  | BitSum' key key_size e payload ->
    destr_bitsum'_bitsum_intro cl bitsum'_size key key_size e payload (mk_destr_bitsum'_bitsum_t cl bitsum'_size key key_size e payload [] e)
and mk_destr_bitsum'_bitsum_t
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (l2: list (key & bitfield cl key_size) { e == l1 `L.append` l2 } )
: Tot (destr_bitsum'_bitsum_t cl bitsum'_size key key_size e payload l1 l2 <: Type u#1)
  (decreases (LexCons payload (LexCons l2 LexTop)))
= match l2 with
  | [] ->
    [@inline_let] let _ =
      L.append_l_nil l1
    in
    destr_bitsum'_bitsum_nil cl bitsum'_size key key_size e payload ()
  | [(k, r)] ->
    [@inline_let] let _ =
      enum_repr_of_key_append_cons e l1 (k, r) [];
      L.append_assoc l1 [(k, r)] []
    in  
    destr_bitsum'_bitsum_cons_nil cl bitsum'_size key key_size e payload l1 k r (mk_destr_bitsum'_t (wf_apply #(enum_key e) #(fun _ -> bitsum' cl (bitsum'_size - key_size)) payload k))
  | (k, r) :: q ->
    [@inline_let] let _ =
      enum_repr_of_key_append_cons e l1 (k, r) q;
      L.append_assoc l1 [(k, r)] q
    in  
    destr_bitsum'_bitsum_cons cl bitsum'_size key key_size e payload l1 k r q (mk_destr_bitsum'_t (wf_apply #(enum_key e) #(fun _ -> bitsum' cl (bitsum'_size - key_size)) payload k)) (mk_destr_bitsum'_bitsum_t cl bitsum'_size key key_size e payload (l1 `L.append` [(k, r)]) q)

(* from a bitsum key to its representation *)

inline_for_extraction
let synth_bitsum'_recip_t
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
: Tot Type0
= (x: bitsum'_type b) ->
  Tot (y: t { y == synth_bitsum'_recip b x })

inline_for_extraction
let synth_bitsum'_recip_BitStop
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
: Tot (synth_bitsum'_recip_t #tot #t #cl #0 (BitStop ()))
= fun _ -> cl.uint_to_t 0

inline_for_extraction
let synth_bitsum'_recip_BitField
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (sz: nat { sz > 0 /\ sz <= bitsum'_size /\ bitsum'_size <= tot })
  (rest: bitsum' cl (bitsum'_size - sz))
  (ih: synth_bitsum'_recip_t rest)
: Tot (synth_bitsum'_recip_t (BitField sz rest))
= fun x ->
  [@inline_let]
  let (hd, tl) = bitsum'_type_elim_BitField cl bitsum'_size sz rest x in
  cl.set_bitfield (ih tl) (bitsum'_size - sz) (bitsum'_size) hd

inline_for_extraction
let synth_bitsum'_recip_BitSum_gen
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (repr_of: (
    (k: enum_key e) ->
    Tot (r: enum_repr e { r == enum_repr_of_key e k })
  ))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (synth_payload: ((k: enum_key e) -> Tot (synth_bitsum'_recip_t (payload k))))
: Tot (synth_bitsum'_recip_t (BitSum' key key_size e payload))
= fun x ->
    [@inline_let]
    let (| k, pl |) = bitsum'_type_elim_BitSum' cl bitsum'_size key key_size e payload x in
    cl.set_bitfield (synth_payload k pl) (bitsum'_size - key_size) bitsum'_size (repr_of k)

inline_for_extraction
noextract
let synth_bitsum'_recip_BitSum_t
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (l2: list (key & bitfield cl key_size) { e == l1 `L.append` l2 } )
: Tot Type0
= (k: enum_key e { ~ (list_mem (k <: key) (list_map fst l1)) }) ->
  (pl: bitsum'_type (payload k)) ->
  Tot (y: t { y == synth_bitsum'_recip (BitSum' key key_size e payload) (| k, pl |) } )

inline_for_extraction
let synth_bitsum'_recip_BitSum_intro
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (phi: synth_bitsum'_recip_BitSum_t cl bitsum'_size key key_size e payload [] e)
: Tot (synth_bitsum'_recip_t (BitSum' key key_size e payload))
= fun x ->
  [@inline_let]
  let (| k, pl |) = x in
  phi k pl

inline_for_extraction
let synth_bitsum'_recip_BitSum_nil
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size) { e == l1 `L.append` [] } )
: Tot (synth_bitsum'_recip_BitSum_t cl bitsum'_size key key_size e payload l1 [])
= fun k _ ->
  [@inline_let] 
  let _ = L.append_l_nil l1 in
  false_elim ()

inline_for_extraction
let synth_bitsum'_recip_BitSum_cons
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (k: key)
  (r: bitfield cl key_size)
  (l2: list (key & bitfield cl key_size) { 
    e == l1 `L.append` ((k, r) :: l2) /\
    list_mem k (list_map fst e) /\
    enum_repr_of_key e k == r /\
    e == (l1 `L.append` [(k, r)]) `L.append` l2
  })
  (destr_payload: synth_bitsum'_recip_t (payload k))
  (destr_tail: synth_bitsum'_recip_BitSum_t cl bitsum'_size key key_size e payload (l1 `L.append` [(k, r)]) l2)
: Tot (synth_bitsum'_recip_BitSum_t cl bitsum'_size key key_size e payload l1 ((k, r) :: l2))
= fun k' rest ->
    [@inline_let]
    let _ =
      enum_repr_of_key_append_cons e l1 (k, r) l2
    in
    if k' = k
    then begin
      [@inline_let]
      let _ =
        assert_norm (synth_bitsum'_recip (BitSum' key key_size e payload) (| k', rest |) == cl.set_bitfield (synth_bitsum'_recip (payload k') rest) (bitsum'_size - key_size) bitsum'_size (enum_repr_of_key e k'))
      in
      (cl.set_bitfield (destr_payload rest) (bitsum'_size - key_size) bitsum'_size r <: t)
    end else
      [@inline_let] let _ =
        L.append_assoc l1 [(k, r)] l2;
        L.map_append fst l1 [(k, r)];
        L.append_mem (L.map fst l1) (L.map fst [(k, r)]) (k' <: key)
      in
      destr_tail (k' <: key) rest

inline_for_extraction
let synth_bitsum'_recip_BitSum_cons_nil
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (k: key)
  (r: bitfield cl key_size {
    e == l1 `L.append` ((k, r) :: []) /\
    list_mem k (list_map fst e) /\
    enum_repr_of_key e k == r /\
    e == (l1 `L.append` [(k, r)]) `L.append` []
  })
  (destr_payload: synth_bitsum'_recip_t (payload k))
: Tot (synth_bitsum'_recip_BitSum_t cl bitsum'_size key key_size e payload l1 ((k, r) :: []))
= fun k' rest ->
    [@inline_let]
    let _ =
      enum_repr_of_key_append_cons e l1 (k, r) []
    in
    [@inline_let]
    let _ : squash (k' = k) =
      if (k' = k)
      then ()
      else begin
        L.append_assoc l1 [(k, r)] [];
        L.map_append fst l1 [(k, r)];
        L.append_mem (L.map fst l1) (L.map fst [(k, r)]) (k' <: key)
      end      
    in
    [@inline_let]
    let _ =
      assert_norm (synth_bitsum'_recip (BitSum' key key_size e payload) (| k', rest |) == cl.set_bitfield (synth_bitsum'_recip (payload k') rest) (bitsum'_size - key_size) bitsum'_size (enum_repr_of_key e k'))
    in
    (cl.set_bitfield (destr_payload rest) (bitsum'_size - key_size) bitsum'_size r <: t)

[@filter_bitsum'_t_attr]
noextract
let rec mk_synth_bitsum'_recip
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (#bitsum'_size: nat)
  (b: bitsum' cl bitsum'_size)
: Tot (synth_bitsum'_recip_t b)
  (decreases (LexCons b (LexCons () LexTop)))
= match b with
  | BitStop _ -> synth_bitsum'_recip_BitStop cl
  | BitField sz rest -> synth_bitsum'_recip_BitField cl bitsum'_size sz rest (mk_synth_bitsum'_recip rest)
  | BitSum' key key_size e payload ->
    synth_bitsum'_recip_BitSum_intro cl bitsum'_size key key_size e payload (mk_synth_bitsum'_recip_BitSum cl bitsum'_size key key_size e payload [] e)
and mk_synth_bitsum'_recip_BitSum
  (#tot: pos)
  (#t: eqtype)
  (cl: uint_t tot t)
  (bitsum'_size: nat)
  (key: eqtype)
  (key_size: nat { key_size > 0 /\ key_size <= bitsum'_size /\ bitsum'_size <= tot })
  (e: enum key (bitfield cl key_size))
  (payload: (enum_key e -> Tot (bitsum' cl (bitsum'_size - key_size))))
  (l1: list (key & bitfield cl key_size))
  (l2: list (key & bitfield cl key_size) { e == l1 `L.append` l2 } )
: Tot (synth_bitsum'_recip_BitSum_t cl bitsum'_size key key_size e payload l1 l2)
  (decreases (LexCons payload (LexCons l2 LexTop)))
= match l2 with
  | [] ->
    [@inline_let] let _ =
      L.append_l_nil l1
    in
    synth_bitsum'_recip_BitSum_nil cl bitsum'_size key key_size e payload l1
  | [(k, r)] ->
    [@inline_let] let _ =
      enum_repr_of_key_append_cons e l1 (k, r) [];
      L.append_assoc l1 [(k, r)] []
    in  
    synth_bitsum'_recip_BitSum_cons_nil cl bitsum'_size key key_size e payload l1 k r (mk_synth_bitsum'_recip (wf_apply #(enum_key e) #(fun _ -> bitsum' cl (bitsum'_size - key_size)) payload k))
  | (k, r) :: q ->
    [@inline_let] let _ =
      enum_repr_of_key_append_cons e l1 (k, r) q;
      L.append_assoc l1 [(k, r)] q
    in  
    synth_bitsum'_recip_BitSum_cons cl bitsum'_size key key_size e payload l1 k r q (mk_synth_bitsum'_recip (wf_apply #(enum_key e) #(fun _ -> bitsum' cl (bitsum'_size - key_size)) payload k)) (mk_synth_bitsum'_recip_BitSum cl bitsum'_size key key_size e payload (l1 `L.append` [(k, r)]) q)
