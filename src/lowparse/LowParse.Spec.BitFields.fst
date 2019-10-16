module LowParse.Spec.BitFields
include LowParse.Spec.Combinators
include LowParse.Spec.Int

module BF = LowParse.BitFields

let rec valid_bitfield_bounds (lo: nat) (hi: nat { lo <= hi }) (l: list nat) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | mi :: q -> lo <= mi && mi <= hi && valid_bitfield_bounds mi hi q

let rec valid_bitfield_widths (lo: nat) (hi: nat { lo <= hi }) (l: list nat) : Tot bool (decreases l) =
  match l with
  | [] -> lo = hi
  | sz :: q -> lo + sz <= hi && valid_bitfield_widths (lo + sz) hi q

let rec bounds_of_widths (lo: nat) (hi: nat { lo <= hi }) (l: list nat) : Pure (list nat)
  (requires (valid_bitfield_widths lo hi l))
  (ensures (fun res -> valid_bitfield_bounds lo hi res))
  (decreases l)
= match l with
  | [] -> []
  | [_] -> []
  | sz :: q -> (lo + sz) :: bounds_of_widths (lo + sz) hi q

let rec bitfields (tot: pos) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) : Tot Type0 (decreases l) =
  match l with
  | [] -> unit
  | [sz] -> BF.bitfield tot sz
  | sz :: q -> BF.bitfield tot sz & bitfields tot (lo + sz) hi q

module U = FStar.UInt

let rec synth_bitfield (tot: pos) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x: U.uint_t tot) : Tot (bitfields tot lo hi l) (decreases l) =
  match l with
  | [] -> ()
  | [_] -> BF.get_bitfield x lo hi
  | sz :: q -> (BF.get_bitfield x lo (lo + sz), synth_bitfield tot (lo + sz) hi q x)

let rec synth_bitfield_injective (tot: pos) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x y: U.uint_t tot) : Lemma
  (requires (synth_bitfield tot lo hi l x == synth_bitfield tot lo hi l y))
  (ensures (BF.get_bitfield x lo hi == BF.get_bitfield y lo hi))
  (decreases l)
= match l with
  | [] ->
    BF.get_bitfield_empty x lo;
    BF.get_bitfield_empty y lo
  | [_] -> ()
  | sz :: q ->
    synth_bitfield_injective tot (lo + sz) hi q x y;
    BF.get_bitfield_partition_2_gen lo (lo + sz) hi x y

#push-options "--z3rlimit 64"

let rec synth_bitfield_ext (tot: pos) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x y: U.uint_t tot) : Lemma
  (requires (BF.get_bitfield x lo hi == BF.get_bitfield y lo hi))
  (ensures (synth_bitfield tot lo hi l x == synth_bitfield tot lo hi l y))
  (decreases l)
= match l with
  | [] -> ()
  | [_] -> ()    
  | sz :: q ->
    BF.get_bitfield_get_bitfield x lo hi 0 sz;
    BF.get_bitfield_get_bitfield x lo hi sz (hi - lo);
    BF.get_bitfield_get_bitfield y lo hi 0 sz;
    BF.get_bitfield_get_bitfield y lo hi sz (hi - lo);
    synth_bitfield_ext tot (lo + sz) hi q x y

#pop-options

module U32 = FStar.UInt32

let synth_bitfield32 (l: list nat { valid_bitfield_widths 0 32 l }) (x: U32.t) : Tot (bitfields 32 0 32 l) =
  synth_bitfield 32 0 32 l (U32.v x)

let synth_bitfield32_injective (l: list nat { valid_bitfield_widths 0 32 l }) : Lemma
  (synth_injective (synth_bitfield32 l))
  [SMTPat (synth_injective (synth_bitfield32 l))]
= synth_injective_intro' (synth_bitfield32 l) (fun x y ->
    synth_bitfield_injective 32 0 32 l (U32.v x) (U32.v y);
    BF.get_bitfield_full (U32.v x);
    BF.get_bitfield_full (U32.v y)
  )

let parse_bitfield32 (l: list nat { valid_bitfield_widths 0 32 l }) : Tot (parser parse_u32_kind (bitfields 32 0 32 l)) =
  parse_u32 `parse_synth` synth_bitfield32 l

let rec synth_bitfield_recip (tot: pos) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x: bitfields tot lo hi l) : Tot (U.uint_t tot) (decreases l) =
  match l with
  | [] -> 0
  | [_] -> BF.set_bitfield 0 lo hi x
  | sz :: q ->
    let (hd, tl) = x <: (BF.bitfield tot sz & bitfields tot (lo + sz) hi q) in
    BF.set_bitfield (synth_bitfield_recip tot (lo + sz) hi q tl) lo (lo + sz) hd

#push-options "--z3rlimit 16"

let rec synth_bitfield_recip_inverse
  (tot: pos) (lo: nat) (hi: nat { lo <= hi /\ hi <= tot }) (l: list nat { valid_bitfield_widths lo hi l }) (x: bitfields tot lo hi l)
: Lemma
  (ensures (synth_bitfield tot lo hi l (synth_bitfield_recip tot lo hi l x) == x))
  (decreases l)
= match l with
  | [] -> ()
  | [sz] ->
    let x = x <: BF.bitfield tot sz in
    BF.get_bitfield_set_bitfield_same 0 lo hi x
  | sz :: q ->
    let (hd, tl) = x <: (BF.bitfield tot sz & bitfields tot (lo + sz) hi q) in
    let y = synth_bitfield_recip tot (lo + sz) hi q tl in
    BF.get_bitfield_set_bitfield_same y lo (lo + sz) hd;
    BF.get_bitfield_set_bitfield_other y lo (lo + sz) hd (lo + sz) hi;
    synth_bitfield_ext tot (lo + sz) hi q y (BF.set_bitfield y lo (lo + sz) hd);
    synth_bitfield_recip_inverse tot (lo + sz) hi q tl

#pop-options

let synth_bitfield32_recip
  (l: list nat { valid_bitfield_widths 0 32 l })
  (x: bitfields 32 0 32 l)
: Tot U32.t
= U32.uint_to_t (synth_bitfield_recip 32 0 32 l x)

let synth_bitfield32_inverse
  (l: list nat { valid_bitfield_widths 0 32 l })
: Lemma
  (synth_inverse (synth_bitfield32 l) (synth_bitfield32_recip l))
  [SMTPat (synth_inverse (synth_bitfield32 l) (synth_bitfield32_recip l))]
= synth_inverse_intro' (synth_bitfield32 l) (synth_bitfield32_recip l) (fun x ->
    synth_bitfield_recip_inverse 32 0 32 l x
  )

let serialize_bitfield32
  (l: list nat { valid_bitfield_widths 0 32 l })
: Tot (serializer (parse_bitfield32 l))
= serialize_synth
    _
    (synth_bitfield32 l)
    serialize_u32
    (synth_bitfield32_recip l)
    ()