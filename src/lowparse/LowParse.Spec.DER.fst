module LowParse.Spec.DER
open LowParse.Spec.Combinators
open LowParse.Spec.SeqBytes.Base
// include LowParse.Spec.VLData // for in_bounds

open FStar.Mul

module U8 = FStar.UInt8
module UInt = FStar.UInt
module Math = LowParse.Math
module E = FStar.Endianness
module Seq = FStar.Seq

#reset-options "--z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0"

// let _ : unit = _ by (FStar.Tactics.(print (string_of_int der_length_max); exact (`())))

let der_length_max_eq =
  assert_norm (der_length_max == pow2 (8 * 126) - 1)

let rec log256
  (x: nat { x > 0 })
: Tot (y: nat { y > 0 /\ pow2 (8 * (y - 1)) <= x /\ x < pow2 (8 * y)})
= assert_norm (pow2 8 == 256);
  if x < 256
  then 1
  else begin
    let n = log256 (x / 256) in
    Math.pow2_plus (8 * (n - 1)) 8;
    Math.pow2_plus (8 * n) 8;
    n + 1
  end

let log256_unique
x
y
= Math.pow2_lt_recip (8 * (y - 1)) (8 * log256 x);
  Math.pow2_lt_recip (8 * (log256 x - 1)) (8 * y)

let log256_le
x1
x2
= Math.pow2_lt_recip (8 * (log256 x1 - 1)) (8 * log256 x2)

let der_length_payload_size_le
x1
x2
= if x1 < 128 || x2 < 128
  then ()
  else
    let len_len2 = log256 x2 in
    let len_len1 = log256 x1 in
    log256_le x1 x2;
    assert_norm (pow2 7 == 128);
    assert_norm (der_length_max == pow2 (8 * 126) - 1);
    Math.pow2_lt_recip (8 * (len_len2 - 1)) (8 * 126)

let synth_be_int
  (len: nat)
  (b: Seq.lseq byte len)
: GTot (lint len)
= E.lemma_be_to_n_is_bounded b;
  E.be_to_n b

let synth_be_int_injective
  (len: nat)
: Lemma
  (synth_injective (synth_be_int len))
  [SMTPat (synth_injective (synth_be_int len))]
= 
  synth_injective_intro' (synth_be_int len) (fun (x x' : Seq.lseq byte len) ->
    E.be_to_n_inj x x'
  )

let synth_der_length_129
  (x: U8.t { x == 129uy } )
  (y: U8.t { U8.v y >= 128 } )
: GTot (refine_with_tag tag_of_der_length x)
= assert_norm (der_length_max == pow2 (8 * 126) - 1);
  assert_norm (pow2 7 == 128);
  assert_norm (pow2 8 == 256);
  assert_norm (256 < der_length_max);
  assert (U8.v x <= der_length_max);
  log256_unique (U8.v y) 1;
  U8.v y

let synth_der_length_greater
  (x: U8.t { U8.v x > 129 /\ U8.v x < 255 } )
  (len: nat { len == U8.v x - 128 } )
  (y: lint len { y >= pow2 (8 * (len - 1)) } )
: Tot (refine_with_tag tag_of_der_length x)
= assert_norm (der_length_max == pow2 (8 * 126) - 1);
  assert_norm (pow2 7 == 128);
  assert_norm (pow2 8 == 256);
  assert_norm (256 < der_length_max);
  assert (U8.v x <= der_length_max);
  Math.pow2_le_compat (8 * 126) (8 * len);
  Math.pow2_le_compat (8 * (len - 1)) 7;
  log256_unique y len;
  y

let parse_der_length_payload
  (x: U8.t)
: Tot (parser (parse_der_length_payload_kind x) (refine_with_tag tag_of_der_length x))
= assert_norm (der_length_max == pow2 (8 * 126) - 1);
  assert_norm (pow2 7 == 128);
  assert_norm (pow2 8 == 256);
  assert_norm (256 < der_length_max);
  assert (U8.v x <= der_length_max);
  let (x' : der_length_t) = U8.v x in
  if x' < 128
  then begin
    weaken (parse_der_length_payload_kind x) (parse_ret (x' <: refine_with_tag tag_of_der_length x))
  end else
   if x = 128uy
   then 
    fail_parser (parse_der_length_payload_kind x) (refine_with_tag tag_of_der_length x) // DER representation of 0 is covered by the x<128 case
   else if x = 255uy
   then 
    fail_parser (parse_der_length_payload_kind x) (refine_with_tag tag_of_der_length x) // forbidden in BER already
   else if x = 129uy
   then
    weaken (parse_der_length_payload_kind x)
      ((parse_u8 `parse_filter` (fun y -> U8.v y >= 128))
        `parse_synth` synth_der_length_129 x)
  else begin
    let len : nat = U8.v x - 128 in
    synth_be_int_injective len; // FIXME: WHY WHY WHY does the pattern not trigger, even with higher rlimit?
    weaken (parse_der_length_payload_kind x)
      (((parse_seq_flbytes len `parse_synth` (synth_be_int len))
        `parse_filter` (fun (y: lint len) -> y >= pow2 (8 * (len - 1))))
       `parse_synth` synth_der_length_greater x len)
  end

let parse_der_length_payload_unfold
  (x: U8.t)
  (input: bytes)
: Lemma
  (
    let y = parse (parse_der_length_payload x) input in
    (256 < der_length_max) /\ (
    if U8.v x < 128
    then tag_of_der_length (U8.v x) == x /\ y == Some (U8.v x, 0)
    else if x = 128uy || x = 255uy
    then y == None
    else if x = 129uy
    then
      match parse parse_u8 input with
      | None -> y == None
      | Some (z, consumed) ->
        if U8.v z < 128
        then y == None
        else tag_of_der_length (U8.v z) == x /\ y == Some (U8.v z, consumed)
    else
      let len : nat = U8.v x - 128 in
      synth_injective (synth_be_int len) /\ (
      let res : option (lint len & consumed_length input) = parse (parse_synth (parse_seq_flbytes len) (synth_be_int len)) input in
      match res with
      | None -> y == None
      | Some (z, consumed) ->
        len > 0 /\ (
        if z >= pow2 (8 * (len - 1))
        then z <= der_length_max /\ tag_of_der_length z == x /\ y == Some ((z <: refine_with_tag tag_of_der_length x), consumed)
        else y == None
  ))))
= assert_norm (der_length_max == pow2 (8 * 126) - 1);
  assert_norm (pow2 7 == 128);
  assert_norm (pow2 8 == 256);
  assert_norm (256 < der_length_max);
  assert (U8.v x <= der_length_max);
  let (x' : der_length_t) = U8.v x in
  if x' < 128
  then begin
    ()
  end else
   if x = 128uy
   then 
    ()
   else if x = 255uy
   then 
    ()
   else if x = 129uy
   then begin
     parse_synth_eq (parse_u8 `parse_filter` (fun y -> U8.v y >= 128)) (synth_der_length_129 x) input;
     parse_filter_eq parse_u8 (fun y -> U8.v y >= 128) input;
     match parse parse_u8 input with
     | None -> ()
     | Some (y, _) ->
       if U8.v y >= 128
       then begin
         log256_unique (U8.v y) 1       
       end else ()
  end else begin
    let len : nat = U8.v x - 128 in
    synth_be_int_injective len; // FIXME: WHY WHY WHY does the pattern not trigger, even with higher rlimit?
    parse_synth_eq ((parse_seq_flbytes len `parse_synth` (synth_be_int len))
        `parse_filter` (fun (y: lint len) -> y >= pow2 (8 * (len - 1)))) (synth_der_length_greater x len) input;
    parse_filter_eq (parse_seq_flbytes len `parse_synth` (synth_be_int len)) (fun (y: lint len) -> y >= pow2 (8 * (len - 1))) input;
    assert (len > 1);
    let res : option (lint len & consumed_length input) = parse (parse_seq_flbytes len `parse_synth` (synth_be_int len)) input in
    match res with
    | None -> ()
    | Some (y, _) ->
      if y >= pow2 (8 * (len - 1))
      then begin
        let (y: lint len { y >= pow2 (8 * (len - 1)) } ) = y in
        Math.pow2_le_compat (8 * 126) (8 * len);
        Math.pow2_le_compat (8 * (len - 1)) 7;
        log256_unique y len
      end else ()
  end

inline_for_extraction
let parse_der_length_payload_kind_weak : parser_kind =
  strong_parser_kind 0 126 None

inline_for_extraction
let parse_der_length_weak_kind : parser_kind = and_then_kind parse_u8_kind parse_der_length_payload_kind_weak

let parse_der_length_weak : parser parse_der_length_weak_kind der_length_t
= parse_tagged_union
    parse_u8
    tag_of_der_length
    (fun x -> weaken parse_der_length_payload_kind_weak (parse_der_length_payload x))

noextract
let parse_bounded_der_length_payload_kind
  (min: der_length_t)
  (max: der_length_t { min <= max } )
: Tot parser_kind =
  [@inline_let] let _ = der_length_payload_size_le min max in
  strong_parser_kind (der_length_payload_size min) (der_length_payload_size max) None

let bounded_int
  (min: der_length_t)
  (max: der_length_t { min <= max })
: Tot Type0
= (x: int { min <= x /\ x <= max })

let parse_bounded_der_length_tag_cond
  (min: der_length_t)
  (max: der_length_t { min <= max })
  (x: U8.t)
: GTot bool
= let len = der_length_payload_size_of_tag x in der_length_payload_size min <= len && len <= der_length_payload_size max

inline_for_extraction // for parser_kind
let tag_of_bounded_der_length
  (min: der_length_t)
  (max: der_length_t { min <= max })
  (x: bounded_int min max)
: Tot (y: U8.t { parse_bounded_der_length_tag_cond min max y == true } )
= [@inline_let]
  let _ = der_length_payload_size_le min x; der_length_payload_size_le x max in
  tag_of_der_length x

let parse_bounded_der_length_payload
  (min: der_length_t)
  (max: der_length_t { min <= max })
  (x: U8.t { parse_bounded_der_length_tag_cond min max x == true } )
: Tot (parser (parse_bounded_der_length_payload_kind min max) (refine_with_tag (tag_of_bounded_der_length min max) x))
= weaken (parse_bounded_der_length_payload_kind min max)
    (parse_der_length_payload x
      `parse_filter` (fun (y: refine_with_tag tag_of_der_length x) -> min <= y && y <= max)
      `parse_synth` (fun (y: refine_with_tag tag_of_der_length x { min <= y && y <= max }) -> (y <: refine_with_tag (tag_of_bounded_der_length min max) x)))

noextract
let parse_bounded_der_length_kind
  (min: der_length_t)
  (max: der_length_t { min <= max } )
: Tot parser_kind
= and_then_kind
    (parse_filter_kind parse_u8_kind)
    (parse_bounded_der_length_payload_kind min max)

let parse_bounded_der_length
  (min: der_length_t)
  (max: der_length_t { min <= max })
: Tot (parser (parse_bounded_der_length_kind min max) (bounded_int min max))
= parse_tagged_union
    (parse_u8 `parse_filter` parse_bounded_der_length_tag_cond min max)
    (tag_of_bounded_der_length min max)
    (parse_bounded_der_length_payload min max)

(* equality *)

let parse_bounded_der_length_payload_unfold
  (min: der_length_t)
  (max: der_length_t { min <= max })
  (x: U8.t { parse_bounded_der_length_tag_cond min max x == true } )
  (input' : bytes)
: Lemma
  (parse (parse_bounded_der_length_payload min max x) input' == (
      match parse (parse_der_length_payload x) input' with
      | None -> None
      | Some (y, consumed_y) ->
        if min <= y && y <= max
        then Some (y, consumed_y)
        else None
  ))
= 
      parse_synth_eq
        (parse_der_length_payload x
                                  `parse_filter` (fun (y: refine_with_tag tag_of_der_length x) -> min <= y && y <= max))
                                    (fun (y: refine_with_tag tag_of_der_length x { min <= y && y <= max }) -> (y <: refine_with_tag (tag_of_bounded_der_length min max) x))
        input' ;
        parse_filter_eq
          (parse_der_length_payload x)
          (fun (y: refine_with_tag tag_of_der_length x) -> min <= y && y <= max)
          input'

let parse_bounded_der_length_unfold_aux
  (min: der_length_t)
  (max: der_length_t { min <= max })
  (input: bytes)
: Lemma
  (parse (parse_bounded_der_length min max) input == (match parse parse_u8 input with
  | None -> None
  | Some (x, consumed_x) ->
    let len = der_length_payload_size_of_tag x in
    if der_length_payload_size min <= len && len <= der_length_payload_size max then
      let input' = Seq.slice input consumed_x (Seq.length input) in
      match parse (parse_bounded_der_length_payload min max x) input'
      with
      | Some (y, consumed_y) -> Some (y, consumed_x + consumed_y)
      | None -> None
    else None
 ))
= parse_tagged_union_eq
    (parse_u8 `parse_filter` parse_bounded_der_length_tag_cond min max)
    (tag_of_bounded_der_length min max)
    (parse_bounded_der_length_payload min max)
    input;
  parse_filter_eq parse_u8 (parse_bounded_der_length_tag_cond min max) input

let parse_bounded_der_length_unfold
  (min: der_length_t)
  (max: der_length_t { min <= max })
  (input: bytes)
: Lemma
  (parse (parse_bounded_der_length min max) input == (match parse parse_u8 input with
  | None -> None
  | Some (x, consumed_x) ->
    let len = der_length_payload_size_of_tag x in
    if der_length_payload_size min <= len && len <= der_length_payload_size max then
      let input' = Seq.slice input consumed_x (Seq.length input) in
      match parse (parse_der_length_payload x) input' with
      | None -> None
      | Some (y, consumed_y) ->
        if min <= y && y <= max
        then Some (y, consumed_x + consumed_y)
        else None
    else None
 ))
= parse_bounded_der_length_unfold_aux min max input;
  match parse parse_u8 input with
  | None -> ()
  | Some (x, consumed_x) ->
    let len = der_length_payload_size_of_tag x in
    if der_length_payload_size min <= len && len <= der_length_payload_size max then
      let input' = Seq.slice input consumed_x (Seq.length input) in
      parse_bounded_der_length_payload_unfold min max (x <:   (x: U8.t { parse_bounded_der_length_tag_cond min max x == true } )
) input'
    else ()

let parse_bounded_der_length_weak
  (min: der_length_t)
  (max: der_length_t { min <= max })
: Tot (parser (parse_filter_kind parse_der_length_weak_kind) (bounded_int min max))
= parse_der_length_weak
    `parse_filter` (fun y -> min <= y && y <= max)
    `parse_synth` (fun (y: der_length_t {min <= y && y <= max}) -> (y <: bounded_int min max))

let parse_bounded_der_length_weak_unfold
  (min: der_length_t)
  (max: der_length_t { min <= max })
  (input: bytes)
: Lemma
  (parse (parse_bounded_der_length_weak min max) input == (
    match parse parse_u8 input with
    | None -> None
    | Some (x, consumed_x) ->
      let input' = Seq.slice input consumed_x (Seq.length input) in
      begin match parse (parse_der_length_payload x) input' with
      | None -> None
      | Some (y, consumed_y) ->
        if min <= y && y <= max
        then Some (y, consumed_x + consumed_y)
        else None
      end
  ))
= parse_synth_eq
    (parse_der_length_weak
      `parse_filter` (fun y -> min <= y && y <= max))
    (fun (y: der_length_t {min <= y && y <= max}) -> (y <: bounded_int min max))
    input;
  parse_filter_eq parse_der_length_weak (fun y -> min <= y && y <= max) input;
  parse_tagged_union_eq
    parse_u8
    tag_of_der_length
    (fun x -> weaken parse_der_length_payload_kind_weak (parse_der_length_payload x))
    input

let parse_bounded_der_length_eq
  (min: der_length_t)
  (max: der_length_t { min <= max })
  (input: bytes)
: Lemma
  (ensures (parse (parse_bounded_der_length min max) input == parse (parse_bounded_der_length_weak min max) input))
= parse_bounded_der_length_unfold min max input;
  parse_bounded_der_length_weak_unfold min max input;
  match parse parse_u8 input with
    | None -> ()
    | Some (x, consumed_x) ->
      let input' = Seq.slice input consumed_x (Seq.length input) in
      begin match parse (parse_der_length_payload x) input' with
      | None -> ()
      | Some (y, consumed_y) ->
        if min <= y && y <= max
        then (der_length_payload_size_le min y; der_length_payload_size_le y max)
        else ()
      end

(* serializer *)

let tag_of_der_length_lt_128
  (x: der_length_t)
: Lemma
  (requires (U8.v (tag_of_der_length x) < 128))
  (ensures (x == U8.v (tag_of_der_length x)))
= if x < 128
  then ()
  else
    let len_len = log256 x in
    assert_norm (der_length_max == pow2 (8 * 126) - 1);
    Math.pow2_lt_recip (8 * (len_len - 1)) (8 * 126)

let tag_of_der_length_invalid
  (x: der_length_t)
: Lemma
  (requires (let y = U8.v (tag_of_der_length x) in y == 128 \/ y == 255))
  (ensures False)
= if x < 128
  then ()
  else
    let len_len = log256 x in
    assert_norm (der_length_max == pow2 (8 * 126) - 1);
    Math.pow2_lt_recip (8 * (len_len - 1)) (8 * 126)

let tag_of_der_length_eq_129
  (x: der_length_t)
: Lemma
  (requires (U8.v (tag_of_der_length x) == 129))
  (ensures (x >= 128 /\ x < 256))
= if x < 128
  then ()
  else
    let len_len = log256 x in
    assert_norm (der_length_max == pow2 (8 * 126) - 1);
    Math.pow2_lt_recip (8 * (len_len - 1)) (8 * 126)

let synth_der_length_129_recip
  (x: U8.t { x == 129uy })
  (y: refine_with_tag tag_of_der_length x)
: GTot (y: U8.t {U8.v y >= 128})
= tag_of_der_length_eq_129 y;
  U8.uint_to_t y

let synth_be_int_recip
  (len: nat)
  (x: lint len)
: GTot (Seq.lseq byte len)
= E.n_to_be len x

let synth_be_int_inverse
  (len: nat)
: Lemma
  (synth_inverse (synth_be_int len) (synth_be_int_recip len))
= ()

let synth_der_length_greater_recip
  (x: U8.t { U8.v x > 129 /\ U8.v x < 255 } )
  (len: nat { len == U8.v x % 128 } )
  (y: refine_with_tag tag_of_der_length x)
: Tot (y: lint len { y >= pow2 (8 * (len - 1)) } )
= assert_norm (der_length_max == pow2 (8 * 126) - 1);
  Math.pow2_lt_recip (8 * (log256 y - 1)) (8 * 126);
  y

let synth_der_length_greater_inverse
  (x: U8.t { U8.v x > 129 /\ U8.v x < 255 } )
  (len: nat { len == U8.v x % 128 } )
: Lemma
  (synth_inverse (synth_der_length_greater x len) (synth_der_length_greater_recip x len))
= ()

private
let serialize_der_length_payload_greater 
  (x: U8.t { not (U8.v x < 128 || x = 128uy || x = 255uy || x = 129uy) } )
  (len: nat { len == U8.v x - 128 } )
=
      (serialize_synth
        #_
        #(parse_filter_refine #(lint len) (fun (y: lint len) -> y >= pow2 (8 * (len - 1))))
        #(refine_with_tag tag_of_der_length x)
        _
        (synth_der_length_greater x len)
        (serialize_filter
          (serialize_synth
            #_
            #(Seq.lseq byte len)
            #(lint len)
            _
            (synth_be_int len)
            (serialize_seq_flbytes len)
            (synth_be_int_recip len)
            ()
          )
          (fun (y: lint len) -> y >= pow2 (8 * (len - 1)))
        )
        (synth_der_length_greater_recip x len)
        ()
      )

let serialize_der_length_payload
  (x: U8.t)
: Tot (serializer (parse_der_length_payload x))
= assert_norm (der_length_max == pow2 (8 * 126) - 1);
  assert_norm (pow2 7 == 128);
  assert_norm (pow2 8 == 256);
  assert_norm (256 < der_length_max);
  assert (U8.v x <= der_length_max);
  let (x' : der_length_t) = U8.v x in
  if x' < 128
  then begin
    serialize_weaken (parse_der_length_payload_kind x) (serialize_ret (x' <: refine_with_tag tag_of_der_length x) (fun (y: refine_with_tag tag_of_der_length x) -> tag_of_der_length_lt_128 y))
  end else
   if x = 128uy || x = 255uy
   then
     fail_serializer (parse_der_length_payload_kind x) (refine_with_tag tag_of_der_length x) (fun y -> tag_of_der_length_invalid y)
   else if x = 129uy
   then begin
     serialize_weaken
       (parse_der_length_payload_kind x)
       (serialize_synth
          (parse_filter parse_u8 (fun y -> U8.v y >= 128))
          (synth_der_length_129 x)
          (serialize_filter serialize_u8 (fun y -> U8.v y >= 128))
          (synth_der_length_129_recip x)
          (synth_inverse_intro' (synth_der_length_129 x) (synth_der_length_129_recip x) (fun (y: refine_with_tag tag_of_der_length x) -> tag_of_der_length_eq_129 y))
       )
   end else begin
    let len : nat = U8.v x - 128 in
    synth_be_int_injective len; // FIXME: WHY WHY WHY does the pattern not trigger, even with higher rlimit?
    serialize_weaken
      (parse_der_length_payload_kind x)
      (serialize_der_length_payload_greater x len)
   end

let serialize_der_length_weak : serializer parse_der_length_weak =
  serialize_tagged_union
    serialize_u8
    tag_of_der_length
    (fun x -> serialize_weaken parse_der_length_payload_kind_weak (serialize_der_length_payload x))

#push-options "--max_ifuel 6 --z3rlimit 64"

let serialize_der_length_weak_unfold
  (y: der_length_t)
: Lemma
  (let res = serialize serialize_der_length_weak y in
    let x = tag_of_der_length y in
    let s1 = Seq.create 1 x in
    if x `U8.lt` 128uy
    then res `Seq.equal` s1
    else if x = 129uy
    then y <= 255 /\ res `Seq.equal` (s1 `Seq.append` Seq.create 1 (U8.uint_to_t y))
    else
      let len = log256 y in
      res `Seq.equal` (s1 `Seq.append` E.n_to_be len y)
  )
= let x = tag_of_der_length y in
  serialize_u8_spec x;
  assert_norm (der_length_max == pow2 (8 * 126) - 1);
  assert_norm (pow2 7 == 128);
  assert_norm (pow2 8 == 256);
  assert_norm (256 < der_length_max);
  assert (U8.v x <= der_length_max);
  let (x' : der_length_t) = U8.v x in
  if x' < 128
  then begin
    ()
  end else
   if x = 128uy || x = 255uy
   then
    tag_of_der_length_invalid y
   else if x = 129uy
   then begin
       tag_of_der_length_eq_129 y;
       assert (U8.v (synth_der_length_129_recip x y) == y);
       let s1 = serialize (       serialize_synth #_ #(parse_filter_refine #U8.t (fun y -> U8.v y >= 128))  #(refine_with_tag tag_of_der_length x)
          (parse_filter parse_u8 (fun y -> U8.v y >= 128))
          (synth_der_length_129 x)
          (serialize_filter serialize_u8 (fun y -> U8.v y >= 128))
          (synth_der_length_129_recip x)
          (synth_inverse_intro' (synth_der_length_129 x) (synth_der_length_129_recip x) (fun (y: refine_with_tag tag_of_der_length x) -> tag_of_der_length_eq_129 y))) 
          y
       in
       serialize_synth_eq'
 #_ #(parse_filter_refine #U8.t (fun y -> U8.v y >= 128))
 #(refine_with_tag tag_of_der_length x)
 (parse_filter parse_u8 (fun y -> U8.v y >= 128))
          (synth_der_length_129 x)
          (serialize_filter serialize_u8 (fun y -> U8.v y >= 128))
          (synth_der_length_129_recip x)
          (synth_inverse_intro' (synth_der_length_129 x) (synth_der_length_129_recip x) (fun (y: refine_with_tag tag_of_der_length x) -> tag_of_der_length_eq_129 y))
          y
          s1
          ()
          (serialize serialize_u8 (synth_der_length_129_recip x y))
          ()
          ;
       serialize_u8_spec (U8.uint_to_t y);
       ()
   end else begin
    let len : nat = U8.v x - 128 in
    synth_be_int_injective len; // FIXME: WHY WHY WHY does the pattern not trigger, even with higher rlimit?
    assert (
      serialize (serialize_der_length_payload x) y == serialize (serialize_der_length_payload_greater x len) y
    );
      serialize_synth_eq'
        #_
        #(parse_filter_refine #(lint len) (fun (y: lint len) -> y >= pow2 (8 * (len - 1))))
        #(refine_with_tag tag_of_der_length x)
        _
        (synth_der_length_greater x len)
        (serialize_filter
          (serialize_synth
            #_
            #(Seq.lseq byte len)
            #(lint len)
            _
            (synth_be_int len)
            (serialize_seq_flbytes len)
            (synth_be_int_recip len)
            ()
          )
          (fun (y: lint len) -> y >= pow2 (8 * (len - 1)))
        )
        (synth_der_length_greater_recip x len)
        ()
        y
        (serialize (serialize_der_length_payload_greater x len) y)
        (_ by (FStar.Tactics.trefl ()))
        (serialize
          (serialize_synth
            #_
            #(Seq.lseq byte len)
            #(lint len)
            _
            (synth_be_int len)
            (serialize_seq_flbytes len)
            (synth_be_int_recip len)
            ()
          )
          (synth_der_length_greater_recip x len y)
        )
        ()
        ;
     serialize_synth_eq
            _
            (synth_be_int len)
            (serialize_seq_flbytes len)
            (synth_be_int_recip len)
            ()
            (synth_der_length_greater_recip x len y);
     Math.pow2_lt_recip (8 * (log256 y - 1)) (8 * 126);
     ()
   end;
  ()

#pop-options

let serialize_bounded_der_length_weak
  (min: der_length_t)
  (max: der_length_t { min <= max })
: Tot (serializer (parse_bounded_der_length_weak min max))
= serialize_synth
    _
    (fun (y: der_length_t {min <= y && y <= max}) -> (y <: bounded_int min max))
    (serialize_filter
      serialize_der_length_weak
      (fun y -> min <= y && y <= max)
    )
    (fun (y : bounded_int min max) -> (y <: (y: der_length_t {min <= y && y <= max})))
    ()

let serialize_bounded_der_length
  (min: der_length_t)
  (max: der_length_t { min <= max })
: Tot (serializer (parse_bounded_der_length min max))
= Classical.forall_intro (parse_bounded_der_length_eq min max);
  serialize_ext
    _
    (serialize_bounded_der_length_weak min max)
    (parse_bounded_der_length min max)

let serialize_bounded_der_length_unfold
  (min: der_length_t)
  (max: der_length_t { min <= max })
  (y: bounded_int min max)
: Lemma
  (let res = serialize (serialize_bounded_der_length min max) y in
    let x = tag_of_der_length y in
    let s1 = Seq.create 1 x in
    if x `U8.lt` 128uy
    then res `Seq.equal` s1
    else if x = 129uy
    then y <= 255 /\ res `Seq.equal` (s1 `Seq.append` Seq.create 1 (U8.uint_to_t y))
    else
      let len = log256 y in
      res `Seq.equal` (s1 `Seq.append` E.n_to_be len y)
  )
= serialize_synth_eq
    _
    (fun (y: der_length_t {min <= y && y <= max}) -> (y <: bounded_int min max))
    (serialize_filter
      serialize_der_length_weak
      (fun y -> min <= y && y <= max)
    )
    (fun (y : bounded_int min max) -> (y <: (y: der_length_t {min <= y && y <= max})))
    ()
    y;
  serialize_der_length_weak_unfold y

(* 32-bit spec *)


module U32 = FStar.UInt32

let der_length_payload_size_of_tag_inv32
  (x: der_length_t)
: Lemma
  (requires (x < 4294967296))
  (ensures (
    tag_of_der_length x == (
      if x < 128
      then U8.uint_to_t x
      else if x < 256
      then 129uy
      else if x < 65536
      then 130uy
      else if x < 16777216
      then 131uy
      else 132uy
  )))
= if x < 128
  then ()
  else
    let len_len = log256 x in
    assert_norm (der_length_max == pow2 (8 * 126) - 1);
    Math.pow2_lt_recip (8 * (len_len - 1)) (8 * 126);
    assert_norm (pow2 (8 * 1) == 256);
    assert_norm (pow2 (8 * 2) == 65536);
    assert_norm (pow2 (8 * 3) == 16777216);
    assert_norm (pow2 (8 * 4) == 4294967296);
    if x < 256
    then
      log256_unique x 1
    else if x < 65536
    then
      log256_unique x 2
    else if x < 16777216
    then
      log256_unique x 3
    else
      log256_unique x 4

let synth_der_length_payload32
  (x: U8.t { der_length_payload_size_of_tag x <= 4 } )
  (y: refine_with_tag tag_of_der_length x)
: GTot (refine_with_tag tag_of_der_length32 x)
= let _ =
    assert_norm (der_length_max == pow2 (8 * 126) - 1);
    let _ = assert_norm (pow2 (8 * 2) == 65536) in
    let _ = assert_norm (pow2 (8 * 3) == 16777216) in
    let _ = assert_norm (pow2 (8 * 4) == 4294967296) in    
    if y >= 128 then begin
      Math.pow2_lt_recip (8 * (log256 y - 1)) (8 * 126);
      assert (U8.v (tag_of_der_length y) == 128 + log256 y)
    end
  in
  U32.uint_to_t y

let synth_der_length_payload32_injective
  (x: U8.t { der_length_payload_size_of_tag x <= 4 } )
: Lemma
  (synth_injective (synth_der_length_payload32 x))
  [SMTPat (synth_injective (synth_der_length_payload32 x))]
= assert_norm (der_length_max == pow2 (8 * 126) - 1);
  let _ = assert_norm (pow2 (8 * 2) == 65536) in
  let _ = assert_norm (pow2 (8 * 3) == 16777216) in
  let _ = assert_norm (pow2 (8 * 4) == 4294967296) in
  synth_injective_intro' (synth_der_length_payload32 x) (fun (y1 y2: refine_with_tag tag_of_der_length x) ->
    if y1 >= 128 then begin
      Math.pow2_lt_recip (8 * (log256 y1 - 1)) (8 * 126);
      assert (U8.v (tag_of_der_length y1) == 128 + log256 y1)
    end;
    if y2 >= 128 then begin
      Math.pow2_lt_recip (8 * (log256 y2 - 1)) (8 * 126);
      assert (U8.v (tag_of_der_length y2) == 128 + log256 y2)
    end
  )

let parse_der_length_payload32
x
: Tot (parser (parse_der_length_payload_kind x) (refine_with_tag tag_of_der_length32 x))
= parse_der_length_payload x `parse_synth` synth_der_length_payload32 x

let be_int_of_bounded_integer
  (len: integer_size)
  (x: nat { x < pow2 (8 * len) } )
: GTot (bounded_integer len)
= integer_size_values len;
  assert_norm (pow2 (8 * 1) == 256);
  assert_norm (pow2 (8 * 2) == 65536);
  assert_norm (pow2 (8 * 3) == 16777216);
  assert_norm (pow2 (8 * 4) == 4294967296);
  U32.uint_to_t x

let be_int_of_bounded_integer_injective
  (len: integer_size)
: Lemma
  (synth_injective (be_int_of_bounded_integer len))
  [SMTPat (synth_injective (be_int_of_bounded_integer len))] // FIXME: WHY WHY WHY does this pattern NEVER trigger?
= integer_size_values len;
  assert_norm (pow2 (8 * 1) == 256);
  assert_norm (pow2 (8 * 2) == 65536);
  assert_norm (pow2 (8 * 3) == 16777216);
  assert_norm (pow2 (8 * 4) == 4294967296)

#push-options "--max_ifuel 4 --z3rlimit 16"

let parse_seq_flbytes_synth_be_int_eq
  (len: integer_size)
  (input: bytes)
: Lemma
  (
    let _ = synth_be_int_injective len in
    let _ = be_int_of_bounded_integer_injective len in
    parse (
      parse_synth #_ #(lint len) #(bounded_integer len)
        (parse_synth #_ #(Seq.lseq byte len) #(lint len)
          (parse_seq_flbytes len)
          (synth_be_int len)
        )
      (be_int_of_bounded_integer len)
    ) input == parse (parse_bounded_integer len) input)
=
    let _ = synth_be_int_injective len in
    let _ = be_int_of_bounded_integer_injective len in
    parse_synth_eq (parse_seq_flbytes len `parse_synth` synth_be_int len) (be_int_of_bounded_integer len) input;
    parse_synth_eq (parse_seq_flbytes len) (synth_be_int len) input;
    parser_kind_prop_equiv (parse_bounded_integer_kind len) (parse_bounded_integer len);
    parse_bounded_integer_spec len input

let parse_der_length_payload32_unfold
x
input
= parse_synth_eq (parse_der_length_payload x) (synth_der_length_payload32 x) input;
    assert_norm (der_length_max == pow2 (8 * 126) - 1);
    assert_norm (pow2 (8 * 1) == 256);
    let _ = assert_norm (pow2 (8 * 2) == 65536) in
    let _ = assert_norm (pow2 (8 * 3) == 16777216) in
    let _ = assert_norm (pow2 (8 * 4) == 4294967296) in    
  begin match parse (parse_der_length_payload x) input with
  | None -> ()
  | Some (y, _) ->
    if y >= 128 then begin
      Math.pow2_lt_recip (8 * (log256 y - 1)) (8 * 126);
      assert (U8.v (tag_of_der_length y) == 128 + log256 y)
    end
  end;
  parse_der_length_payload_unfold x input;
    if U8.v x < 128
    then () // tag_of_der_length (U8.v x) == x /\ y == Some (Cast.uint8_to_uint32 x, 0)
    else if x = 128uy || x = 255uy
    then () // y == None
    else if x = 129uy
    then ()
    else begin
      let len : nat = U8.v x - 128 in
      assert (2 <= len /\ len <= 4);
      let _ = synth_be_int_injective len in
      let _ = be_int_of_bounded_integer_injective len in
      parse_seq_flbytes_synth_be_int_eq len input;
      integer_size_values len;
      parse_synth_eq
        #_
        #(lint len)
        #(bounded_integer len)
        (parse_synth #_ #(Seq.lseq byte len) #(lint len) (parse_seq_flbytes len) (synth_be_int len))
        (be_int_of_bounded_integer len)
        input
    end

#pop-options

let log256_eq
x
= log256_unique x (log256' x)

let synth_bounded_der_length32
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 })
  (x: bounded_int min max)
: GTot (bounded_int32 min max)
= U32.uint_to_t x

let parse_bounded_der_length32
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 })
: Tot (parser (parse_bounded_der_length32_kind min max) (bounded_int32 min max))
= parse_bounded_der_length min max `parse_synth` synth_bounded_der_length32 min max

#push-options "--z3rlimit 50"
let parse_bounded_der_length32_unfold
min
max
input
= parse_synth_eq (parse_bounded_der_length min max) (synth_bounded_der_length32 min max) input;
  parse_bounded_der_length_unfold min max input;
  match parse parse_u8 input with
   | None -> ()
   | Some (x, consumed_x) ->
     let len = der_length_payload_size_of_tag x in
     if der_length_payload_size min <= len && len <= der_length_payload_size max then
      let input' = Seq.slice input consumed_x (Seq.length input) in
      assert_norm (4294967296 <= der_length_max);
      der_length_payload_size_le max 4294967295;
      assert_norm (pow2 (8 * 3) == 16777216);
      assert_norm (pow2 (8 * 4) == 4294967296);
      log256_unique 4294967295 4;
      parse_synth_eq (parse_der_length_payload x) (synth_der_length_payload32 x) input' ;
      match parse (parse_der_length_payload x) input' with
      | None -> ()
      | Some (y, _) ->
        if y >= 128 then begin
          assert_norm (der_length_max == pow2 (8 * 126) - 1);
          Math.pow2_lt_recip (8 * (log256 y - 1)) (8 * 126);
          assert (U8.v (tag_of_der_length y) == 128 + log256 y)
        end
     else ()
#pop-options

let synth_bounded_der_length32_recip
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 })
  (x: bounded_int32 min max)
: GTot (bounded_int min max)
= U32.v x

let serialize_bounded_der_length32
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 })
: Tot (serializer (parse_bounded_der_length32 min max))
= serialize_synth
    _
    (synth_bounded_der_length32 min max)
    (serialize_bounded_der_length min max)
    (synth_bounded_der_length32_recip min max)
    ()

let serialize_bounded_der_length32_unfold
min max y'
= serialize_synth_eq
    _
    (synth_bounded_der_length32 min max)
    (serialize_bounded_der_length min max)
    (synth_bounded_der_length32_recip min max)
    ()
    y';
  serialize_bounded_der_length_unfold min max (U32.v y');
    let x = tag_of_der_length32_impl y' in
    if x `U8.lt` 128uy
    then ()
    else if x = 129uy
    then FStar.Math.Lemmas.small_modulo_lemma_1 (U32.v y') 256
    else begin
      assert (x <> 128uy /\ x <> 255uy);
      let len = log256' (U32.v y') in
      log256_eq (U32.v y');
      serialize_bounded_integer_spec len y'
    end

#push-options "--z3rlimit 20"
let serialize_bounded_der_length32_size
min max y'
= serialize_bounded_der_length32_unfold min max y'
#pop-options
