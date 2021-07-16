module LowParse.SLow.Base
include LowParse.Size.Base

module B32 = LowParse.Bytes32
module U32 = FStar.UInt32

let bytes32 = B32.bytes

let parser32_correct
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input: bytes32)
  (res: option (t * U32.t))
: GTot Type0
= let gp = parse p (B32.reveal input) in
  match res with
  | None -> gp == None
  | Some (hres, consumed) ->
    Some? gp /\ (
      let (Some (hres' , consumed')) = gp in
      hres == hres' /\
      U32.v consumed == (consumed' <: nat)
    )

[@unifier_hint_injective]
inline_for_extraction
let parser32
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= (input: bytes32) -> Tot (res: option (t * U32.t) { parser32_correct p input res } )

let parser32_consumes
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
  (input: bytes32)
: Lemma
  (Some? (p32 input) ==> (let (Some (_, consumed)) = p32 input in U32.v consumed <= B32.length input))
= ()

let parser32_consumes'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
  (input: bytes32)
: Lemma
  (match p32 input with
  | Some (_, consumed) -> U32.v consumed <= B32.length input
  | _ -> True)
= ()

inline_for_extraction
let make_parser32
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (p32: (input: bytes32) -> Pure (option (t * U32.t)) (requires True) (ensures (fun res -> parser32_correct p input res)))
: Tot (parser32 p)
= (fun (input: bytes32) -> (p32 input <: (res: option (t * U32.t) { parser32_correct p input res } )))

inline_for_extraction
let coerce_parser32
  (t2: Type)
  (#k: parser_kind)
  (#t1: Type)
  (#p: parser k t1)
  (p32: parser32 p)
  (u: unit { t2 == t1 } )
: Tot (parser32 (coerce_parser t2 p))
= p32

let validator_correct
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input: bytes32)
  (res: option U32.t)
: GTot Type0
= let gp = parse p (B32.reveal input) in
  match res with
  | None -> gp == None
  | Some (consumed) ->
    Some? gp /\ (
      let (Some (_ , consumed')) = gp in
      U32.v consumed == (consumed' <: nat)
    )

let validator
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= (input: bytes32) -> Tot (res: option U32.t { validator_correct p input res } )

let serializer32_correct
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (input: t)
  (res: bytes32)
: GTot Type0
= B32.reveal res == s input

let serializer32_correct'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (input: t)
  (res: bytes32)
: GTot Type0
= B32.reveal res `bytes_equal` s input

[@unifier_hint_injective]
inline_for_extraction
let serializer32
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (input: t) -> Tot (res: bytes32 { serializer32_correct s input res } )

let serializer32_correct_length
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (input: t)
  (res: bytes32)
: Lemma
  (requires (serializer32_correct s input res))
  (ensures (
    let len = FStar.Bytes.length res in
    k.parser_kind_low <= len /\ (
    match k.parser_kind_high with
    | Some max -> len <= max
    | _ -> True
  )))
  [SMTPat (serializer32_correct s input res); SMTPat (FStar.Bytes.length res)]
= serialize_length s input

inline_for_extraction
let serialize32_ext
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (s1': serializer32 s1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (u: squash (t1 == t2 /\ (forall (input: bytes) . parse p1 input == parse p2 input)))
: Tot (serializer32 (serialize_ext p1 s1 p2))
= fun input -> s1' input

inline_for_extraction
let partial_serializer32
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (input: t { Seq.length (s input) < 4294967296 } ) -> Tot (res: bytes32 { serializer32_correct s input res } )

let serializer32_then_parser32
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (p32: parser32 p)
  (s32: serializer32 s)
  (input: t)
: Lemma
  (p32 (s32 input) == Some (input, B32.len (s32 input)))
= ()

let parser32_then_serializer32
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (p32: parser32 p)
  (s32: serializer32 s)
  (input: bytes32)
: Lemma
  (requires (Some? (p32 input)))
  (ensures (
    let (Some (v, consumed)) = p32 input in
    U32.v consumed <= B32.length input /\
    s32 v == B32.b32slice input 0ul consumed
  ))
= serializer_correct_implies_complete p s

let parser32_then_serializer32'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (p32: parser32 p)
  (s32: serializer32 s)
  (input: bytes32)
  (v: t)
  (consumed: U32.t)
: Lemma
  (requires (p32 input == Some (v, consumed)))
  (ensures (
    B32.length (s32 v) == U32.v consumed /\
    U32.v consumed <= B32.length input /\
    B32.reveal (s32 v) == Seq.slice (B32.reveal input) 0 (U32.v consumed)
  ))
= parser32_then_serializer32 s p32 s32 input

let parser32_injective
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
  (input1 input2: bytes32)
: Lemma
  (requires (
    let p1 = p32 input1 in
    let p2 = p32 input2 in
    Some? p1 /\
    Some? p2 /\ (
    let (Some (v1, _)) = p1 in
    let (Some (v2, _)) = p2 in
    v1 == v2
  )))
  (ensures (
    let p1 = p32 input1 in
    let p2 = p32 input2 in
    Some? p1 /\
    Some? p2 /\ (
    let (Some (v1, consumed1)) = p1 in
    let (Some (v2, consumed2)) = p2 in
    v1 == v2 /\
    consumed1 == consumed2 /\
    U32.v consumed1 <= B32.length input1 /\
    U32.v consumed2 <= B32.length input2 /\
    B32.b32slice input1 0ul consumed1 == B32.b32slice input2 0ul consumed2
  )))
= parser_kind_prop_equiv k p;
  assert (injective_precond p (B32.reveal input1) (B32.reveal input2));
  assert (injective_postcond p (B32.reveal input1) (B32.reveal input2))

let serializer32_injective
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (s32: serializer32 s)
  (input1 input2: t)
: Lemma
  (requires (s32 input1 == s32 input2))
  (ensures (input1 == input2))
= assert (parse p (serialize s input1) == parse p (serialize s input2))

let parse32_size
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
  (input: bytes32)
  (data: t)
  (consumed: U32.t)
: Lemma
  (requires (p32 input == Some (data, consumed)))
  (ensures (
    k.parser_kind_low <= U32.v consumed /\ (
    Some? k.parser_kind_high ==> (
    let (Some hi) = k.parser_kind_high in
    U32.v consumed <= hi
  ))))
= parser_kind_prop_equiv k p

let parse32_total
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
  (input: bytes32)
: Lemma
  (requires (
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal /\
    k.parser_kind_low <= B32.length input
  ))
  (ensures (
    Some? (p32 input)
  ))
= parser_kind_prop_equiv k p

(* Total parsers for sequences *)

[@"opaque_to_smt"]
irreducible
let rec bytes_of_seq'
  (x: Seq.seq byte)
  (accu: bytes32  { B32.length accu + Seq.length x < 4294967296 })
: Tot (y: bytes32 { B32.reveal y `Seq.equal` (B32.reveal accu `Seq.append` x) })
  (decreases (Seq.length x))
= if Seq.length x = 0
  then accu
  else bytes_of_seq' (Seq.tail x) (B32.append accu (B32.create 1ul (Seq.head x)))

[@"opaque_to_smt"]
inline_for_extraction
let bytes_of_seq
  (x: Seq.seq byte { Seq.length x < 4294967296 })
: Tot (y: bytes32 { B32.reveal y `Seq.equal` x })
= bytes_of_seq' x B32.empty_bytes

inline_for_extraction
let parse_tot_seq_of_parser32
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p {
    k.parser_kind_subkind == Some ParserStrong /\
    begin match k.parser_kind_high with
    | None -> False
    | Some max -> max < 4294967296
    end
  })
  (x: Seq.seq byte)
: Tot (y: _ { y == parse p x })
= match k.parser_kind_high with
  | Some max ->
    if Seq.length x < max
    then 
      match p32 (bytes_of_seq x) with
      | None -> None
      | Some (x, consumed) -> Some (x, U32.v consumed)
    else begin
      [@inline_let]
      let max32 = U32.uint_to_t max in
      let res = p32 (bytes_of_seq (Seq.slice x 0 max)) in
      Classical.move_requires (parse_strong_prefix p x) (Seq.slice x 0 max);
      Classical.move_requires (parse_strong_prefix p (Seq.slice x 0 max)) x;
      parser_kind_prop_equiv k p;
      match res with
      | None -> None
      | Some (x, consumed) -> Some (x, U32.v consumed)
    end

[@"opaque_to_smt"]
irreducible
let rec seq_of_bytes'
  (x: bytes32)
  (accu: Seq.seq byte)
: Tot (y: Seq.seq byte { y `Seq.equal` (accu `Seq.append` B32.reveal x) })
  (decreases (B32.length x))
= if B32.len x = 0ul
  then accu
  else (seq_of_bytes' (B32.slice x 1ul (B32.len x)) (Seq.append accu (Seq.create 1 (B32.index x 0))) <: Seq.seq byte)

[@"opaque_to_smt"]
inline_for_extraction
let seq_of_bytes
  (x: bytes32)
: Tot (y: Seq.seq byte { y `Seq.equal` B32.reveal x })
= seq_of_bytes' x Seq.empty

inline_for_extraction
let serialize_tot_seq_of_serializer32
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (x: t)
: Tot (y: _ { y == serialize s x })
= seq_of_bytes (s32 x)
